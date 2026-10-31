// Cloud save sync (Mac and iOS): keeps the committed save directory ($DM_SAVE) in step with an S3-compatible bucket (Cloudflare R2, Backblaze B2, MinIO, AWS S3, ...).
// Off unless DM_CLOUD_S3_ENDPOINT is set. Settings are environment variables (iOS: Documents/env.txt, or baked in with the NSP script's --env-file; Mac: the shell, or DM_CLOUD_CONFIG=<file of KEY=VALUE lines>):
//   DM_CLOUD_S3_ENDPOINT  https://<host>[:port]   (https only: an iOS app does not talk plain http; http://localhost[:port] is accepted for tests)
//   DM_CLOUD_S3_BUCKET    bucket name             (path-style addressing: <endpoint>/<bucket>/<key>)
//   DM_CLOUD_S3_KEY / DM_CLOUD_S3_SECRET   access key id / secret
//   DM_CLOUD_S3_REGION    signing region (default "auto", what R2 expects; AWS and B2 need their real region)
//   DM_CLOUD_S3_PREFIX    key prefix (default "nxnative"); the objects are <prefix>/<title ID>/save.bin and save.meta
// Start (dm_cloud_start, first thing in host_preload, so before the game mounts the save): read the remote meta; remote newer and local untouched since the last sync -> replace the local save with the remote one;
// local changed and remote not -> push later; both changed -> the save with the newer file wins; the first sync of a device (no cloud_state.txt) with different content on both sides -> the cloud save wins
// (a device that has just started a fresh game must not beat real progress). The side that loses is kept, never dropped:
// the local save is renamed to <save>.before-sync-<time> (the newest 3 stay), a remote save about to be overwritten is first copied (S3 copy) to <prefix>/<title ID>/history/. Offline or failing: the local save is used as it is.
// Running: the save is never replaced (the game has it mounted). A thread watches the number of save commits (dm_fs_commit_count); 8 s after the last commit the save is uploaded.
// The upload reads a clone of the committed directory taken under hle_fs.c's commit locks (dm_fs_clone_committed), so it is always one committed version; an empty save is never uploaded,
// and a remote save that has to be kept in history/ is not overwritten until the copy succeeded. A pull swaps the downloaded directory in with one renamex_np(RENAME_SWAP).
// Writes are conditional (If-Match / If-None-Match on the ETags just read), so two devices uploading at the same moment cannot overwrite each other unseen: the loser reads again and keeps the
// winner's save in history/ first. save.meta records the ETag of the save.bin it belongs to, so a save.bin whose save.meta is not written yet is recognised as another device's. A server that answers
// conditional headers with 501 gets unconditional writes. Failed pushes are retried after 30 s, doubling up to 5 min.
// dm_cloud_flush uploads at once (going to the background, closing the window, graceful exit); dm_cloud_sync_now uploads and checks the cloud for another device's newer save (the Mac's Cloud Save menu);
// dm_cloud_status says in one line where the sync stands (the Mac window's subtitle).
// The save is one object: a deterministic archive of the files (sorted paths, no times), so its SHA-256 says whether two saves are equal; save.meta (written after save.bin) carries that hash and the newest file time.
#import <Foundation/Foundation.h>
#import <CommonCrypto/CommonDigest.h>
#import <CommonCrypto/CommonHMAC.h>
#include <dirent.h>
#include <sys/stat.h>
#include <unistd.h>
#include <pthread.h>
#include <stdatomic.h>
#include <sys/xattr.h>
#include "hle.h"

uint64_t dm_fs_commit_count(void);
int dm_fs_clone_committed(const char *dir, const char *to);   // hle_fs.c

#define SAVE_MAX (256ull << 20)   // a save bigger than this is not synced (it is kept in memory while packed)

static NSString *g_ep, *g_bucket, *g_region, *g_ak, *g_sk, *g_prefix, *g_dir, *g_state_path;
static NSURLSession *g_sess;
static pthread_mutex_t g_mu = PTHREAD_MUTEX_INITIALIZER;   // one pull / push at a time
static NSString *g_synced_sha;       // hash of the save as last pushed or pulled
static NSString *g_remote_sha;       // hash of the remote object as last seen (to tell our own earlier push from somebody else's)
static _Atomic int g_on, g_need_push;
static int g_pack_failed;            // the last pack failed (logged once until it works again)
static int g_no_cond;                // the server refused conditional writes (501): they are sent without If-Match / If-None-Match
// status (dm_cloud_status): read by the front end without the lock
static _Atomic int g_busy, g_offline, g_failed, g_remote_newer;
static _Atomic long g_synced_at;            // time() of the last push, pull or check that found the cloud in step
static _Atomic uint64_t g_pushed_commits;   // dm_fs_commit_count that the cloud save contains
#define RETRY_MIN 30000000000ull            // retry after a failed push: 30 s, doubling up to 5 min
#define RETRY_MAX 300000000000ull
static _Atomic uint64_t g_retry_at, g_retry_ns = RETRY_MIN;

// ---------- small helpers ----------
static NSString *hex(const unsigned char *d, size_t n) { NSMutableString *s = [NSMutableString stringWithCapacity:n * 2]; for (size_t i = 0; i < n; i++) [s appendFormat:@"%02x", d[i]]; return s; }
static NSString *sha256_hex(NSData *d) { unsigned char h[CC_SHA256_DIGEST_LENGTH]; CC_SHA256(d.bytes, (CC_LONG)d.length, h); return hex(h, sizeof h); }
static NSData *hmac(NSData *key, NSString *msg) { unsigned char h[CC_SHA256_DIGEST_LENGTH]; NSData *m = [msg dataUsingEncoding:NSUTF8StringEncoding]; CCHmac(kCCHmacAlgSHA256, key.bytes, key.length, m.bytes, m.length, h); return [NSData dataWithBytes:h length:sizeof h]; }
// RFC 3986 encoding of one object key (the '/' between segments stays)
static NSString *uri_encode(NSString *s) {
    NSMutableString *o = [NSMutableString string]; const char *u = s.UTF8String;
    for (; *u; u++) { unsigned char c = (unsigned char)*u; if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_' || c == '.' || c == '~' || c == '/') [o appendFormat:@"%c", c]; else [o appendFormat:@"%%%02X", c]; }
    return o;
}
static NSString *utc(const char *fmt, time_t t) { char b[40]; struct tm tm; gmtime_r(&t, &tm); strftime(b, sizeof b, fmt, &tm); return @(b); }

// ---------- S3 (Signature V4) ----------
// Returns the response body (nil on a network error); *status is the HTTP status (0 on a network error); *etag (when not NULL) the response's ETag. extra: more headers (lower case), signed with the rest
static NSData *s3(NSString *method, NSString *key, NSData *body, NSDictionary<NSString *, NSString *> *extra, int *status, NSTimeInterval timeout, NSString **etag) {
    *status = 0; if (etag) *etag = nil;
    NSString *path = [NSString stringWithFormat:@"/%@/%@", g_bucket, uri_encode(key)];
    NSURL *url = [NSURL URLWithString:[g_ep stringByAppendingString:path]];
    if (!url || !url.host) return nil;
    NSString *host = url.port ? [NSString stringWithFormat:@"%@:%@", url.host, url.port] : url.host;
    time_t now = time(NULL); NSString *amz = utc("%Y%m%dT%H%M%SZ", now), *day = utc("%Y%m%d", now);
    NSString *ph = sha256_hex(body ?: [NSData data]);
    NSMutableDictionary *h = [NSMutableDictionary dictionaryWithDictionary:@{@"host": host, @"x-amz-content-sha256": ph, @"x-amz-date": amz}];
    [h addEntriesFromDictionary:extra];
    NSArray *names = [h.allKeys sortedArrayUsingSelector:@selector(compare:)];
    NSMutableString *ch = [NSMutableString string]; for (NSString *n in names) [ch appendFormat:@"%@:%@\n", n, h[n]];
    NSString *signed_ = [names componentsJoinedByString:@";"];
    NSString *canon = [NSString stringWithFormat:@"%@\n%@\n\n%@\n%@\n%@", method, path, ch, signed_, ph];
    NSString *scope = [NSString stringWithFormat:@"%@/%@/s3/aws4_request", day, g_region];
    NSString *sts = [NSString stringWithFormat:@"AWS4-HMAC-SHA256\n%@\n%@\n%@", amz, scope, sha256_hex([canon dataUsingEncoding:NSUTF8StringEncoding])];
    NSData *k = hmac([[@"AWS4" stringByAppendingString:g_sk] dataUsingEncoding:NSUTF8StringEncoding], day);
    k = hmac(k, g_region); k = hmac(k, @"s3"); k = hmac(k, @"aws4_request");
    NSData *sig = hmac(k, sts);
    NSMutableURLRequest *rq = [NSMutableURLRequest requestWithURL:url cachePolicy:NSURLRequestReloadIgnoringLocalCacheData timeoutInterval:timeout];
    rq.HTTPMethod = method;
    for (NSString *n in names) if (![n isEqualToString:@"host"]) [rq setValue:h[n] forHTTPHeaderField:n];
    [rq setValue:[NSString stringWithFormat:@"AWS4-HMAC-SHA256 Credential=%@/%@, SignedHeaders=%@, Signature=%@", g_ak, scope, signed_, hex(sig.bytes, sig.length)] forHTTPHeaderField:@"Authorization"];
    dispatch_semaphore_t sem = dispatch_semaphore_create(0); __block NSData *out = nil; __block int st = 0; __block NSString *tag = nil;
    void (^done)(NSData *, NSURLResponse *, NSError *) = ^(NSData *d, NSURLResponse *r, NSError *e) {
        if (!e && [r isKindOfClass:NSHTTPURLResponse.class]) { st = (int)((NSHTTPURLResponse *)r).statusCode; out = d ?: [NSData data]; tag = [(NSHTTPURLResponse *)r valueForHTTPHeaderField:@"ETag"]; }
        dispatch_semaphore_signal(sem);
    };
    NSURLSessionTask *t = body.length ? [g_sess uploadTaskWithRequest:rq fromData:body completionHandler:done] : [g_sess dataTaskWithRequest:rq completionHandler:done];
    [t resume];
    if (dispatch_semaphore_wait(sem, dispatch_time(DISPATCH_TIME_NOW, (int64_t)((timeout + 5) * NSEC_PER_SEC)))) { [t cancel]; return nil; }
    *status = st; if (etag) *etag = tag; return out;
}
// conditions for overwriting an object last seen with ETag `etag` (nil: it did not exist)
static NSDictionary *cond(NSString *etag) { return g_no_cond ? @{} : etag ? @{@"if-match": etag} : @{@"if-none-match": @"*"}; }
static NSString *obj(NSString *name) { return [NSString stringWithFormat:@"%@/%s/%@", g_prefix, DM_GAME_ID, name]; }

// ---------- the save as one archive ----------
// "NXSAVE1\n", then per entry: type 'D' or 'F', u32 path length, path, (F: u64 size, bytes). Paths sorted by bytes, so equal saves give equal archives.
// A file or directory hle_fs.c renamed on a case collision (.dm-case-N) keeps its guest name in an xattr: an 'N' entry (u32 length, name) right after it carries that name.
#define FS_GUEST_NAME "org.d2rmobile.guest-name"   // hle_fs.c
static void put_guest_name(NSMutableData *o, NSString *rel, const char *full) {
    if (![rel.lastPathComponent hasPrefix:@".dm-case-"]) return;
    char g[0x301]; ssize_t k = getxattr(full, FS_GUEST_NAME, g, sizeof g, 0, XATTR_NOFOLLOW); if (k <= 0) return;
    char t = 'N'; uint32_t gl = (uint32_t)k; [o appendBytes:&t length:1]; [o appendBytes:&gl length:4]; [o appendBytes:g length:gl];
}
static NSData *pack_dir(NSString *dir, uint64_t *newest) {
    *newest = 0;
    NSFileManager *fm = NSFileManager.defaultManager;
    NSArray *subs = [[fm subpathsOfDirectoryAtPath:dir error:nil] sortedArrayUsingComparator:^NSComparisonResult(NSString *a, NSString *b) { int c = strcmp(a.UTF8String, b.UTF8String); return c < 0 ? NSOrderedAscending : c > 0 ? NSOrderedDescending : NSOrderedSame; }];
    NSMutableData *o = [NSMutableData dataWithBytes:"NXSAVE1\n" length:8];
    for (NSString *rel in subs) {
        NSString *full = [dir stringByAppendingPathComponent:rel]; struct stat st;
        if (lstat(full.UTF8String, &st)) continue;
        const char *p = rel.UTF8String; uint32_t pl = (uint32_t)strlen(p);
        if (S_ISDIR(st.st_mode)) { char t = 'D'; [o appendBytes:&t length:1]; [o appendBytes:&pl length:4]; [o appendBytes:p length:pl]; put_guest_name(o, rel, full.fileSystemRepresentation); }
        else if (S_ISREG(st.st_mode)) {
            if ((uint64_t)st.st_size + o.length > SAVE_MAX) return nil;
            NSData *d = [NSData dataWithContentsOfFile:full options:NSDataReadingUncached error:nil]; if (!d && st.st_size) return nil;
            char t = 'F'; uint64_t sz = d.length;
            [o appendBytes:&t length:1]; [o appendBytes:&pl length:4]; [o appendBytes:p length:pl]; [o appendBytes:&sz length:8]; if (d) [o appendData:d];
            put_guest_name(o, rel, full.fileSystemRepresentation);
            if ((uint64_t)st.st_mtime > *newest) *newest = (uint64_t)st.st_mtime;
        }
    }
    return o;
}
static BOOL unpack_to(NSData *a, NSString *dest) {
    const unsigned char *b = a.bytes; size_t n = a.length, i = 8; NSFileManager *fm = NSFileManager.defaultManager;
    if (n < 8 || memcmp(b, "NXSAVE1\n", 8)) return NO;
    [fm removeItemAtPath:dest error:nil];
    if (![fm createDirectoryAtPath:dest withIntermediateDirectories:YES attributes:nil error:nil]) return NO;
    NSString *last = nil;   // the entry an 'N' entry names
    while (i < n) {
        char t = (char)b[i++]; uint32_t pl; if (i + 4 > n) return NO; memcpy(&pl, b + i, 4); i += 4;
        if (i + pl > n) return NO;
        if (t == 'N') {
            if (!last || !pl || pl > 0x300) return NO;
            if (setxattr(last.fileSystemRepresentation, FS_GUEST_NAME, b + i, pl, 0, XATTR_NOFOLLOW)) return NO;
            i += pl; continue;
        }
        NSString *rel = [[NSString alloc] initWithBytes:b + i length:pl encoding:NSUTF8StringEncoding]; i += pl;
        if (!rel.length || [rel hasPrefix:@"/"] || [rel isEqualToString:@".."] || [rel hasPrefix:@"../"] || [rel hasSuffix:@"/.."] || [rel containsString:@"/../"]) return NO;   // never write outside the save
        NSString *full = last = [dest stringByAppendingPathComponent:rel];
        if (t == 'D') { if (![fm createDirectoryAtPath:full withIntermediateDirectories:YES attributes:nil error:nil]) return NO; }
        else if (t == 'F') {
            uint64_t sz; if (i + 8 > n) return NO; memcpy(&sz, b + i, 8); i += 8; if (sz > n - i) return NO;
            [fm createDirectoryAtPath:full.stringByDeletingLastPathComponent withIntermediateDirectories:YES attributes:nil error:nil];
            if (![[NSData dataWithBytes:b + i length:sz] writeToFile:full options:0 error:nil]) return NO;
            i += sz;
        } else return NO;
    }
    return YES;
}

// The committed save as one archive. The game may commit while it is read: hle_fs.c swaps the whole directory, so the files are read from a clone taken under its commit lock;
// where cloning fails (not APFS) they are read in place, again if a commit happened meanwhile. nil: missing, unreadable, too big or not one version
static NSData *pack_save(uint64_t *newest) {
    NSString *snap = [g_dir stringByAppendingString:@".cloud.snap"]; NSFileManager *fm = NSFileManager.defaultManager;
    [fm removeItemAtPath:snap error:nil];
    BOOL exists = [fm fileExistsAtPath:g_dir];
    if (exists && !dm_fs_clone_committed(g_dir.fileSystemRepresentation, snap.fileSystemRepresentation)) { NSData *a = pack_dir(snap, newest); [fm removeItemAtPath:snap error:nil]; return a; }
    for (int tries = 0; tries < 3; tries++) {
        uint64_t c0 = dm_fs_commit_count(); NSData *a = pack_dir(g_dir, newest);
        if (dm_fs_commit_count() == c0) return a;
    }
    return nil;
}

// ---------- meta and state ----------
typedef struct { BOOL ok; NSString *sha; uint64_t mtime; NSString *etag, *bin_etag; } meta_t;   // ok = the object exists and parses; etag: of save.meta; bin_etag: of the save.bin it belongs to (nil in older metas)
static NSString *meta_text(NSString *sha, uint64_t newest, size_t size, NSString *bin_etag) {
    char host[256] = ""; gethostname(host, sizeof host);
    return [NSString stringWithFormat:@"sha=%@\nmtime=%llu\nsize=%zu\ndevice=%s\ntime=%@\nbin_etag=%@\n", sha, (unsigned long long)newest, size, host, utc("%Y-%m-%dT%H:%M:%SZ", time(NULL)), bin_etag ?: @""];
}
static void reachable(void) { if (atomic_exchange(&g_offline, 0)) LOG("cloud save: the server is reachable again"); }
// *net is set when the request itself failed (offline / server error), so the caller can tell "nothing there" from "cannot tell"
static meta_t get_meta(BOOL *net) {
    meta_t m = {NO, nil, 0, nil, nil}; int st; *net = NO; NSString *tag;
    NSData *d = s3(@"GET", obj(@"save.meta"), nil, nil, &st, 15, &tag);
    if (st == 404) { reachable(); return m; }
    if (st != 200) {
        *net = YES;
        if (st) LOG("[RED] cloud save: the server answered HTTP %d%s", st, st == 403 || st == 401 ? " (check DM_CLOUD_S3_KEY / _SECRET / _REGION / _BUCKET)" : "");
        return m;
    }
    for (NSString *ln in [[[NSString alloc] initWithData:d encoding:NSUTF8StringEncoding] componentsSeparatedByString:@"\n"]) {
        if ([ln hasPrefix:@"sha="]) m.sha = [ln substringFromIndex:4]; else if ([ln hasPrefix:@"mtime="]) m.mtime = (uint64_t)strtoull([ln substringFromIndex:6].UTF8String, NULL, 10);
        else if ([ln hasPrefix:@"bin_etag="] && ln.length > 9) m.bin_etag = [ln substringFromIndex:9];
    }
    reachable(); m.etag = tag; m.ok = m.sha.length == 64; return m;
}
static void state_write(void) { [[NSString stringWithFormat:@"base_sha=%@\n", g_synced_sha ?: @""] writeToFile:g_state_path atomically:YES encoding:NSUTF8StringEncoding error:nil]; }
static NSString *state_read(void) {
    NSString *t = [NSString stringWithContentsOfFile:g_state_path encoding:NSUTF8StringEncoding error:nil];
    return [t hasPrefix:@"base_sha="] && t.length >= 73 ? [t substringWithRange:NSMakeRange(9, 64)] : nil;
}

// ---------- push ----------
static BOOL push_retry(void) { atomic_store(&g_need_push, 1); return NO; }
static BOOL push_offline(const char *why) {
    if (!atomic_exchange(&g_offline, 1)) LOG("cloud save: push (%s) skipped, the server could not be reached; retried later", why);
    return push_retry();
}
static BOOL push_done(uint64_t commits) { atomic_store(&g_pushed_commits, commits); atomic_store(&g_need_push, 0); atomic_store(&g_failed, 0); atomic_store(&g_synced_at, (long)time(NULL)); return YES; }
static BOOL push_locked(const char *why) {
    uint64_t commits = dm_fs_commit_count();   // read before packing: the pack holds at least these commits
    uint64_t newest; NSData *a = pack_save(&newest);
    if (!a) { if (!g_pack_failed) LOG("[RED] cloud save: the save could not be packed (missing, unreadable or over %llu MB); not pushed", SAVE_MAX >> 20); g_pack_failed = 1; atomic_store(&g_failed, 1); return NO; }
    g_pack_failed = 0;
    if (a.length <= 8) return push_done(commits);   // no save (yet, or it is gone): never upload an empty one over the cloud's
    NSString *sha = sha256_hex(a);
    if ([sha isEqualToString:g_synced_sha]) return push_done(commits);
    atomic_store(&g_busy, 1);
    BOOL ok = NO; int round = 0;
    for (; round < 4 && !ok; round++) {
        // save.bin's ETag first, then save.meta: another device writes them in the other order, so a save.bin newer than the meta read here is seen as not ours
        int st; NSString *bin_etag;
        s3(@"HEAD", obj(@"save.bin"), nil, nil, &st, 15, &bin_etag);
        if (st != 200 && st != 404) { if (st) LOG("[RED] cloud save: the server answered HTTP %d", st); ok = st ? push_retry() : push_offline(why); break; }
        if (st == 404) bin_etag = nil;
        BOOL net; meta_t rm = get_meta(&net);
        if (net) { push_offline(why); break; }
        BOOL paired = rm.ok && (!rm.bin_etag || [rm.bin_etag isEqualToString:bin_etag]);   // save.bin is the one save.meta describes
        if (paired && [rm.sha isEqualToString:sha]) { g_synced_sha = g_remote_sha = sha; state_write(); ok = push_done(commits); break; }
        if (bin_etag && !(paired && [rm.sha isEqualToString:g_remote_sha])) {   // overwriting a save this device did not write: keep it, and do not overwrite it until it is kept
            NSString *hist = [NSString stringWithFormat:@"%@/%s/history/%@-%@.bin", g_prefix, DM_GAME_ID, utc("%Y%m%dT%H%M%SZ", time(NULL)), paired ? [rm.sha substringToIndex:8] : @"unpaired"];
            NSMutableDictionary *h = [NSMutableDictionary dictionaryWithObject:[NSString stringWithFormat:@"/%@/%@", g_bucket, uri_encode(obj(@"save.bin"))] forKey:@"x-amz-copy-source"];
            if (!g_no_cond) h[@"x-amz-copy-source-if-match"] = bin_etag;
            s3(@"PUT", hist, nil, h, &st, 60, NULL);
            if (st == 412) { LOG("cloud save: the remote save changed while it was being kept; checking again"); continue; }
            if (st != 200) { LOG("[RED] cloud save: keeping the remote save (changed by another device) in history/ failed (HTTP %d); not overwritten, the push is retried", st); atomic_store(&g_failed, st != 0); ok = push_retry(); break; }
            LOG("cloud save: the remote save was changed by another device; it is kept as %s", hist.UTF8String);
        }
        NSString *new_etag;
        s3(@"PUT", obj(@"save.bin"), a, cond(bin_etag), &st, 120, &new_etag);
        if (st == 501 && !g_no_cond) { g_no_cond = 1; LOG("cloud save: the server does not take conditional writes; uploads are unconditional"); continue; }
        if (st == 412 || st == 409) { LOG("cloud save: another device uploaded at the same moment; checking again"); continue; }
        if (st != 200) { LOG("[RED] cloud save: uploading save.bin failed (HTTP %d); it will be retried", st); atomic_store(&g_failed, st != 0); ok = push_retry(); break; }
        s3(@"PUT", obj(@"save.meta"), [meta_text(sha, newest, a.length, new_etag) dataUsingEncoding:NSUTF8StringEncoding], cond(rm.ok ? rm.etag : nil), &st, 30, NULL);
        if (st == 501 && !g_no_cond) { g_no_cond = 1; LOG("cloud save: the server does not take conditional writes; uploads are unconditional"); continue; }
        if (st == 412 || st == 409) { LOG("cloud save: another device uploaded at the same moment; checking again"); continue; }
        if (st != 200) { LOG("[RED] cloud save: uploading save.meta failed (HTTP %d); it will be retried", st); atomic_store(&g_failed, st != 0); ok = push_retry(); break; }
        g_synced_sha = g_remote_sha = sha; state_write(); atomic_store(&g_remote_newer, 0); push_done(commits);
        LOG("cloud save: pushed %zu bytes (%s)", a.length, why);
        ok = YES;
    }
    if (!ok && round == 4) { LOG("[RED] cloud save: uploads kept colliding with another device's; retried later"); atomic_store(&g_failed, 1); push_retry(); }
    atomic_store(&g_busy, 0);
    return ok;
}
// After a push (or none needed): does the cloud hold a save from another device that this run has not loaded? It is loaded at the next start, while the local save stays unchanged
static void check_remote_locked(void) {
    BOOL net; meta_t rm = get_meta(&net); if (net) return;
    int newer = rm.ok && ![rm.sha isEqualToString:g_remote_sha];
    if (newer && !atomic_load(&g_remote_newer)) LOG("cloud save: the cloud has a save from another device that this run has not loaded; restart to load it (saving first replaces it, keeping it in history/)");
    atomic_store(&g_remote_newer, newer);
    if (!newer) atomic_store(&g_synced_at, (long)time(NULL));
}

// ---------- start: pull ----------
static void prune_backups(void) {
    NSString *base = g_dir.lastPathComponent, *pfx = [base stringByAppendingString:@".before-sync-"]; NSFileManager *fm = NSFileManager.defaultManager; NSMutableArray *old = [NSMutableArray array];
    for (NSString *n in [fm contentsOfDirectoryAtPath:g_dir.stringByDeletingLastPathComponent error:nil]) if ([n hasPrefix:pfx]) [old addObject:n];
    [old sortUsingSelector:@selector(compare:)];
    while (old.count > 3) { [fm removeItemAtPath:[g_dir.stringByDeletingLastPathComponent stringByAppendingPathComponent:old[0]] error:nil]; [old removeObjectAtIndex:0]; }
}
static BOOL pull_remote(meta_t rm) {
    int st; NSData *a = s3(@"GET", obj(@"save.bin"), nil, nil, &st, 120, NULL);
    if (st != 200 || ![sha256_hex(a) isEqualToString:rm.sha]) { LOG("[RED] cloud save: downloading save.bin failed or does not match save.meta (HTTP %d); the local save is used", st); return NO; }
    NSString *tmp = [g_dir stringByAppendingString:@".cloud.tmp"]; NSFileManager *fm = NSFileManager.defaultManager;
    if (!unpack_to(a, tmp)) { LOG("[RED] cloud save: the downloaded save could not be unpacked; the local save is used"); [fm removeItemAtPath:tmp error:nil]; return NO; }
    if ([fm fileExistsAtPath:g_dir] && [fm contentsOfDirectoryAtPath:g_dir error:nil].count == 0) [fm removeItemAtPath:g_dir error:nil];   // nothing in it to keep
    if ([fm fileExistsAtPath:g_dir]) {   // swap the two directories in one step (killed at any moment, save/ is one whole save), then the old one becomes the backup
        NSString *bk = [NSString stringWithFormat:@"%@.before-sync-%@", g_dir, utc("%Y%m%dT%H%M%SZ", time(NULL))];
        for (int n = 1; [fm fileExistsAtPath:bk]; n++) bk = [NSString stringWithFormat:@"%@.before-sync-%@-%d", g_dir, utc("%Y%m%dT%H%M%SZ", time(NULL)), n];
        if (renamex_np(tmp.fileSystemRepresentation, g_dir.fileSystemRepresentation, RENAME_SWAP)) { LOG("[RED] cloud save: installing the downloaded save failed (errno %d); the local save is used", errno); [fm removeItemAtPath:tmp error:nil]; return NO; }
        if (rename(tmp.fileSystemRepresentation, bk.fileSystemRepresentation)) LOG("[RED] cloud save: the previous local save could not be renamed (errno %d); it is in %s until the next pull", errno, tmp.lastPathComponent.UTF8String);
        else LOG("cloud save: the previous local save is kept in %s", bk.lastPathComponent.UTF8String);
    }
    else if (rename(tmp.fileSystemRepresentation, g_dir.fileSystemRepresentation)) { LOG("[RED] cloud save: installing the downloaded save failed (errno %d)", errno); return NO; }
    prune_backups();
    g_synced_sha = g_remote_sha = rm.sha; state_write(); atomic_store(&g_synced_at, (long)time(NULL));
    LOG("cloud save: pulled %zu bytes from the cloud", a.length);
    return YES;
}
static void backoff(BOOL ok) {   // after any push: reset, or wait twice as long as last time before the next try
    if (ok) { atomic_store(&g_retry_ns, RETRY_MIN); atomic_store(&g_retry_at, 0); return; }
    uint64_t d = atomic_load(&g_retry_ns); atomic_store(&g_retry_at, now_ns() + d); atomic_store(&g_retry_ns, d * 2 > RETRY_MAX ? RETRY_MAX : d * 2);
}
static void *watch_thread(void *unused) {
    (void)unused; uint64_t last = atomic_load(&g_pushed_commits), dirty_at = 0;
    for (;;) {
        sleep(2);
        uint64_t c = dm_fs_commit_count(), t = now_ns();
        if (c != last) { last = c; dirty_at = t; }
        BOOL due = dirty_at && t - dirty_at >= 8000000000ull;   // 8 s after the last commit
        if ((due || atomic_load(&g_need_push)) && t >= atomic_load(&g_retry_at)) {
            BOOL ok; @autoreleasepool { pthread_mutex_lock(&g_mu); ok = push_locked("save committed"); pthread_mutex_unlock(&g_mu); }   // a pthread has no pool of its own: without this every pack (the whole save) stays in memory
            if (ok) dirty_at = 0;
            backoff(ok);
        }
    }
    return NULL;
}

static void load_config_file(void) {
    const char *f = getenv("DM_CLOUD_CONFIG"); if (!f || !*f) return;
    NSString *txt = [NSString stringWithContentsOfFile:@(f) encoding:NSUTF8StringEncoding error:nil];
    for (NSString *raw in [txt componentsSeparatedByCharactersInSet:NSCharacterSet.newlineCharacterSet]) {
        NSString *ln = [raw stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceCharacterSet]; NSRange eq = [ln rangeOfString:@"="];
        if (!ln.length || [ln hasPrefix:@"#"] || eq.location == NSNotFound || !eq.location) continue;
        setenv([ln substringToIndex:eq.location].UTF8String, [ln substringFromIndex:eq.location + 1].UTF8String, 0);
    }
}
void dm_cloud_start(void) {
    load_config_file();
    const char *ep = getenv("DM_CLOUD_S3_ENDPOINT"), *bk = getenv("DM_CLOUD_S3_BUCKET"), *ak = getenv("DM_CLOUD_S3_KEY"), *sk = getenv("DM_CLOUD_S3_SECRET"), *sd = getenv("DM_SAVE");
    if (!ep || !*ep) return;
    if (!bk || !*bk || !ak || !*ak || !sk || !*sk) { LOG("[RED] cloud save: DM_CLOUD_S3_ENDPOINT is set but DM_CLOUD_S3_BUCKET / _KEY / _SECRET are not all set; cloud save is off"); return; }
    if (!sd || !*sd) { LOG("[RED] cloud save: DM_SAVE is not set; cloud save is off"); return; }
    if (strncmp(ep, "https://", 8) && strncmp(ep, "http://127.0.0.1", 16) && strncmp(ep, "http://localhost", 16)) { LOG("[RED] cloud save: the endpoint must start with https:// (http only for localhost, for tests); cloud save is off"); return; }
    g_ep = @(ep); while ([g_ep hasSuffix:@"/"]) g_ep = [g_ep substringToIndex:g_ep.length - 1];
    g_bucket = @(bk); g_ak = @(ak); g_sk = @(sk);
    const char *rg = getenv("DM_CLOUD_S3_REGION"), *px = getenv("DM_CLOUD_S3_PREFIX");
    g_region = rg && *rg ? @(rg) : @"auto"; g_prefix = px && *px ? @(px) : @"nxnative";
    g_dir = @(sd); while (g_dir.length > 1 && [g_dir hasSuffix:@"/"]) g_dir = [g_dir substringToIndex:g_dir.length - 1];
    g_state_path = [g_dir.stringByDeletingLastPathComponent stringByAppendingPathComponent:@"cloud_state.txt"];
    NSURLSessionConfiguration *cfg = NSURLSessionConfiguration.ephemeralSessionConfiguration; cfg.URLCache = nil; cfg.HTTPCookieStorage = nil; cfg.waitsForConnectivity = NO;
    g_sess = [NSURLSession sessionWithConfiguration:cfg];
    atomic_store(&g_on, 1);
    LOG("cloud save: on, bucket %s at %s, prefix %s", bk, [NSURL URLWithString:g_ep].host.UTF8String ?: "?", g_prefix.UTF8String);
    pthread_mutex_lock(&g_mu);
    uint64_t t0 = now_ns(), lnew; NSData *la = pack_save(&lnew); NSString *lsha = la ? sha256_hex(la) : nil; BOOL lempty = !la || la.length <= 8;
    NSString *base = state_read(); BOOL net; meta_t rm = get_meta(&net);
    if (net) { LOG("cloud save: the server could not be reached; the local save is used (it is uploaded later)"); g_synced_sha = base; g_remote_sha = base; atomic_store(&g_need_push, 1); }
    else if (!rm.ok) { LOG("cloud save: nothing in the cloud yet; the local save is uploaded%s", lempty ? " once there is one" : ""); g_synced_sha = nil; g_remote_sha = nil; if (!lempty) atomic_store(&g_need_push, 1); }
    else if ([rm.sha isEqualToString:lsha]) { g_synced_sha = g_remote_sha = rm.sha; state_write(); atomic_store(&g_synced_at, (long)time(NULL)); LOG("cloud save: in sync"); }
    else {
        BOOL local_changed = !(base && [base isEqualToString:lsha]), remote_changed = !(base && [base isEqualToString:rm.sha]);
        BOOL take_remote;
        if (lempty) take_remote = YES;
        else if (!local_changed) take_remote = YES;
        else if (!remote_changed) take_remote = NO;
        else if (!base) { take_remote = YES; LOG("cloud save: first sync of this device and the saves differ; the cloud save is used, the local one is kept"); }
        else { take_remote = rm.mtime > lnew; LOG("cloud save: both the local and the cloud save changed; the newer one (%s) wins, the other is kept", take_remote ? "cloud" : "local"); }
        g_synced_sha = base; g_remote_sha = remote_changed && !take_remote ? nil : rm.sha;   // a cloud save that is about to be overwritten is not ours: the push copies it to history/
        if (take_remote) { if (!pull_remote(rm)) { g_remote_sha = nil; atomic_store(&g_need_push, 0); } }   // not pulled: the cloud save is not ours, a later push keeps it in history/ before overwriting it
        else { if (!remote_changed) LOG("cloud save: the local save changed since the last sync; it is uploaded"); atomic_store(&g_need_push, 1); }
    }
    atomic_store(&g_pushed_commits, dm_fs_commit_count());
    pthread_mutex_unlock(&g_mu);
    LOG("cloud save: start-up sync took %.2f s", (now_ns() - t0) / 1e9);
    pthread_t th; if (!pthread_create(&th, NULL, watch_thread, NULL)) pthread_detach(th);
}

// Upload now when something changed since the last push; waits at most `timeout` seconds (graceful exit, closing the window)
void dm_cloud_flush(double timeout) {
    if (!atomic_load(&g_on)) return;
    dispatch_group_t g = dispatch_group_create();
    dispatch_group_async(g, dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{ pthread_mutex_lock(&g_mu); backoff(push_locked("flush")); pthread_mutex_unlock(&g_mu); });
    dispatch_group_wait(g, dispatch_time(DISPATCH_TIME_NOW, (int64_t)(timeout * NSEC_PER_SEC)));
}
// Going to the background: upload without waiting; on iOS the work runs inside an expiring activity so the system lets it finish
void dm_cloud_flush_async(void) {
    if (!atomic_load(&g_on)) return;
    void (^work)(void) = ^{ pthread_mutex_lock(&g_mu); backoff(push_locked("background")); pthread_mutex_unlock(&g_mu); };
#if TARGET_OS_IPHONE
    [NSProcessInfo.processInfo performExpiringActivityWithReason:@"cloud save upload" usingBlock:^(BOOL expired) {
        if (!expired) { work(); return; }
        LOG("[RED] cloud save: background time ran out; the upload is cancelled and retried when the app is back");   // the uploads fail at once, push_locked marks a retry, the activity ends before iOS suspends the app
        [g_sess getAllTasksWithCompletionHandler:^(NSArray<NSURLSessionTask *> *ts) { for (NSURLSessionTask *t in ts) [t cancel]; }];
    }];
#else
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), work);
#endif
}
// The player asked to sync (the Mac's Cloud Save menu): upload a save not yet pushed, whatever the retry wait, then look for another device's newer save
void dm_cloud_sync_now(void) {
    if (!atomic_load(&g_on)) return;
    atomic_store(&g_busy, 1);
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        pthread_mutex_lock(&g_mu);
        BOOL ok = push_locked("sync now"); backoff(ok);
        if (ok) check_remote_locked();
        atomic_store(&g_busy, 0);
        pthread_mutex_unlock(&g_mu);
    });
}
// One line for the player: 0 when cloud save is off
int dm_cloud_status(char *out, size_t n) {
    if (!atomic_load(&g_on)) return 0;
    uint64_t t = now_ns(), ra = atomic_load(&g_retry_at); long at = atomic_load(&g_synced_at);
    unsigned wait = ra > t ? (unsigned)((ra - t) / 1000000000ull) + 1 : 0;
    BOOL pending = atomic_load(&g_need_push) || dm_fs_commit_count() != atomic_load(&g_pushed_commits);
    char when[16] = ""; if (at) { struct tm tm; time_t tt = at; localtime_r(&tt, &tm); strftime(when, sizeof when, "%H:%M", &tm); }
    if (atomic_load(&g_busy)) snprintf(out, n, "Cloud save: syncing...");
    else if (atomic_load(&g_remote_newer)) snprintf(out, n, "Cloud save: another device's newer save is in the cloud; restart to load it");
    else if (atomic_load(&g_offline)) snprintf(out, n, pending ? (wait ? "Cloud save: offline, not uploaded yet (retry in %u s)" : "Cloud save: offline, not uploaded yet") : "Cloud save: offline", wait);
    else if (atomic_load(&g_failed)) snprintf(out, n, wait ? "Cloud save: upload failed (retry in %u s)" : "Cloud save: upload failed", wait);
    else if (pending) snprintf(out, n, "Cloud save: saved, uploading shortly");
    else if (at) snprintf(out, n, "Cloud save: synced at %s", when);
    else snprintf(out, n, "Cloud save: on");
    return 1;
}
