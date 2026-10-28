#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

/* The execution host exposes /proc/self/exe but not /proc/<own-pid>/exe.
 * Translate only that equivalent self-reference after ENOENT or EACCES. This changes
 * executable-path discovery, not Lean's elaborator, kernel, or proof objects.
 */
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    if (!original) { errno = ENOSYS; return -1; }
    ssize_t result = original(path, buf, size);
    if (result == -1 && (errno == ENOENT || errno == EACCES)) {
        char self[64];
        snprintf(self, sizeof self, "/proc/%ld/exe", (long)getpid());
        if (strcmp(path, self) == 0)
            return original("/proc/self/exe", buf, size);
    }
    return result;
}
