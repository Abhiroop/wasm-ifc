/* The password checker of the paper's overview (section 3), written for information-flow
 * control: it reads a password from a file in /secrets, compares a hash of it with a dictionary
 * of weak passwords, shows the verdict on its standard output, and appends a record of the run
 * to a log in /log that is shared with the developer. The password must not reach the log.
 *
 * Unlike password-naive.c, the code that handles the password does not branch on it: the hash
 * runs over the whole buffer and masks the bytes past the end, the comparisons are combined
 * arithmetically, and the verdict is chosen by an offset rather than by a branch. A branch on a
 * secret raises the pc of the rest of its block, and a call to the host (every write) needs a
 * public pc; the compiler freely moves a write into the block of such a branch.
 *
 * LEAK selects a variant that leaks:
 *   (none)          the log records only public information: the number of entries checked
 *   LEAK_CONTROL    the log records whether the password was weak, chosen by a branch
 *   LEAK_MEMORY     the log records the hash, through a buffer in memory
 */
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

/* djb2 hashes of the dictionary's weak passwords: "123456", "password", "qwerty", "letmein". */
static const uint32_t weak[] = {0x7dd1705au, 0x17f6dc38u, 0x1818ae71u, 0x715ae1b3u};
#define ENTRIES (sizeof weak / sizeof weak[0])
#define CAPACITY 64

static char password[CAPACITY];
static char record[64];
static const char verdicts[] = "ok\n\0\0weak\n"; /* "ok\n" at 0, "weak\n" at 5 */

/* The djb2 hash of the first length bytes, computed over the whole buffer. */
static uint32_t djb2(const char *text, uint32_t length) {
    uint32_t h = 5381;
    for (uint32_t i = 0; i < CAPACITY; i++) {
        uint32_t keep = -(uint32_t)(i < length);
        uint32_t next = h * 33 + (unsigned char)text[i];
        h = (next & keep) | (h & ~keep);
    }
    return h;
}

/* Write a decimal number into the record at position at; return the new position. */
static int put_number(int at, uint32_t n) {
    char digits[10];
    int count = 0;
    do {
        digits[count++] = (char)('0' + n % 10);
        n /= 10;
    } while (n != 0);
    while (count > 0) record[at++] = digits[--count];
    return at;
}

int main(void) {
    int in = open("/secrets/password", O_RDONLY);
    if (in < 0) return 1;
    int count = (int)read(in, password, sizeof password);
    close(in);
    if (count < 0) return 1;

    /* Drop one trailing newline. */
    uint32_t length = (uint32_t)count;
    uint32_t last = (unsigned char)password[(length - 1) % CAPACITY];
    length -= (uint32_t)(length > 0) & (uint32_t)(last == '\n');

    uint32_t hash = djb2(password, length);
    uint32_t matched = 0;
    for (unsigned i = 0; i < ENTRIES; i++) matched |= (uint32_t)(hash == weak[i]);

    write(1, verdicts + 5 * matched, 3 + 2 * matched);

    int log = open("/log/runs.log", O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (log < 0) return 1;
    memcpy(record, "checked ", 8);
    int at = put_number(8, ENTRIES);
#if defined(LEAK_CONTROL)
    if (matched) {
        memcpy(record + at, " weak", 5);
        at += 5;
    }
#elif defined(LEAK_MEMORY)
    record[at++] = ' ';
    at = put_number(at, hash);
#endif
    record[at++] = '\n';
    write(log, record, (size_t)at);
    close(log);
    return 0;
}
