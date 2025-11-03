#include "dimacs.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

static int
mygetline(char **inmem, size_t *insize, FILE *file) {
    char *buf = *inmem;
    size_t bufsize = *insize;
    if (!buf) {
        char *mem = (char *) malloc(BUFSIZ / 2);
        if (!mem) {
            return -1;
        }
        buf = mem;
        bufsize = BUFSIZ / 2;

        *inmem = buf;
        *insize = bufsize;
    }
    size_t ntotal = 0;
    size_t nleft = bufsize - 1;

    char *endl = NULL;
    while (!endl) {
        if (nleft == 0) {
            char *mem = (char *) realloc(buf, bufsize * 2);
            if (!mem) {
                return -1;
            }
            nleft += bufsize;
            buf = mem;
            bufsize *= 2;

            *inmem = buf;
            *insize = bufsize;
        }

        size_t nread = fread(buf + ntotal, 1, nleft, file);
        buf[ntotal + nread] = '\0';

        if (nread < nleft && ferror(file)) {
            return -1;
        }
        endl = strchr(buf + ntotal, '\n');
        if (!endl && feof(file)) {
            endl = buf + ntotal + nread;
        }
        ntotal += nread;
        nleft -= nread;
    }
    int len = endl - buf;
    if (len > 0 && buf[len - 1] == '\r') {
        --len;
    }
    buf[len] = '\0';

    long offset = ntotal - (endl - buf + 1);
    if (offset > 0 && fseek(file, -offset, SEEK_CUR) != 0) {
        return -1;
    }
    return len;
}

void
on_clause_print(void *log, int clno, int *clause, int nlit) {
    FILE *file = (FILE *) log;
    fprintf(file, "clause %d (%d vars): %d", clno, nlit, clause[0]);
    for (int i = 1; i < nlit; ++i) {
        fprintf(file, " V %d", clause[i]);
    }
    fprintf(file, "\n");
}

#define COUNTOF(x) (sizeof((x)) / sizeof(*(x)))

int
dimacs_fread(
        FILE *file,
        void *udata,
        dimacs_header_func on_header,
        dimacs_clause_func on_clause) {
    int rc = 0;
    char *line = NULL;
    size_t linesz = 0;
    int lineno = 1;

    int nlit = 0, ncls = 0;

    int litbufsz = 256;
    int *litbuf = (int *) malloc(litbufsz * sizeof(*litbuf));
    if (!litbuf) {
        rc = -1;
        goto dimacs_exit;
    }

    while (!feof(file) && (rc = mygetline(&line, &linesz, file)) >= 0) {
        const char *s = line;
        while (isspace(*s)) {
            ++s;
        }
        if (*s == 'p') {
            int varsdecl = 0, clsdecl = 0;
            if (sscanf(s, "p cnf %d %d", &varsdecl, &clsdecl) != 2) {
                rc = -1;
                goto dimacs_exit;
            }
            if (on_header) {
                on_header(udata, varsdecl, clsdecl);
            }
        } else if (*s == '-' || isdigit(*s)) {
            int lit = 0;
            while ((rc = sscanf(s, "%d", &lit)) == 1) {
                if (nlit >= litbufsz) {
                    void *mem = realloc(litbuf, litbufsz * 2 * sizeof(*litbuf));
                    if (!mem) {
                        rc = -1;
                        goto dimacs_exit;
                    }
                    litbuf = (int *) mem;
                    litbufsz *= 2;
                }
                if (lit != 0 && nlit < litbufsz) {
                    litbuf[nlit++] = lit;
                } else if (lit == 0) {
                    /* zero terminates clause, handles multiline clauses */
                    ++ncls;
                    if (on_clause) {
                        on_clause(udata, ncls, litbuf, nlit);
                    }
                    nlit = 0;
                    break;
                }
                while (isspace(*s)) {
                    ++s;
                }
                while (*s && !isspace(*s)) {
                    ++s;
                }
            }
            if (rc != 1 && *s) {
                rc = -1;
                goto dimacs_exit;
            }
        }
        ++lineno;
    }

dimacs_exit:
    free(line);
    free(litbuf);
    return (rc < 0) ? lineno : 0;
}

/*
int
main(int argc, char *argv[]) {
    char errmsg[256];
    for (int i = 1; i < argc; ++i) {
        FILE *file = fopen(argv[i], "rb");
        if (!file) {
            perror(argv[i]);
            continue;
        }
        int lineno = dimacs_fread(file, stderr, NULL, on_clause_print);
        if (lineno) {
            snprintf(errmsg, sizeof(errmsg), "%s:%d", argv[i], lineno);
            perror(errmsg);
        }
        fclose(file);
    }
    return 0;
}
*/
