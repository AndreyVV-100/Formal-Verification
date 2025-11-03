#ifndef DIMACS_H
#define DIMACS_H

#include <stdio.h>

#ifdef __cplusplus
#define DIMACS_EXPORT extern "C"
#else
#define DIMACS_EXPORT
#endif

typedef void (*dimacs_header_func)(void *, int, int);
typedef void (*dimacs_clause_func)(void *, int, int *, int);

DIMACS_EXPORT int dimacs_fread(
    FILE *file, void *udata, dimacs_header_func, dimacs_clause_func);

#endif
