#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "kernel.h"

static FILE *trace;
static void *module;
static Triangulation *trace_manifold;
static char label[100];
static int verbosity;

static void *symbol(const char *name) {
    if (!module) {
        module = dlopen(getenv("SNAPPY_TRACE_MODULE"), RTLD_LAZY | RTLD_NOLOAD);
        if (!module) { fprintf(stderr, "%s\n", dlerror()); abort(); }
    }
    void *result = dlsym(module, name);
    if (!result) abort();
    return result;
}

// The trace only writes objects explicitly selected by the replay driver.
void trace_select(const char *name, int level) {
    if (!trace) {
        trace = fopen(getenv("SNAPPY_TRACE_FILE"), "w");
        if (!trace) abort();
    }
    snprintf(label, sizeof(label), "%s", name);
    verbosity = level;
}

typedef struct {
    int num;
    uintptr_t *tet;
} Inventory;

static Inventory index_tets(const Triangulation *t) {
    int num = t->num_tetrahedra;
    Inventory result = {num, calloc(num > 0 ? num : 1, sizeof(uintptr_t))};
    int i = 0;
    for (const Tetrahedron *tet = t->tet_list_begin.next; tet != &t->tet_list_end; tet = tet->next) {
        if (i >= num) { fprintf(stderr, "tet index too big %d / %d\n", i, num); abort(); }
        result.tet[i++] = (uintptr_t) tet;
    }
    if (i != num) abort();
    return result;
}

static int find(const Inventory *a, uintptr_t ptr) {
    for (int i = 0; i < a->num; i++)
        if (a->tet[i] == ptr) return i;
    return -1;
}

static void snapshot(const Triangulation *t, const char *event, const Inventory *before, int removed, int side) {
    if (!verbosity) return;
    Inventory after = index_tets(t);
    fprintf(trace, "{\"label\":\"%s\",\"event\":\"%s\",\"removed\":%d,\"side\":%d,",
            label, event, removed, side);
    fprintf(trace, "\"oldToNew\":[");
    if (before)
        for (int i = 0; i < before->num; i++)
            fprintf(trace, "%s%d", i ? "," : "", find(&after, before->tet[i]));
    fprintf(trace, "],\"tets\":[");
    for (int i = 0; i < after.num; i++) {
        const Tetrahedron *tet = (const Tetrahedron *) after.tet[i];
        fprintf(trace, "%s{\"neighbor\":[", i ? "," : "");
        for (int j = 0; j < 4; j++)
            fprintf(trace, "%s%d", j ? "," : "", find(&after, (uintptr_t)tet->neighbor[j]));
        fprintf(trace, "],\"gluing\":[");
        for (int j = 0; j < 4; j++) {
            fprintf(trace, "%s[", j ? "," : "");
            for (int k = 0; k < 4; k++)
                fprintf(trace, "%s%d", k ? "," : "", EVALUATE(tet->gluing[j],k));
            fprintf(trace, "]");
        }
        fprintf(trace, "],\"cusp\":[");
        for (int j = 0; j < 4; j++)
            fprintf(trace, "%s%d", j ? "," : "", tet->cusp[j] ? tet->cusp[j]->index : -999);
        fprintf(trace, "],\"curve\":[");
        for (int l = 0; l < 64; l++) {
            int c = l/32, h = (l/16)%2, v = (l/4)%4, f = l%4;
            fprintf(trace, "%s%d", l ? "," : "", tet->curve[c][h][v][f]);
        }
        fprintf(trace, "]}");
    }
    fprintf(trace, "]}\n");
    fflush(trace);
    free(after.tet);
}

FuncResult proto_canonize(Triangulation *m) {
    static FuncResult (*call)(Triangulation *);
    if (!call) call = symbol("proto_canonize");
    Triangulation *keep = trace_manifold;
    if (verbosity) { trace_manifold = m; snapshot(m, "proto_begin", NULL, -1, -1); }
    FuncResult out = call(m);
    if (verbosity) snapshot(m, "proto_end", NULL, -1, -1);
    trace_manifold = keep;
    return out;
}

void canonical_retriangulation(Triangulation *m) {
    static void (*call)(Triangulation *);
    if (!call) call = symbol("canonical_retriangulation");
    Triangulation *keep = trace_manifold;
    if (verbosity) { trace_manifold = m; snapshot(m, "canonical_begin", NULL, -1, -1); }
    call(m);
    if (verbosity) snapshot(m, "canonical_end", NULL, -1, -1);
    trace_manifold = keep;
}

void remove_finite_vertices(Triangulation *m) {
    static void (*call)(Triangulation *);
    if (!call) call = symbol("remove_finite_vertices");
    Triangulation *keep = trace_manifold;
    if (verbosity >= 2) { trace_manifold = m; snapshot(m, "finite_removal_begin", NULL, -1, -1); }
    call(m);
    if (verbosity >= 2) snapshot(m, "finite_removal_end", NULL, -1, -1);
    trace_manifold = keep;
}

static int recording(int *n) { return verbosity && trace_manifold && n == &trace_manifold->num_tetrahedra; }

FuncResult two_to_three(Tetrahedron *t, FaceIndex f, int *n) {
    static FuncResult (*call)(Tetrahedron *, FaceIndex, int *);
    if (!call) call = symbol("two_to_three");
    if (!recording(n)) return call(t,f,n);
    Inventory before = index_tets(trace_manifold);
    int index = find(&before, (uintptr_t)t);
    FuncResult out = call(t,f,n);
    if (out == func_OK) snapshot(trace_manifold, "2-3", &before, index, f);
    free(before.tet);
    return out;
}

FuncResult three_to_two(EdgeClass *e, EdgeClass **resume, int *n) {
    static FuncResult (*call)(EdgeClass *, EdgeClass **, int *);
    if (!call) call = symbol("three_to_two");
    if (!recording(n)) return call(e,resume,n);
    Inventory before = index_tets(trace_manifold);
    int index = find(&before, (uintptr_t)e->incident_tet);
    int edge = e->incident_edge_index;
    FuncResult out = call(e,resume,n);
    if (out == func_OK) snapshot(trace_manifold, "3-2", &before, index, edge);
    free(before.tet);
    return out;
}

FuncResult cancel_tetrahedra(EdgeClass *e, EdgeClass **resume, int *n) {
    static FuncResult (*call)(EdgeClass *, EdgeClass **, int *);
    if (!call) call = symbol("cancel_tetrahedra");
    if (!recording(n)) return call(e,resume,n);
    Inventory before = index_tets(trace_manifold);
    int index = find(&before, (uintptr_t)e->incident_tet);
    int edge = e->incident_edge_index;
    FuncResult out = call(e,resume,n);
    if (out == func_OK) snapshot(trace_manifold, "cancel", &before, index, edge);
    free(before.tet);
    return out;
}

void one_to_four(Tetrahedron *t, int *n, int cusp) {
    static void (*call)(Tetrahedron *, int *, int);
    if (!call) call = symbol("one_to_four");
    if (!recording(n)) { call(t,n,cusp); return; }
    Inventory before = index_tets(trace_manifold);
    int index = find(&before, (uintptr_t)t);
    call(t,n,cusp);
    snapshot(trace_manifold, "1-4", &before, index, cusp);
    free(before.tet);
}

void tidy_peripheral_curves(Triangulation *m) {
    static void (*call)(Triangulation *);
    if (!call) call = symbol("tidy_peripheral_curves");
    if (!verbosity || m != trace_manifold) { call(m); return; }
    Inventory before = index_tets(m);
    call(m);
    snapshot(m, "tidy", &before, -1, -1);
    free(before.tet);
}
