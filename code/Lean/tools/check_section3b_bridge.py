#!/usr/bin/env python3
"""Independent exact-arithmetic and source-boundary checks for Section 3B.

Not a Lean kernel check: the new source must be compiled under the pinned
Lean/Mathlib toolchain before it is called a verified formalization.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import json
import random
import re

ROOT = Path(__file__).resolve().parents[1]

@lru_cache(None)
def osz(p, q, i):
    if q == 0:
        assert p == 1
        return F(0)
    return F(p*q - (2*i+1-p-q)**2, 4*p*q) - osz(q,p%q,i%q)

def spinBase(p,q):
    return ((p+(p-q)-1)*((p+1)//2))%p

def dY(j):
    return osz(245,141,(70+j)%245)

def Q(h,a,s):
    return [[h,1,a,0],[1,2,0,0],[a,0,s,1],[0,0,1,2]]

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def mv(M,y):return [dot(row,y) for row in M]

def inverse(matrix):
    size = len(matrix)
    rows = [[F(x) for x in row] + [F(i == j) for j in range(size)]
            for i, row in enumerate(matrix)]
    for i in range(size):
        pivot = next(k for k in range(i, size) if rows[k][i])
        rows[i], rows[pivot] = rows[pivot], rows[i]
        rows[i] = [x / rows[i][i] for x in rows[i]]
        for k, row in enumerate(rows):
            if k != i:
                rows[k] = [x - row[i] * y for x, y in zip(row, rows[i])]
    return [row[size:] for row in rows]

CANDIDATES=[(2,1,42),(4,0,18),(8,5,12),(14,11,14),(62,61,62)]

# Nontrivial facts checked without relying on the Lean source's table.
# Since 245 >= 4h - 3, h <= 62. Solve the determinant equation for s.
forms = []
for h in range(2, 63, 2):
    for a in range(h):
        two_s_minus_one, rem = divmod(245 + 4 * a * a, 2 * h - 1)
        if rem == 0 and two_s_minus_one % 4 == 3:
            s = (two_s_minus_one + 1) // 2
            if h <= s:
                forms.append((h, a, s))
assert forms == CANDIDATES
assert spinBase(245,104)==70
assert 245-104==141
assert dY(0)==-1

# Check all 245 recursion entries against the literal Lean certificate table.
s=(ROOT/'Trefoil/FiniteCorrectionTerms.lean').read_text()
m=re.search(r'private def scaledData : Array ℤ := #\[(.*?)\]',s,re.S)
assert m, 'missing Lean correction-term table'
table=[int(x) for x in re.findall(r'-?\d+',m.group(1))]
assert len(table)==245,len(table)
for j in range(245):
    assert 245*dY(j)==table[j],(j,dY(j),table[j])
    assert (2*j)%245==((j+j)%245)

# General spin-center convention, including odd p not in this family.
general_spin_checks=0
for p in range(3,252,2):
    for q in range(1,p):
        if gcd(p,q)!=1: continue
        i=spinBase(p,q)
        assert (2*i-(p+(p-q)-1))%p==0
        assert sum((2*j-(p+(p-q)-1))%p==0 for j in range(p))==1
        general_spin_checks+=1

# Characteristic class and even-parity formula b(x+Qy)-b(x).
# Q has even diagonal, so 2*y.x + y^T Q y is always even.
rng=random.Random(20261120)
parity_checks=0
for h,a,s in CANDIDATES:
    mat=Q(h,a,s)
    inv=inverse(mat)
    for _ in range(750):
        x=[rng.randint(-20,20) for _ in range(4)]
        y=[rng.randint(-15,15) for _ in range(4)]
        delta=2*dot(x,y)+dot(y,mv(mat,y))
        shifted=[xi+z for xi,z in zip(x,mv(mat,y))]
        assert dot(shifted,mv(inv,shifted))-dot(x,mv(inv,x))==delta
        assert delta%2==0
        parity_checks+=1

# There is no spin-centered label satisfying the already-checked necessary
# tests in the five candidate cases.
def admissible(b,j):
    t=b-table[j]
    return t>=0 and t%490==0
assert all(not admissible(-199,j) for j in range(245))
assert all(not admissible(1,j) for j in range(245))
assert all(not admissible(-225,j) for j in range(245))
assert all(not admissible(-175,j) for j in range(245))
assert all(not (admissible(-239,j) and admissible(-221,(2*j)%245))
           for j in range(245))

# Source-level lint is supplementary; it cannot replace Lean typechecking.
new=[ROOT/'Trefoil/Section3BMinimum.lean',ROOT/'Trefoil/Section3BTopology.lean',
     ROOT/'Trefoil/Section3LowerBound.lean',
     ROOT/'SECTION3B_Reference_Audit.lean']
for f in new:
    t=f.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',t)
    assert 'section3B' in t or 'minimum_to_comparison' in t
report={
    'status':'independent_arithmetic_passed',
    'correction_terms_exactly_checked':len(table),
    'candidate_forms':CANDIDATES,
    'spin_conventions_checked':general_spin_checks,
    'quadratic_class_parity_checks':parity_checks,
    'obstruction_cases_checked':5,
    'new_lean_files':[str(f.relative_to(ROOT)) for f in new],
    'provenance':'This arithmetic check runs independently of the Lean build.'
}
(ROOT/'reports/section3b-independent-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
