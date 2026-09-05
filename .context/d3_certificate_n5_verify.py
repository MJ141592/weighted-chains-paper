"""Exact verifier for the d=3,k=2,n=5 fibre-LYM certificate.

Run with Python 3; only stdlib Fraction is used.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial, prod

def compositions(total, parts, prefix=()):
    if parts == 1:
        yield prefix + (total,)
    else:
        for i in range(total + 1):
            yield from compositions(total - i, parts - 1, prefix + (i,))

n, d, k = 5, 3, 2
types = list(compositions(n, d + 1))
outside = list(compositions(n - k, d + 1))
rank_size = [sum(sum(u) == r for u in product(range(d + 1), repeat=k))
             for r in range(d * k + 1)]
weights = [
    '1/10','2/15','17/90','1117/3240','13/90','2503/9720',
    '559/1620','79/270','893/2430','14/45','167/540','1123/3240',
    '1313/4860','169/540','907/3240','17/90','3/20','59/360','2/15','1/10'
]
lam = {z: Q(v) for z, v in zip(outside, weights)}

def coefficient(t):
    c = Q(0)
    for z in outside:
        u = tuple(t[i] - z[i] for i in range(d + 1))
        if min(u) < 0 or sum(u) != k:
            continue
        multiplicity = 1
        for i in range(d + 1):
            multiplicity *= comb(t[i], u[i])
        local_rank = sum(i * u[i] for i in range(d + 1))
        c += lam[z] * Q(multiplicity, rank_size[local_rank])
    return c

assert all(coefficient(t) >= 1 for t in types)
objective = comb(n, k) * sum(
    Q(factorial(n - k), 1) / prod(factorial(v) for v in z) * lam[z]
    for z in outside
)
assert objective == 161
print('verified:', len(types), 'type inequalities; objective =', objective)
