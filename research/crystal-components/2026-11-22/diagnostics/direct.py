"""Direct definition and enumeration of canonical factor pairs."""
from math import isqrt

def accepts(n, a, b):
    return (n > 0 and n % 2 == 1 and a > 1 and b > 1 and n == a * b
            and ((a + b)**2 + (a*b + 1)**2) % (2*(a+1)*(b+1)) == 0)

def pairs(n):
    return {(a,n//a) for a in range(2, isqrt(n)+1)
            if n % a == 0 and accepts(n,a,n//a)}

def different(a, b, c, d):
    return tuple(sorted((a,b))) != tuple(sorted((c,d)))
