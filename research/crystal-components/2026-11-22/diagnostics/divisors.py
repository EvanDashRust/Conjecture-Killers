"""Divisors of t² from trial factorization of t, followed by signed reconstruction."""
from math import isqrt

def square_divisors(t):
    values = [1]
    prime = 2
    while prime * prime <= t:
        exponent = 0
        while t % prime == 0:
            t //= prime
            exponent += 1
        if exponent:
            values = [d * prime**j for d in values for j in range(2*exponent+1)]
        prime = 3 if prime == 2 else prime + 2
    if t > 1:
        values = [d * u for d in values for u in (1,t,t*t)]
    return values

def reconstruct(n, D):
    if n < 1 or n % 2 == 0 or D <= 0 or (n+1)**2 % D:
        return None
    s = D-(n+1)
    delta = s*s-4*n
    if delta < 0:
        return None
    q = isqrt(delta)
    if q*q != delta or (s-q) % 2:
        return None
    a, b = (s-q)//2, (s+q)//2
    return (a,b) if a > 1 and b > 1 and a*b == n else None

def pairs(n):
    if n < 1 or n % 2 == 0:
        return set()
    return {pair for D in square_divisors(n+1) if (pair := reconstruct(n,D)) is not None}

def accepts(n,a,b):
    if a*b != n:
        return False
    return reconstruct(n, n+1+a+b) == tuple(sorted((a,b)))
