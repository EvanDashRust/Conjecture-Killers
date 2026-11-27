"""Exact r=1 exclusion assuming the numerical moduli 25 and 27 are both absent."""
from fractions import Fraction as Q
from cross_heights import LIMIT, MISSING_FIFTEEN, check_loss, head_law, primes_through


def certificate(t, primes):
    g3,g5 = Q(54,29),Q(100,79)
    mixed = (1-t)*g5/5 + t*g5/20 + (g3/6)*(g5/4)
    parts = check_loss(primes,g3,g5,head_law(t,None,None),11,MISSING_FIFTEEN)
    total = mixed + sum(parts)
    print(f"orbit=1 absent=[25, 27] t={t} mixed={mixed} total={total} ({float(total):.12f})",flush=True)
    assert total < 1


if __name__=='__main__':
    primes=primes_through(LIMIT)
    for t in (Q(17,29),Q(18,29)):
        certificate(t,primes)
