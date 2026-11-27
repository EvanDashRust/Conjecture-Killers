"""Count rough prime coordinates that occur on classes divisible by 25 or 27."""
from fractions import Fraction as Q
from cross_heights import MISSING_FIFTEEN, primes_through
from high_counts import MARGINS

# All possible smooth weights, split into the disjoint cases a>=3 and a<=2,b>=2.
s = Q(2,18)*(1+Q(4,3)/4) + Q(4,3)/20*(1+Q(2,3)+Q(2,9))
assert s == Q(37,135)
limit=200
entries=[]
for p in primes_through(limit):
    if p<11:
        continue
    delta=Q(MISSING_FIFTEEN[p],p-1) if p in MISSING_FIFTEEN else Q(3,10)
    entries.append((1/((1-delta)*(p-1)),p))
entries.sort(reverse=True)
# For larger primes delta=3/10. None can enter the first ten.
assert Q(10,7*limit)<entries[9][0]
for orbit,target in enumerate(MARGINS["both"],1):
    product=1
    for i,(term,p) in enumerate(entries,1):
        upper=s*(product-1)
        product*=1+term
        if s*(product-1)>=target:
            print(f"r={orbit} required_prime_count={i} upper_with_{i-1}={upper} ({float(upper):.12f})",flush=True)
            break
