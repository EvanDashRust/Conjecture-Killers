"""Sharp finite approximations to head survival in the two no-7 phase orbits."""
from fractions import Fraction as Q
from itertools import product


def towers(orbit,depth):
    assert orbit in (1,2) and depth>=2
    A={1:0,2:orbit}|{i:5+3**(i-1) for i in range(3,depth+1)}
    C={1:0}|{i:2+5**(i-1) for i in range(2,depth+1)}
    E={1:1}|{i:3+5**(i-1) for i in range(2,depth+1)}
    B={}
    for b in E:
        if orbit==2:
            values={1:1,2:8}|{i:5+2*3**(i-1) for i in range(3,depth+1)}
        elif b==1:
            values={1:1,2:2}|{i:8+3**(i-1) for i in range(3,depth+1)}
        else:
            values={1:2,2:4}|{i:7+3**(i-1) for i in range(3,depth+1)}
        for a,r in values.items():
            B[a,b]=r
    return A,C,E,B


def check(orbit,depth):
    A,C,E,B=towers(orbit,depth)
    assert A[2]==orbit and (B[1,1],E[1])==(1,1)
    # Direct finite CRT grid; both coordinates determine every class.
    uncovered=0
    for x in range(3**depth):
        if any(x%3**a==r for a,r in A.items()):continue
        for y in range(5**depth):
            if any(y%5**b==r for b,r in C.items()):continue
            if not any(x%3**a==r and y%5**b==E[b] for (a,b),r in B.items()):
                uncovered+=1
    s=sum(Q(1,3**i) for i in A)
    t=sum(Q(1,5**i) for i in C)
    overlap=Q(0) if orbit==2 else Q(1,45)+(s-Q(4,9))*(t-Q(1,5))
    exact=(1-s)*(1-t)-s*t+overlap
    assert exact==Q(uncovered,15**depth)
    return exact


if __name__=="__main__":
    for orbit in (1,2):
        for depth in (2,3,4):
            print("orbit",orbit,"depth",depth,"uncovered",check(orbit,depth))
