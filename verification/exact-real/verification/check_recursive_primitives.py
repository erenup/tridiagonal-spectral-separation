#!/usr/bin/env python3
'Exact finite checks of polynomial and interval primitives.\n\nThe characteristic-polynomial checks are supplementary identities.\nThe all-input construction and operation count are in ../proofs/PROOF.md.\n'
import argparse
from fractions import Fraction as F
from itertools import product,permutations
from copy import deepcopy


def need(ok,message):
    if not ok:raise SystemExit('FAIL: '+message)


def trim(p):
    p=list(p)
    while len(p)>1 and not p[-1]:p.pop()
    return p


def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return trim(c)


def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)


def evaluate(a,x):
    v=F(0)
    for c in reversed(a):v=v*x+c
    return v


def roots_polynomial(roots):
    p=[F(1)]
    for r in roots:p=mul(p,[r,F(1)])
    return p


def graeffe(p,corrupt=False):
    even=[c*(-1)**i for i,c in enumerate(p[::2])]
    odd=[c*(-1)**i for i,c in enumerate(p[1::2])]
    out=add(mul(even,even),[F(0)]+mul(odd,odd))
    if corrupt:out[0]+=1
    return out


def check_graeffe(corrupt=False):
    roots=[F(1),F(7,6),F(3,2),F(2),F(11,4)]
    p=roots_polynomial(roots);R=1
    for step in range(4):
        p=graeffe(p,corrupt and step==0);roots=[x*x for x in roots];R*=2
        need(p==roots_polynomial(roots),'Graeffe positive-root squaring identity')
        ordered=sorted(roots,reverse=True);n=len(roots)
        for j in range(1,n+1):
            ratio=p[n-j]/p[n-j+1]
            need(ordered[j-1]/(2**n)<=ratio<=ordered[j-1]*2**n,'adjacent coefficient-ratio bounds')


def below(A,B,t,weak):
    answer=0;j=0
    for a in A:
        while j<len(B) and (B[j]<=a+t if weak else B[j]<a+t):j+=1
        answer+=j
    return answer


def count(A,B,l,u):return below(A,B,u,False)-below(A,B,l,True)


def choose(A,B,l,u):
    N=len(A)*len(B);R=1
    while R<=N:
        mid=(l+u)/2
        if count(A,B,l,mid)<=count(A,B,mid,u):u=mid
        else:l=mid
        R*=2
    return (l+u)/2,(u-l)/2


def check_shifts(corrupt=False):
    cases=[([F(-2),F(0),F(3)],[F(-1),F(0),F(2),F(5)]),
           ([F(0)]*4,[F(0)]*3),
           ([F(-5,7),F(1,9),F(4,3)],[F(-1,7),F(2,9)])]
    for A,B in cases:
        for l,u in ((F(-1),F(1)),(F(0),F(1)),(F(-3,4),F(5,6))):
            need(count(A,B,l,u)==sum(l<b-a<u for a in A for b in B),'strict open difference count')
            t,margin=choose(A,B,l,u)
            if corrupt:t=B[0]-A[0]
            need(l<=t<=u,'shift interval membership')
            need(all(abs(a+t-b)>=margin for a in A for b in B),'empty interval midpoint margin')
            need(margin>=(u-l)/(4*(len(A)*len(B)+1)),'uniform difference-avoidance bound')


def mm(A,B):
    return [[add(mul(A[i][0],B[0][j]),mul(A[i][1],B[1][j])) for j in range(2)] for i in range(2)]


def tree(diag,couplings,l,r):
    if r-l==1:
        c=F(0) if l==0 else couplings[l-1]**2
        return dict(l=l,r=r,M=[[[-diag[l],F(1)],[-c]],[[F(1)],[F(0)]]])
    m=(l+r)//2;left=tree(diag,couplings,l,m);right=tree(diag,couplings,m,r)
    return dict(l=l,r=r,M=mm(right['M'],left['M']),left=left,right=right)


def cover(node,i):
    if node['l']>=i:return []
    if node['r']<=i:return [node]
    return cover(node['left'],i)+cover(node['right'],i)


def check_prefix(corrupt=False):
    a=[F(1,3),F(-2,5),F(4,7),F(0),F(1,9),F(-1,8),F(3,4)]
    b=[F(1,4),F(2,9),F(1,5),F(3,8),F(2,7),F(1,3)]
    root=tree(a,b,0,len(a))
    for i in range(len(a)+1):
        z=F(2*i-3,11)
        direct0,direct1=F(0),F(1)
        for j in range(i):direct0,direct1=direct1,(z-a[j])*direct1-(b[j-1]**2 if j else 0)*direct0
        vector=[F(1),F(0)]
        nodes=cover(root,i)
        if corrupt and i==3:nodes=nodes[:-1]
        for node in nodes:
            A=[[evaluate(p,z) for p in row] for row in node['M']]
            vector=[sum(A[j][k]*vector[k] for k in range(2)) for j in range(2)]
        need(vector[0]==direct1,'offline prefix transfer-product query')


# Sparse multivariate polynomials in z,h,eta,tau, with rational coefficients.
def padd(a,b):
    out=dict(a)
    for k,v in b.items():out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}


def pscale(a,c):return {k:v*c for k,v in a.items() if v*c}


def pmul(a,b):
    out={}
    for x,c in a.items():
        for y,d in b.items():
            z=tuple(i+j for i,j in zip(x,y));out[z]=out.get(z,F(0))+c*d
    return {k:v for k,v in out.items() if v}


def pdet(A):
    out={};n=len(A)
    for q in permutations(range(n)):
        sign=(-1)**sum(q[i]>q[j] for i in range(n) for j in range(i+1,n))
        term={(0,0,0,0):F(sign)}
        for i in range(n):term=pmul(term,A[i][q[i]])
        out=padd(out,term)
    return out


def check_merge(corrupt=False):
    zero={};one={(0,0,0,0):F(1)}
    z={(1,0,0,0):F(1)};h={(0,1,0,0):F(1)}
    eta={(0,0,1,0):F(1)};tau={(0,0,0,1):F(1)}
    A=[[padd(z,pscale(h,-1)),pscale(one,F(-1,2)),zero],
       [pscale(one,F(-1,2)),z,pscale(eta,F(-1,2))],
       [zero,pscale(eta,F(-1,2)),z]]
    actual=pdet(A)
    expected={(3,0,0,0):F(1),(2,1,0,0):F(-1),(1,0,0,0):F(-1,4),
              (1,0,2,0):F(-1,4),(0,1,2,0):F(1,4)}
    if corrupt:expected[(1,0,0,0)]=F(-1,3)
    need(actual==expected,'normalized leading3 characteristic identity')
    substituted={}
    for (ez,eh,ee,et),c in actual.items():
        key=(0,eh+ez,ee+2*ez,et);substituted[key]=substituted.get(key,F(0))+c
    substituted={k:v for k,v in substituted.items() if v}
    need(substituted=={(0,3,6,0):F(1),(0,3,4,0):F(-1),(0,1,4,0):F(-1,4)},'IVT endpoint sign factorization')
    child=[[z,pscale(eta,F(-1,2)),zero],
           [pscale(eta,F(-1,2)),z,pscale(tau,F(-1,2))],
           [zero,pscale(tau,F(-1,2)),z]]
    need(pdet(child)=={(3,0,0,0):F(1),(1,0,2,0):F(-1,4),(1,0,0,2):F(-1,4)},'child characteristic identity')
    for delta in (F(1,4),F(1,16),F(1,100)):
        for eta0 in (F(1,4),F(1,8),F(1,32)):
            tau0=delta*eta0**4
            need(0<tau0<=eta0,'positive irreducible small edge')
            need(max(F(1,2),F(1,2)+eta0/2,eta0/2+tau0/2,tau0/2)<=F(5,8),'normalized row-sum bound')
            need(2*delta*eta0**2+tau0<=3*delta*eta0**2,'universal gap upper-bound constant')


def reject(call,name):
    try:call()
    except SystemExit:return
    raise SystemExit('FAIL: negative control accepted: '+name)


def main():
    check_graeffe();check_shifts();check_prefix();check_merge()
    reject(lambda:check_graeffe(True),'wrong Graeffe coefficient')
    reject(lambda:check_shifts(True),'resonant returned shift')
    reject(lambda:check_prefix(True),'missing transfer node')
    reject(lambda:check_merge(True),'wrong characteristic coefficient')
    print('PASS: exact Graeffe identities and coefficient-ratio bounds')
    print('PASS: difference counts, empty-interval shifts, prefix queries')
    print('PASS: normalized irreducible merge identities and universal constants')
    print('PASS: 4 negative controls rejected')




def negative_control(name):
    if name == 'graeffe-coefficient':
        check_graeffe(True)
    elif name == 'resonant-shift':
        check_shifts(True)
    elif name == 'missing-prefix-node':
        check_prefix(True)
    elif name == 'characteristic-coefficient':
        check_merge(True)
    else:
        raise SystemExit('FAIL: unknown negative control')
    raise SystemExit('FAIL: negative control unexpectedly passed')


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=['graeffe-coefficient', 'resonant-shift', 'missing-prefix-node', 'characteristic-coefficient'])
    args = parser.parse_args()
    if args.negative_control is not None:
        negative_control(args.negative_control)
    else:
        main()


if __name__ == '__main__':
    cli()
