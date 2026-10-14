#!/usr/bin/env python3
"""Independent rational screens for the selector and polynomial definitions.
These finite tests supplement the universal Lean proofs; they are not premises.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
import json
import sys


def need(condition, message):
    if not condition:
        raise SystemExit(message)


def mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def roots_poly(roots):
    p = [Q(1)]
    for r in roots:
        p = mul(p, [Q(r), Q(1)])
    return p


def graeffe(p):
    even = [c * (-1)**j for j, c in enumerate(p[::2])]
    odd = [c * (-1)**j for j, c in enumerate(p[1::2])]
    a = mul(even, even)
    b = [Q(0)] + mul(odd, odd) if odd else [Q(0)]
    out = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] += x
    for i, x in enumerate(b): out[i] += x
    while len(out) > 1 and not out[-1]: out.pop()
    return out


def potential(f, a, b):
    width = b-a
    return (f(b)-f(b-width/4))/(width/4) - (f(a+width/4)-f(a))/(width/4)


def selector_case(n, delta, f, noise):
    a, b = Q(0), delta/n
    p0 = potential(f, a, b)
    need(0 <= p0 < n**3, 'initial potential')
    k = 0
    while 2**k < 16*n**3: k += 1
    need(2**k < 32*n**3 and all(2**j < 16*n**3 for j in range(k)), 'least doubling')
    calls = []
    for j in range(k):
        width = b-a
        children = [(a+width/4, a+width/2), (a+width/2, a+3*width/4)]
        true = [potential(f,*child) for child in children]
        need(sum(true) <= potential(f,a,b), 'children sum')
        estimates = []
        for side, (u,v) in enumerate(children):
            ell = v-u
            points = [u,u+ell/4,v-ell/4,v]
            errors = [Q(noise(j,side,q))*ell/1024 for q in range(4)]
            need(all(abs(e) <= ell/1024 for e in errors), 'reply contract')
            values = [f(x)+e for x,e in zip(points,errors)]
            estimate = 4*(values[3]-values[2]-values[1]+values[0])/ell
            need(abs(estimate-true[side]) <= Q(1,64), 'estimate accuracy')
            need(all(0 <= x <= delta/n for x in points), 'query containment')
            calls.extend(zip(points,[ell/1024]*4,values))
            estimates.append(estimate)
        chosen = 0 if estimates[0] <= estimates[1] else 1
        old = (a,b)
        a,b = children[chosen]
        need(old[0] <= a < b <= old[1], 'nested interval')
        need(b-a == delta/(n*4**(j+1)), 'interval length')
        need(potential(f,a,b) <= potential(f,*old)/2 + Q(1,32), 'one step')
        need(potential(f,a,b) <= Q(1,2**(j+1))*p0 + Q(1,16)*(1-Q(1,2**(j+1))), 'iterated bound')
    c,r = (a+b)/2,(b-a)/4
    need(len(calls)==8*k, 'transcript length')
    need(all(0<=x<=delta/n and tol>0 and abs(y-f(x))<=tol for x,tol,y in calls), 'transcript validity')
    need(r==delta/(4*n*4**k) and delta/(4096*n**7)<r<1, 'radius')
    need(potential(f,a,b)<Q(1,8) and f(c+r)+f(c-r)-2*f(c)<r/8, 'final defect')
    return {'n':n,'rounds':k,'calls':len(calls)}


def main(control=None):
    # Empty, repeated, zero and negative roots exercise the identity's full domain.
    samples=[[],[0],[-2],[3,2],[1,1,1],[Q(1,3),-2,0,4]]
    identities=0
    for roots in samples:
        p=roots_poly(roots)
        for k in range(5):
            need(p==roots_poly([r**(2**k) for r in roots]),'Graeffe iterate identity')
            p=graeffe(p);identities+=1
    bounded=0
    for roots in [[],[Q(1,3)],[3,2],[4,4,2,1],[Q(5,2),Q(3,2),Q(1,2)]]:
        n=len(roots)
        for k in range(4):
            powered=[r**(2**k) for r in roots]
            coeff=roots_poly(powered)
            for j in range(n+1):
                e=coeff[n-j]
                expansion=sum((product(powered[i] for i in s) for s in combinations(range(n),j)),Q(0))
                p=product(powered[:j])
                need(e==expansion and e>0,'coefficient expansion/positivity')
                need(p<=e<=comb(n,j)*p<=2**n*p,'ordered coefficient bounds')
                bounded+=1
            for i in range(n):
                ratio=coeff[n-i-1]/coeff[n-i]
                need(powered[i]/2**n<=ratio<=2**n*powered[i],'algebraic ratio')
    if control=='unordered':
        roots=[Q(1),Q(3)];e=roots_poly(roots)[1]
        need(e<=2*roots[0],'unordered roots violate upper bound')
    if control=='nonpositive':
        need(roots_poly([Q(-1)])[0]>0,'nonpositive root violates positivity')
    if control=='wrong_graeffe':
        need(graeffe(roots_poly([Q(3),Q(2)]))==[Q(36),Q(12),Q(1)],'corrupted transformed coefficient')
    noise_patterns=[lambda j,s,q:0,lambda j,s,q: (-1)**(j+s+q),lambda j,s,q: 1 if (q in (0,3)) != bool(s) else -1]
    if control=='bad_reply':noise_patterns=[lambda j,s,q:2]
    cases=[]
    for n,delta in [(2,Q(1,4)),(5,Q(2,5)),(9,Q(1,3))]:
        fns=[lambda x:Q(7)-2*x+3*x*x,lambda x:abs(x-Q(1,100))+x/3,lambda x:max(Q(0),2*x-Q(1,60),x-Q(1,120))]
        for f in fns:
            for noise in noise_patterns:cases.append(selector_case(n,delta,f,noise))
    need(control is None,'unknown or unexpectedly passing negative control')
    print(json.dumps({'status':'PASS','graeffe_identities':identities,'coefficient_cases':bounded,'selector_cases':len(cases),'selector_transcripts':cases},sort_keys=True))


def product(values):
    out=Q(1)
    for x in values:out*=x
    return out

if __name__=='__main__':
    if len(sys.argv)>2:raise SystemExit('usage: check_exact.py [negative-control]')
    main(sys.argv[1] if len(sys.argv)==2 else None)
