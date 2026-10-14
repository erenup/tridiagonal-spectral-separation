#!/usr/bin/env python3
'Exact finite checks of the convex interval selector.\n\nAll arithmetic uses integers and Fraction. Bounded signed value errors\nare included. The all-input argument is in ../proofs/PROOF.md.\n'
import argparse
from fractions import Fraction as Q
import random


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


class ConvexPL:
    def __init__(self, slope, hinges, constant=Q(0)):
        self.slope = Q(slope)
        self.hinges = tuple((Q(z), Q(w)) for z, w in hinges)
        self.constant = Q(constant)
        require(all(w >= 0 for _, w in self.hinges), "nonconvex hinge")

    def __call__(self, x):
        return self.constant + self.slope * x + sum(
            (w * max(Q(0), x - z) for z, w in self.hinges), Q(0)
        )

    def direct_secant(self, u, v):
        # Integrate the independently specified step-function derivative.
        require(u < v, "secant order")
        return self.slope + sum(
            (w * max(Q(0), v - max(u, z)) / (v-u)
             for z, w in self.hinges), Q(0)
        )


def potential(f, interval):
    a, b = interval
    q = (b-a)/4
    require(q > 0, "interval length")
    return (f(b)-f(b-q)-f(a+q)+f(a))/q


def independent_potential(f, interval):
    a, b = interval
    q = (b-a)/4
    return f.direct_secant(b-q, b)-f.direct_secant(a, a+q)


def children(interval):
    a, b = interval
    q = (b-a)/4
    return (a+q, a+2*q), (a+2*q, a+3*q)


def second_difference(f, interval, radius_factor=Q(1, 4)):
    a, b = interval
    c, r = (a+b)/2, (b-a)*radius_factor
    return (f(c+r)+f(c-r)-2*f(c))/r


class BiasedOracle:
    def __init__(self, f, phase):
        self.f = f
        self.phase = phase
        self.calls = 0

    def value(self, x, error):
        pattern = (Q(1), Q(-1), Q(1,2), Q(-1,2), Q(0))
        bias = pattern[(self.calls+self.phase) % len(pattern)]
        self.calls += 1
        result = self.f(x) + error*bias
        require(abs(result-self.f(x)) <= error, "oracle error promise")
        return result


def approximate_potential(oracle, interval):
    a, b = interval
    ell = b-a
    q, error = ell/4, ell/1024
    return (oracle.value(b, error)-oracle.value(b-q, error)
            -oracle.value(a+q, error)+oracle.value(a, error))/q


def check_choice(f, interval, chosen):
    require(potential(f, chosen) <= potential(f, interval)/2+Q(1,32),
            "robust half-variation choice")


def check_local(f, interval):
    p = potential(f, interval)
    require(p == independent_potential(f, interval),
            "secants versus integrated derivative")
    require(p >= 0, "nonnegative potential")
    left, right = children(interval)
    require(potential(f, left)+potential(f, right) <= p,
            "children potential sum")
    curvature = second_difference(f, interval)
    require(0 <= curvature <= p, "centered curvature control")


def select(f, n, delta, phase):
    initial = (Q(0), delta/n)
    interval = initial
    oracle = BiasedOracle(f, phase)
    k, power = 0, 1
    while power < 16*n**3:
        power *= 2
        k += 1
    require(power < 32*n**3, "minimal dyadic depth")
    p0 = potential(f, initial)
    require(p0 <= n**3, "initial potential bound")
    for j in range(k):
        check_local(f, interval)
        left, right = children(interval)
        pl = approximate_potential(oracle, left)
        pr = approximate_potential(oracle, right)
        require(abs(pl-potential(f, left)) <= Q(1,64),
                "left potential accuracy")
        require(abs(pr-potential(f, right)) <= Q(1,64),
                "right potential accuracy")
        chosen = left if pl <= pr else right
        check_choice(f, interval, chosen)
        interval = chosen
        bound = p0 / 2**(j+1)+Q(1,16)*(1-Q(1,2**(j+1)))
        require(potential(f, interval) <= bound, "iterated recurrence")
    check_local(f, interval)
    require(potential(f, interval) < Q(1,8), "final potential")
    a, b = interval
    c, r = (a+b)/2, (b-a)/4
    require(r > delta/(4096*n**7), "polynomial radius")
    require(0 <= c-r < c+r <= delta/n, "parameter containment")
    require(second_difference(f, interval) < Q(1,8),
            "final second difference")
    return oracle.calls


def expect_reject(action, name):
    try:
        action()
    except SystemExit:
        return
    raise SystemExit("FAIL: negative control accepted: " + name)


def main():
    rng = random.Random(20261012)
    total_cases = total_calls = 0
    for n in (2, 3, 5, 8, 13):
        delta = Q(1,3)
        length = delta/n
        for case in range(18):
            if case < 9:
                knots = [(length*Q(case,8), Q(n**3,2))]
            else:
                knots = [(length*Q(rng.randrange(-20,121),100),
                          Q(n**3*rng.randrange(1,10),500))
                         for _ in range(25)]
            f = ConvexPL(Q(n*(n+1),2), knots, Q(-7,3))
            total_calls += select(f, n, delta, case)
            total_cases += 1

    interval = (Q(0), Q(1))
    f = ConvexPL(0, [(Q(5,16), Q(1))])
    left, right = children(interval)
    require(potential(f, left) == 1 and potential(f, right) == 0,
            "wrong-child fixture")
    expect_reject(lambda: check_choice(f, interval, left), "wrong child")

    def bad_oracle():
        error = Q(1,1024)
        true = f(Q(1,2))
        reported = true + 2*error
        require(abs(reported-true) <= error, "oracle error promise")

    expect_reject(bad_oracle, "false oracle accuracy")
    outside = ConvexPL(0, [(Q(5,4), Q(1))])
    expect_reject(lambda: require(
        second_difference(outside, interval, Q(1)) <= potential(outside, interval),
        "centered curvature control"), "radius outside guarded core")
    expect_reject(lambda: ConvexPL(0, [(Q(1,2), Q(-1))]), "nonconvex input")

    # Exact constant conversion used by the quarter-power jump lemma.
    require(10**12 < 2**40, "gap constant conversion")
    require(4096**4 == 2**48, "radius fourth-power constant")
    require(4*7+14 == 42, "uniform gap exponent")
    print("PASS: %d convex rational functions; %d bounded-error value calls" %
          (total_cases, total_calls))
    print("PASS: secant inequalities, robust choices, recurrence, radius, curvature")
    print("PASS: 4 negative controls rejected; exact final exponent constants")




def negative_control(name):
    interval = (Q(0), Q(1))
    f = ConvexPL(0, [(Q(5, 16), Q(1))])
    if name == 'wrong-child':
        left, right = children(interval)
        check_choice(f, interval, left)
    elif name == 'oracle-accuracy':
        error = Q(1, 1024)
        true = f(Q(1, 2))
        reported = true + 2*error
        require(abs(reported-true) <= error, 'oracle error promise')
    elif name == 'unguarded-radius':
        outside = ConvexPL(0, [(Q(5, 4), Q(1))])
        require(second_difference(outside, interval, Q(1)) <= potential(outside, interval),
                'centered curvature control')
    elif name == 'nonconvex-hinge':
        ConvexPL(0, [(Q(1, 2), Q(-1))])
    else:
        raise SystemExit('FAIL: unknown negative control')
    raise SystemExit('FAIL: negative control unexpectedly passed')


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=['wrong-child', 'oracle-accuracy', 'unguarded-radius', 'nonconvex-hinge'])
    args = parser.parse_args()
    if args.negative_control is not None:
        negative_control(args.negative_control)
    else:
        main()


if __name__ == '__main__':
    cli()
