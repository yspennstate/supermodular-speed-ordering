"""Computer checks for "A non-monotone Markov chain whose speeded-up versions decrease in the supermodular order".

Sections (numbers as in Section 7 of the paper):
  A  exact: the certificate identities of Lemma 4.2 for S and T_0..T_3, in integer arithmetic
  B  exact: the spectral reduction of Lemma 3.1 for the star with equal return rates (sympy)
  C  high precision: the violation of Theorem 1.2 at a2 = a3 = 1, b2 = 1, b3 = 2 (mpmath, 40 digits)
  D  floating point: the finite-grid LP test of (1.1) at n = 3, 4 for stars and controls (scipy HiGHS)
  E  floating point: reversible three-state chains, the sign criterion of Proposition 6.1 against the LP test
Run: python checks.py   (prints PASS/FAIL per check and a summary; exit code 1 if any check fails)
"""
import itertools
import sys
from fractions import Fraction

import numpy as np
import sympy as sp
import mpmath as mp
from scipy.linalg import expm
from scipy.optimize import linprog

FAILS = []


def report(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""), flush=True)
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- A: certificates
# An expression is a dict {point in {1,2,3}^4: integer coefficient}, standing for sum coef * psi(point).

def add(e, pt, c):
    e[pt] = e.get(pt, 0) + c
    if e[pt] == 0:
        del e[pt]


def elem(x, i, j):
    """E[x; i, j] = psi(x+e_i+e_j) - psi(x+e_i) - psi(x+e_j) + psi(x), coordinates 1-based."""
    assert i != j
    x = list(x)
    xi = x.copy(); xi[i - 1] += 1
    xj = x.copy(); xj[j - 1] += 1
    xij = x.copy(); xij[i - 1] += 1; xij[j - 1] += 1
    for p in (x, xi, xj, xij):
        assert all(1 <= v <= 3 for v in p), (x, i, j)
    e = {}
    add(e, tuple(xij), 1); add(e, tuple(x), 1); add(e, tuple(xi), -1); add(e, tuple(xj), -1)
    return e


def combo(terms):
    e = {}
    for c, x, i, j in terms:
        for p, v in elem(x, i, j).items():
            add(e, p, c * v)
    return e


def bracket(l, c, cp):
    """psi(l,l,l,l) - psi(l,l,1,c') - psi(1,c,l,l) + psi(1,c,1,c')"""
    e = {}
    add(e, (l, l, l, l), 1); add(e, (l, l, 1, cp), -1); add(e, (1, c, l, l), -1); add(e, (1, c, 1, cp), 1)
    return e


def S_expr():
    e = {}
    for l, c, cp in itertools.product((2, 3), repeat=3):
        for p, v in bracket(l, c, cp).items():
            add(e, p, v)
    return e


def T_expr(k):
    e = {}
    for l, c, cp in itertools.product((2, 3), repeat=3):
        if (l, c, cp).count(2) == k:
            for p, v in bracket(l, c, cp).items():
                add(e, p, v)
    return e


CERT_S = [(2, (1, 2, 1, 2), 1, 3), (2, (1, 2, 1, 3), 1, 3), (2, (1, 2, 2, 3), 1, 3),
          (2, (1, 3, 1, 2), 1, 3), (2, (1, 3, 1, 3), 1, 3), (2, (1, 3, 2, 3), 1, 3),
          (2, (2, 2, 2, 2), 2, 4), (2, (2, 2, 2, 3), 2, 3),
          (2, (2, 3, 1, 2), 1, 4), (4, (2, 3, 1, 3), 1, 3), (4, (2, 3, 2, 3), 1, 3)]
CERT_T = {
    3: [(1, (1, 2, 1, 2), 1, 3)],
    0: [(1, (1, 3, 1, 3), 1, 3), (1, (1, 3, 2, 3), 1, 3), (1, (2, 3, 1, 3), 1, 3), (1, (2, 3, 2, 3), 1, 3)],
    2: [(1, (1, 2, 1, 2), 1, 3), (1, (1, 2, 1, 3), 1, 3), (1, (1, 2, 2, 3), 1, 3), (1, (1, 3, 1, 2), 1, 3),
        (1, (2, 2, 2, 2), 2, 4), (1, (2, 2, 2, 3), 2, 3), (1, (2, 3, 1, 2), 1, 4), (1, (2, 3, 1, 3), 1, 3),
        (1, (2, 3, 2, 3), 1, 3)],
    1: [(1, (1, 2, 1, 3), 1, 3), (1, (1, 2, 2, 3), 1, 3), (1, (1, 3, 1, 2), 1, 3), (1, (1, 3, 1, 3), 1, 3),
        (1, (1, 3, 2, 3), 1, 3), (1, (2, 2, 2, 2), 2, 4), (1, (2, 2, 2, 3), 1, 3), (1, (2, 3, 1, 2), 1, 3),
        (1, (2, 3, 1, 3), 1, 3), (1, (2, 3, 2, 2), 1, 4), (1, (2, 3, 2, 3), 1, 3), (1, (3, 2, 2, 3), 2, 3)],
}


def section_A():
    S = S_expr()
    report("A1 S equals its certificate (Lemma 4.2, p = 1/2)", S == combo(CERT_S),
           f"{len(S)} point evaluations, {sum(c for c, *_ in CERT_S)} elementary differences counted with weight")
    for k in (3, 2, 1, 0):
        report(f"A2 T_{k} equals its certificate (Lemma 4.2)", T_expr(k) == combo(CERT_T[k]),
               f"{len(CERT_T[k])} elementary differences")
    tot = {}
    for k in range(4):
        for p, v in T_expr(k).items():
            add(tot, p, v)
    report("A3 T_0 + T_1 + T_2 + T_3 = S (that is, 8 S_{1/2} = S)", tot == S)
    # the certificates are not unique; record that S is not a sum of the eight brackets with signed terms
    report("A4 every certificate coefficient is a positive integer",
           all(c > 0 for c, *_ in CERT_S) and all(c > 0 for v in CERT_T.values() for c, *_ in v))


# ---------------------------------------------------------------- B: spectral reduction (sympy)

def section_B():
    a2, a3, b, g = sp.symbols("a2 a3 b g", positive=True)
    s = a2 + a3
    Q = sp.Matrix([[-s, a2, a3], [b, -b, 0], [b, 0, -b]])
    pi = sp.Matrix([[b, a2, a3]]) / (b + s)
    report("B1 pi Q = 0 and pi sums to 1", sp.simplify(pi * Q) == sp.zeros(1, 3) and sp.simplify(sum(pi)) == 1)
    D = sp.diag(*pi)
    report("B2 detailed balance: diag(pi) Q symmetric", sp.simplify(D * Q - (D * Q).T) == sp.zeros(3, 3))
    v0 = sp.Matrix([1, 1, 1]); v1 = sp.Matrix([0, a3, -a2]); v2 = sp.Matrix([-s / b, 1, 1])
    mu = [0, b, s + b]
    ok = all(sp.simplify(Q * v - (-m) * v) == sp.zeros(3, 1) for v, m in zip((v0, v1, v2), mu))
    report("B3 right eigenvectors v0, v1, v2 with eigenvalues 0, -b, -(a2+a3+b)", ok)
    ip = lambda u, w: sp.simplify(sum(pi[i] * u[i] * w[i] for i in range(3)))
    report("B4 v0, v1, v2 orthogonal in L^2(pi)", ip(v0, v1) == 0 and ip(v0, v2) == 0 and ip(v1, v2) == 0)
    # P_g = sum_l e^{-mu_l g} v_l (pi v_l)^T / <v_l, v_l>; check P_0 = I and P_0' = Q
    terms = [(v, m) for v, m in zip((v0, v1, v2), mu)]
    P = sp.zeros(3, 3)
    for v, m in terms:
        P += sp.exp(-m * g) * v * sp.Matrix([[pi[j] * v[j] for j in range(3)]]) / ip(v, v)
    report("B5 spectral form: P_0 = I and dP/dg at 0 = Q",
           sp.simplify(P.subs(g, 0) - sp.eye(3)) == sp.zeros(3, 3)
           and sp.simplify(sp.diff(P, g).subs(g, 0) - Q) == sp.zeros(3, 3))
    Phi = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"F{i+1}{j+1}"))
    F = sp.expand(sum(pi[x] * P[x, y] * Phi[x, y] for x in range(3) for y in range(3)))
    # the coefficient of e^{-b g}: rebuild F with the two decaying exponentials as free symbols
    e1, e2 = sp.symbols("e1 e2")
    Pe = sp.zeros(3, 3)
    for v, E in zip((v0, v1, v2), (1, e1, e2)):
        Pe += E * v * sp.Matrix([[pi[j] * v[j] for j in range(3)]]) / ip(v, v)
    Fe = sp.expand(sum(pi[x] * Pe[x, y] * Phi[x, y] for x in range(3) for y in range(3)))
    alpha = Fe.coeff(e1)
    p, q = a2 / s, a3 / s
    alpha_claim = (pi[1] + pi[2]) * p * q * (Phi[1, 1] - Phi[1, 2] - Phi[2, 1] + Phi[2, 2])
    report("B6 alpha = (pi_2+pi_3) p q [Phi22 - Phi23 - Phi32 + Phi33]  (4.1)", sp.simplify(alpha - alpha_claim) == 0)
    minusF0 = sp.simplify(-sp.diff(F, g).subs(g, 0))
    claim = b * (pi[1] + pi[2]) * (Phi[0, 0] + p * Phi[1, 1] + q * Phi[2, 2] - p * (Phi[0, 1] + Phi[1, 0])
                                   - q * (Phi[0, 2] + Phi[2, 0]))
    report("B7 -F'(0) = b (pi_2+pi_3) [Phi11 + p Phi22 + q Phi33 - p(Phi12+Phi21) - q(Phi13+Phi31)]  (4.2)",
           sp.simplify(minusF0 - claim) == 0)
    edge = sum(pi[x] * Q[x, y] * (Phi[x, x] + Phi[y, y] - Phi[x, y] - Phi[y, x])
               for x in range(3) for y in range(x + 1, 3))
    report("B8 -F'(0) equals the edge sum of Lemma 3.1", sp.simplify(minusF0 - edge) == 0)


# ---------------------------------------------------------------- C: Theorem 1.2 numerically

def section_C():
    mp.mp.dps = 40
    a2 = a3 = mp.mpf(1); b2 = mp.mpf(1); b3 = mp.mpf(2)
    Q = mp.matrix([[-(a2 + a3), a2, a3], [b2, -b2, 0], [b3, 0, -b3]])
    w = [1, a2 / b2, a3 / b3]; Z = sum(w); pi = [x / Z for x in w]
    G = lambda t: pi[0] * (1 - mp.expm(Q * t)[0, 2])     # P(X_0 <= 1, X_t <= 2)
    s1, s2 = mp.mpf(2), mp.mpf(6)
    g1, g2 = G(s1), G(s2)
    report("C1 b3 > b2 violates (1.1) at n = 2: P(X_0<=1, X_2<=2) < P(X_0<=1, X_6<=2)", g1 < g2,
           f"{mp.nstr(g1, 12)} < {mp.nstr(g2, 12)}")
    # the slow eigenvalue lies strictly between b2 and b3
    S = mp.matrix(3, 3)
    for i in range(3):
        for j in range(3):
            S[i, j] = -mp.sqrt(pi[i]) * Q[i, j] / mp.sqrt(pi[j])
    ev = sorted(mp.eigsy(S)[0])
    report("C2 0 < b2 < mu_1 < b3 < mu_2 (interlacing, strict)", b2 < ev[1] < b3 < ev[2] and abs(ev[0]) < 1e-30,
           f"mu_1 = {mp.nstr(ev[1], 12)}, mu_2 = {mp.nstr(ev[2], 12)}")
    # the mirrored chain (b2 > b3) has P(X_0<=1, X_t<=2) nonincreasing on a grid
    Qm = mp.matrix([[-(a2 + a3), a2, a3], [b3, -b3, 0], [b2, 0, -b2]])
    wm = [1, a2 / b3, a3 / b2]; Zm = sum(wm); pim = [x / Zm for x in wm]
    vals = [pim[0] * (1 - mp.expm(Qm * (mp.mpf(k) / 10))[0, 2]) for k in range(0, 101)]
    report("C3 with b2 > b3 (rates swapped) the same quantity is nonincreasing on t = 0, 0.1, ..., 10",
           all(vals[k + 1] <= vals[k] + mp.mpf(10) ** -35 for k in range(100)))


# ---------------------------------------------------------------- D, E: LP tests (floating point)

def stationary(Q):
    w, v = np.linalg.eig(Q.T)
    k = np.argmin(abs(w)); p = np.real(v[:, k]); return p / p.sum()


def fdd(Q, gaps):
    pi = stationary(Q); n = len(gaps) + 1
    P = [expm(Q * gp) for gp in gaps]
    law = np.zeros([3] * n)
    for x in itertools.product(range(3), repeat=n):
        pr = pi[x[0]]
        for k in range(n - 1):
            pr *= P[k][x[k], x[k + 1]]
        law[x] = pr
    return law


_A = {}


def constraints(n):
    if n not in _A:
        pts = list(itertools.product(range(3), repeat=n)); idx = {x: i for i, x in enumerate(pts)}
        rows = []
        for x in pts:
            for i in range(n):
                for j in range(i + 1, n):
                    if x[i] < 2 and x[j] < 2:
                        r = np.zeros(len(pts))
                        xi = list(x); xi[i] += 1; xj = list(x); xj[j] += 1; xij = list(xi); xij[j] += 1
                        r[idx[tuple(xij)]] -= 1; r[idx[x]] -= 1; r[idx[tuple(xi)]] += 1; r[idx[tuple(xj)]] += 1
                        rows.append(r)
        _A[n] = (pts, np.array(rows))
    return _A[n]


def sm_gap(law_fast, law_slow):
    """max over supermodular phi with |phi| <= 1 of E_fast phi - E_slow phi; (1.1) needs this <= 0."""
    n = law_fast.ndim; pts, A = constraints(n)
    c = np.array([law_slow[x] - law_fast[x] for x in pts])
    res = linprog(c, A_ub=A, b_ub=np.zeros(len(A)), bounds=[(-1, 1)] * len(pts), method="highs")
    assert res.status == 0, res.message
    return -res.fun


LAYOUTS = {3: [(1.0, 1.0), (0.3, 0.7)], 4: [(1.0, 0.5, 1.5), (0.5, 0.5, 0.5)]}
SPEEDS = [0.25, 0.5, 1.0, 2.0, 4.0]


def worst_gap(Q, ns=(3, 4)):
    worst = -np.inf
    for n in ns:
        for lay in LAYOUTS[n]:
            for c1, c2 in zip(SPEEDS[:-1], SPEEDS[1:]):
                # speed c: gaps c*g. c1 < c2: the c1 process is the "slow" one and must dominate.
                worst = max(worst, sm_gap(fdd(Q, [c2 * gp for gp in lay]), fdd(Q, [c1 * gp for gp in lay])))
    return worst


def star(a2, a3, b2, b3):
    return np.array([[-(a2 + a3), a2, a3], [b2, -b2, 0.0], [b3, 0.0, -b3]])


TOL = 1e-9


def section_D():
    for prm in [(1, 1, 1, 1), (1, 1, 3, 3), (3, 3, 1, 1), (1, 4, 2, 2), (5, 1, 1, 1), (0.2, 3, 0.7, 0.7)]:
        w = worst_gap(star(*map(float, prm)))
        report(f"D1 star a2,a3,b2,b3 = {prm} (equal return rates): LP gap <= {TOL:g}", w <= TOL, f"max {w:+.2e}")
    for prm in [(1, 1, 2, 1), (1, 1, 4, 1), (1, 3, 1.5, 1), (3, 1, 3, 1)]:
        w = worst_gap(star(*map(float, prm)))
        report(f"D2 star {prm} (b2 > b3, Conjecture 1.4): LP gap <= {TOL:g}", w <= TOL, f"max {w:+.2e}")
    for prm in [(1, 1, 1, 2), (1, 1, 1, 4)]:
        w = worst_gap(star(*map(float, prm)))
        report(f"D3 star {prm} (b3 > b2, Theorem 1.2): LP gap > 0", w > 1e-4, f"max {w:+.2e}")
    cyc = np.array([[-1.0, 1, 0], [0, -1, 1], [1, 0, -1]])
    w = worst_gap(cyc)
    report("D4 control: the cyclic chain 1->2->3->1 fails", w > 1e-4, f"max {w:+.2e}")
    bd = np.array([[-1.0, 1, 0], [2, -3, 1], [0, 2, -2]])
    w = worst_gap(bd)
    report("D5 control: a monotone birth-death chain passes", w <= TOL, f"max {w:+.2e}")


def reversible(rng):
    # random conductances c_xy and stationary weights pi: q(x,y) = c_xy / pi_x
    pi = rng.uniform(0.2, 1.0, 3); pi /= pi.sum()
    c = rng.uniform(0.05, 1.0, 3)          # edges 12, 13, 23
    C = np.array([[0, c[0], c[1]], [c[0], 0, c[2]], [c[1], c[2], 0]])
    Q = C / pi[:, None]
    np.fill_diagonal(Q, -Q.sum(1))
    return Q, pi


def slow_left(Q, pi):
    S = np.sqrt(pi)[:, None] * Q / np.sqrt(pi)[None, :]
    w, V = np.linalg.eigh((S + S.T) / 2)
    order = np.argsort(-w)                 # 0, -mu_1, -mu_2
    u = V[:, order[1]]
    return np.sqrt(pi) * u, -w[order[1]], -w[order[2]]   # l_1 = pi v_1 with v_1 = u / sqrt(pi)


def monotone(Q):
    # stochastically monotone iff sum_{z >= y} q(x, z) is nondecreasing in x for z-tails not containing x
    for y in (1, 2):
        for x in range(3):
            for xp in range(x + 1, 3):
                tx = Q[x, y:].sum(); txp = Q[xp, y:].sum()
                if (x < y and xp < y) or (x >= y and xp >= y):
                    if tx > txp + 1e-12:
                        return False
    return True


def section_E():
    rng = np.random.default_rng(20261015)
    agree = 0; nonmono_pass = 0; nonmono = 0; mism = []
    N = 60
    for t in range(N):
        Q, pi = reversible(rng)
        l1, m1, m2 = slow_left(Q, pi)
        sign_ok = l1[0] * l1[2] <= 0
        lp_ok = worst_gap(Q) <= TOL
        agree += (sign_ok == lp_ok)
        if not monotone(Q):
            nonmono += 1; nonmono_pass += lp_ok
        if sign_ok != lp_ok:
            mism.append((t, l1, m1, m2))
    report(f"E1 sign criterion l_1(1) l_1(3) <= 0 agrees with the LP test (n = 3, 4) on {N} random reversible chains",
           agree == N, f"{agree}/{N}; non-monotone {nonmono}, of which {nonmono_pass} pass")
    # repeated eigenvalue: the refresh chain Q = mu (1 pi - I) is monotone and passes
    pi = np.array([0.2, 0.5, 0.3]); Qr = 1.7 * (np.outer(np.ones(3), pi) - np.eye(3))
    report("E2 refresh chain (double eigenvalue) is stochastically monotone and passes the LP test",
           monotone(Qr) and worst_gap(Qr) <= TOL)


if __name__ == "__main__":
    section_A(); section_B(); section_C(); section_D(); section_E()
    print(f"\n{'ALL PASS' if not FAILS else 'FAILED: ' + ', '.join(FAILS)}")
    raise SystemExit(bool(FAILS))
