# Supermodular ordering of speeded-up Markov chains without stochastic monotonicity

Yitzchak Shmalo

For a stationary continuous-time Markov chain with real values, let the chain run at speed c. Leskelä (Queueing Systems 100 (2022), 213-215, Problem 3) asked whether some stationary ergodic chain that is not stochastically monotone becomes smaller in the supermodular order of processes as it is speeded up. The paper shows that such chains exist on three states. A chain that leaves its smallest value for either of the other two values at any positive rates and returns from both at a common rate has this property and is not stochastically monotone. If the largest value returns faster than the middle one, the property fails already for pairs of sampling times. For reversible three-state chains with two distinct nonzero eigenvalues the pairs are ordered exactly when the slow left eigenvector does not have the same strict sign at the two extreme states.

## Contents

- `paper/main.tex`, `paper/main.pdf`: the paper.
- `code/checks.py`: the computer checks of Section 7 (exact certificate identities, SymPy spectral formulas, a 40-digit evaluation of the counterexample, and floating-point linear programs over supermodular functions). Its output is `code/checks_output.txt`; the script exits with a nonzero code if any check fails.
- `code/StarCertificates.lean`: Lean 4 / Mathlib proofs of the four identities of Lemma 4.2 and of the inequality S_p(ψ) ≥ 0. The compiler output is `code/lean_output.txt`.

## Running the checks

```
python code/checks.py
```

Requires Python 3 with NumPy, SciPy, SymPy and mpmath; it runs in about ten seconds.
