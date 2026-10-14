import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Rat

/-!
The finite inequality behind condition (C2) for the star chain.

`ψ : ℕ → ℕ → ℕ → ℕ → ℚ` is any function whose mixed second differences in every pair of coordinates
are nonnegative (hypotheses `h12` .. `h34`); only its values on `{1,2,3}^4` enter. A supermodular
function on `{1,2,3}^4` has this form after composing with the clamp `x ↦ min (max x 1) 3` in each
coordinate, which is monotone and preserves joins and meets.

* `S_identity`, `S_nonneg`: the sum `S(ψ)` over `l, c, c' ∈ {2,3}` of
  `ψ(l,l,l,l) - ψ(l,l,1,c') - ψ(1,c,l,l) + ψ(1,c,1,c')` equals the certificate of Lemma 4.2 at p = 1/2, hence `S(ψ) ≥ 0`.
* `T3_identity` .. `T0_identity`: the parts `T_k` of the sum with exactly `k` labels equal to 2 equal
  the certificates of Lemma 4.2.
* `Sp_nonneg`: for `p, q ≥ 0` the weighted sum `S_p(ψ)` with weights `w_2 = p`, `w_3 = q` is `≥ 0`.
-/

set_option linter.unusedVariables false

namespace StarCertificates

variable (ψ : ℕ → ℕ → ℕ → ℕ → ℚ)

/-- The mixed second difference `E[x; i, j]` is written out in place in each certificate. -/
theorem S_identity :
    (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) + (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 2 2 2 + ψ 1 2 1 3) + (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 3 2 2 + ψ 1 3 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 2 3 3 + ψ 1 2 1 2) + (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 2 3 3 + ψ 1 2 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 3 3 3 + ψ 1 3 1 2) + (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 3 3 3 + ψ 1 3 1 3) =
    2 * (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) + 2 * (ψ 2 2 2 3 - ψ 2 2 1 3 - ψ 1 2 2 3 + ψ 1 2 1 3) + 2 * (ψ 2 2 3 3 - ψ 2 2 2 3 - ψ 1 2 3 3 + ψ 1 2 2 3) + 2 * (ψ 2 3 2 2 - ψ 2 3 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + 2 * (ψ 2 3 2 3 - ψ 2 3 1 3 - ψ 1 3 2 3 + ψ 1 3 1 3) + 2 * (ψ 2 3 3 3 - ψ 2 3 2 3 - ψ 1 3 3 3 + ψ 1 3 2 3) + 2 * (ψ 2 3 2 3 - ψ 2 3 2 2 - ψ 2 2 2 3 + ψ 2 2 2 2) + 2 * (ψ 2 3 3 3 - ψ 2 3 2 3 - ψ 2 2 3 3 + ψ 2 2 2 3) + 2 * (ψ 3 3 1 3 - ψ 3 3 1 2 - ψ 2 3 1 3 + ψ 2 3 1 2) + 4 * (ψ 3 3 2 3 - ψ 3 3 1 3 - ψ 2 3 2 3 + ψ 2 3 1 3) + 4 * (ψ 3 3 3 3 - ψ 3 3 2 3 - ψ 2 3 3 3 + ψ 2 3 2 3) := by
  ring

theorem S_nonneg
    (h12 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) (b + 1) c d - ψ (a + 1) b c d - ψ a (b + 1) c d + ψ a b c d)
    (h13 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b (c + 1) d - ψ (a + 1) b c d - ψ a b (c + 1) d + ψ a b c d)
    (h14 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b c (d + 1) - ψ (a + 1) b c d - ψ a b c (d + 1) + ψ a b c d)
    (h23 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) (c + 1) d - ψ a (b + 1) c d - ψ a b (c + 1) d + ψ a b c d)
    (h24 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) c (d + 1) - ψ a (b + 1) c d - ψ a b c (d + 1) + ψ a b c d)
    (h34 : ∀ a b c d : ℕ, 0 ≤ ψ a b (c + 1) (d + 1) - ψ a b (c + 1) d - ψ a b c (d + 1) + ψ a b c d) :
    0 ≤ (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) + (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 2 2 2 + ψ 1 2 1 3) + (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 3 2 2 + ψ 1 3 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 2 3 3 + ψ 1 2 1 2) + (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 2 3 3 + ψ 1 2 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 3 3 3 + ψ 1 3 1 2) + (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 3 3 3 + ψ 1 3 1 3) := by
  have e0 := h13 1 2 1 2
  norm_num at e0
  have e1 := h13 1 2 1 3
  norm_num at e1
  have e2 := h13 1 2 2 3
  norm_num at e2
  have e3 := h13 1 3 1 2
  norm_num at e3
  have e4 := h13 1 3 1 3
  norm_num at e4
  have e5 := h13 1 3 2 3
  norm_num at e5
  have e6 := h24 2 2 2 2
  norm_num at e6
  have e7 := h23 2 2 2 3
  norm_num at e7
  have e8 := h14 2 3 1 2
  norm_num at e8
  have e9 := h13 2 3 1 3
  norm_num at e9
  have e10 := h13 2 3 2 3
  norm_num at e10
  linarith

theorem T3_identity :
    (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) =
    (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) := by
  ring

theorem T3_nonneg
    (h12 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) (b + 1) c d - ψ (a + 1) b c d - ψ a (b + 1) c d + ψ a b c d)
    (h13 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b (c + 1) d - ψ (a + 1) b c d - ψ a b (c + 1) d + ψ a b c d)
    (h14 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b c (d + 1) - ψ (a + 1) b c d - ψ a b c (d + 1) + ψ a b c d)
    (h23 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) (c + 1) d - ψ a (b + 1) c d - ψ a b (c + 1) d + ψ a b c d)
    (h24 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) c (d + 1) - ψ a (b + 1) c d - ψ a b c (d + 1) + ψ a b c d)
    (h34 : ∀ a b c d : ℕ, 0 ≤ ψ a b (c + 1) (d + 1) - ψ a b (c + 1) d - ψ a b c (d + 1) + ψ a b c d) :
    0 ≤ (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) := by
  have e0 := h13 1 2 1 2
  norm_num at e0
  linarith

theorem T2_identity :
    (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 2 2 2 + ψ 1 2 1 3) + (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 2 3 3 + ψ 1 2 1 2) =
    (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) + (ψ 2 2 2 3 - ψ 2 2 1 3 - ψ 1 2 2 3 + ψ 1 2 1 3) + (ψ 2 2 3 3 - ψ 2 2 2 3 - ψ 1 2 3 3 + ψ 1 2 2 3) + (ψ 2 3 2 2 - ψ 2 3 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + (ψ 2 3 2 3 - ψ 2 3 2 2 - ψ 2 2 2 3 + ψ 2 2 2 2) + (ψ 2 3 3 3 - ψ 2 3 2 3 - ψ 2 2 3 3 + ψ 2 2 2 3) + (ψ 3 3 1 3 - ψ 3 3 1 2 - ψ 2 3 1 3 + ψ 2 3 1 2) + (ψ 3 3 2 3 - ψ 3 3 1 3 - ψ 2 3 2 3 + ψ 2 3 1 3) + (ψ 3 3 3 3 - ψ 3 3 2 3 - ψ 2 3 3 3 + ψ 2 3 2 3) := by
  ring

theorem T2_nonneg
    (h12 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) (b + 1) c d - ψ (a + 1) b c d - ψ a (b + 1) c d + ψ a b c d)
    (h13 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b (c + 1) d - ψ (a + 1) b c d - ψ a b (c + 1) d + ψ a b c d)
    (h14 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b c (d + 1) - ψ (a + 1) b c d - ψ a b c (d + 1) + ψ a b c d)
    (h23 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) (c + 1) d - ψ a (b + 1) c d - ψ a b (c + 1) d + ψ a b c d)
    (h24 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) c (d + 1) - ψ a (b + 1) c d - ψ a b c (d + 1) + ψ a b c d)
    (h34 : ∀ a b c d : ℕ, 0 ≤ ψ a b (c + 1) (d + 1) - ψ a b (c + 1) d - ψ a b c (d + 1) + ψ a b c d) :
    0 ≤ (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 2 2 2 + ψ 1 2 1 3) + (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 2 3 3 + ψ 1 2 1 2) := by
  have e0 := h13 1 2 1 2
  norm_num at e0
  have e1 := h13 1 2 1 3
  norm_num at e1
  have e2 := h13 1 2 2 3
  norm_num at e2
  have e3 := h13 1 3 1 2
  norm_num at e3
  have e4 := h24 2 2 2 2
  norm_num at e4
  have e5 := h23 2 2 2 3
  norm_num at e5
  have e6 := h14 2 3 1 2
  norm_num at e6
  have e7 := h13 2 3 1 3
  norm_num at e7
  have e8 := h13 2 3 2 3
  norm_num at e8
  linarith

theorem T1_identity :
    (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 3 2 2 + ψ 1 3 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 2 3 3 + ψ 1 2 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 3 3 3 + ψ 1 3 1 2) =
    (ψ 2 2 2 3 - ψ 2 2 1 3 - ψ 1 2 2 3 + ψ 1 2 1 3) + (ψ 2 2 3 3 - ψ 2 2 2 3 - ψ 1 2 3 3 + ψ 1 2 2 3) + (ψ 2 3 2 2 - ψ 2 3 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + (ψ 2 3 2 3 - ψ 2 3 1 3 - ψ 1 3 2 3 + ψ 1 3 1 3) + (ψ 2 3 3 3 - ψ 2 3 2 3 - ψ 1 3 3 3 + ψ 1 3 2 3) + (ψ 2 3 2 3 - ψ 2 3 2 2 - ψ 2 2 2 3 + ψ 2 2 2 2) + (ψ 3 2 3 3 - ψ 3 2 2 3 - ψ 2 2 3 3 + ψ 2 2 2 3) + (ψ 3 3 2 2 - ψ 3 3 1 2 - ψ 2 3 2 2 + ψ 2 3 1 2) + (ψ 3 3 2 3 - ψ 3 3 1 3 - ψ 2 3 2 3 + ψ 2 3 1 3) + (ψ 3 3 2 3 - ψ 3 3 2 2 - ψ 2 3 2 3 + ψ 2 3 2 2) + (ψ 3 3 3 3 - ψ 3 3 2 3 - ψ 2 3 3 3 + ψ 2 3 2 3) + (ψ 3 3 3 3 - ψ 3 3 2 3 - ψ 3 2 3 3 + ψ 3 2 2 3) := by
  ring

theorem T1_nonneg
    (h12 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) (b + 1) c d - ψ (a + 1) b c d - ψ a (b + 1) c d + ψ a b c d)
    (h13 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b (c + 1) d - ψ (a + 1) b c d - ψ a b (c + 1) d + ψ a b c d)
    (h14 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b c (d + 1) - ψ (a + 1) b c d - ψ a b c (d + 1) + ψ a b c d)
    (h23 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) (c + 1) d - ψ a (b + 1) c d - ψ a b (c + 1) d + ψ a b c d)
    (h24 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) c (d + 1) - ψ a (b + 1) c d - ψ a b c (d + 1) + ψ a b c d)
    (h34 : ∀ a b c d : ℕ, 0 ≤ ψ a b (c + 1) (d + 1) - ψ a b (c + 1) d - ψ a b c (d + 1) + ψ a b c d) :
    0 ≤ (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 3 2 2 + ψ 1 3 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 2 3 3 + ψ 1 2 1 3) + (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 3 3 3 + ψ 1 3 1 2) := by
  have e0 := h13 1 2 1 3
  norm_num at e0
  have e1 := h13 1 2 2 3
  norm_num at e1
  have e2 := h13 1 3 1 2
  norm_num at e2
  have e3 := h13 1 3 1 3
  norm_num at e3
  have e4 := h13 1 3 2 3
  norm_num at e4
  have e5 := h24 2 2 2 2
  norm_num at e5
  have e6 := h13 2 2 2 3
  norm_num at e6
  have e7 := h13 2 3 1 2
  norm_num at e7
  have e8 := h13 2 3 1 3
  norm_num at e8
  have e9 := h14 2 3 2 2
  norm_num at e9
  have e10 := h13 2 3 2 3
  norm_num at e10
  have e11 := h23 3 2 2 3
  norm_num at e11
  linarith

theorem T0_identity :
    (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 3 3 3 + ψ 1 3 1 3) =
    (ψ 2 3 2 3 - ψ 2 3 1 3 - ψ 1 3 2 3 + ψ 1 3 1 3) + (ψ 2 3 3 3 - ψ 2 3 2 3 - ψ 1 3 3 3 + ψ 1 3 2 3) + (ψ 3 3 2 3 - ψ 3 3 1 3 - ψ 2 3 2 3 + ψ 2 3 1 3) + (ψ 3 3 3 3 - ψ 3 3 2 3 - ψ 2 3 3 3 + ψ 2 3 2 3) := by
  ring

theorem T0_nonneg
    (h12 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) (b + 1) c d - ψ (a + 1) b c d - ψ a (b + 1) c d + ψ a b c d)
    (h13 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b (c + 1) d - ψ (a + 1) b c d - ψ a b (c + 1) d + ψ a b c d)
    (h14 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b c (d + 1) - ψ (a + 1) b c d - ψ a b c (d + 1) + ψ a b c d)
    (h23 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) (c + 1) d - ψ a (b + 1) c d - ψ a b (c + 1) d + ψ a b c d)
    (h24 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) c (d + 1) - ψ a (b + 1) c d - ψ a b c (d + 1) + ψ a b c d)
    (h34 : ∀ a b c d : ℕ, 0 ≤ ψ a b (c + 1) (d + 1) - ψ a b (c + 1) d - ψ a b c (d + 1) + ψ a b c d) :
    0 ≤ (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 3 3 3 + ψ 1 3 1 3) := by
  have e0 := h13 1 3 1 3
  norm_num at e0
  have e1 := h13 1 3 2 3
  norm_num at e1
  have e2 := h13 2 3 1 3
  norm_num at e2
  have e3 := h13 2 3 2 3
  norm_num at e3
  linarith

theorem Sp_nonneg (p q : ℚ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h12 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) (b + 1) c d - ψ (a + 1) b c d - ψ a (b + 1) c d + ψ a b c d)
    (h13 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b (c + 1) d - ψ (a + 1) b c d - ψ a b (c + 1) d + ψ a b c d)
    (h14 : ∀ a b c d : ℕ, 0 ≤ ψ (a + 1) b c (d + 1) - ψ (a + 1) b c d - ψ a b c (d + 1) + ψ a b c d)
    (h23 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) (c + 1) d - ψ a (b + 1) c d - ψ a b (c + 1) d + ψ a b c d)
    (h24 : ∀ a b c d : ℕ, 0 ≤ ψ a (b + 1) c (d + 1) - ψ a (b + 1) c d - ψ a b c (d + 1) + ψ a b c d)
    (h34 : ∀ a b c d : ℕ, 0 ≤ ψ a b (c + 1) (d + 1) - ψ a b (c + 1) d - ψ a b c (d + 1) + ψ a b c d) :
    0 ≤ p * p * p * (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 2 2 2 + ψ 1 2 1 2) + p * p * q * (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 2 2 2 + ψ 1 2 1 3) + p * q * p * (ψ 2 2 2 2 - ψ 2 2 1 2 - ψ 1 3 2 2 + ψ 1 3 1 2) + p * q * q * (ψ 2 2 2 2 - ψ 2 2 1 3 - ψ 1 3 2 2 + ψ 1 3 1 3) + q * p * p * (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 2 3 3 + ψ 1 2 1 2) + q * p * q * (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 2 3 3 + ψ 1 2 1 3) + q * q * p * (ψ 3 3 3 3 - ψ 3 3 1 2 - ψ 1 3 3 3 + ψ 1 3 1 2) + q * q * q * (ψ 3 3 3 3 - ψ 3 3 1 3 - ψ 1 3 3 3 + ψ 1 3 1 3) := by
  have t3 := T3_nonneg ψ h12 h13 h14 h23 h24 h34
  have t2 := T2_nonneg ψ h12 h13 h14 h23 h24 h34
  have t1 := T1_nonneg ψ h12 h13 h14 h23 h24 h34
  have t0 := T0_nonneg ψ h12 h13 h14 h23 h24 h34
  have m3 := mul_nonneg (mul_nonneg (mul_nonneg hp hp) hp) t3
  have m2 := mul_nonneg (mul_nonneg (mul_nonneg hp hp) hq) t2
  have m1 := mul_nonneg (mul_nonneg (mul_nonneg hp hq) hq) t1
  have m0 := mul_nonneg (mul_nonneg (mul_nonneg hq hq) hq) t0
  linarith

end StarCertificates

#print axioms StarCertificates.S_identity
#print axioms StarCertificates.S_nonneg
#print axioms StarCertificates.T3_identity
#print axioms StarCertificates.T2_identity
#print axioms StarCertificates.T1_identity
#print axioms StarCertificates.T0_identity
#print axioms StarCertificates.Sp_nonneg
