import Mathlib

/-!
# Basel problem: statement B (Gauss, blind formalizer)

Source (Wikipedia, "Basel problem"; Wiedijk's 100 list, item 14):
> The Basel problem asks for the precise summation of the reciprocals of the squares of the natural
> numbers, i.e. the precise sum of the infinite series ∑_{n=1}^{∞} 1/n² = 1/1² + 1/2² + 1/3² + ⋯
> … Euler found the exact sum to be π²/6

Phrasing chosen: the most elementary one. "The infinite series has sum S" is read as the classical
ε–N statement that its partial sums `1/1² + ⋯ + 1/n²` get and stay within any ε > 0 of S.
No `HasSum`, no `tsum`, no filters.

Mapping, source → Lean:
* "reciprocals of the squares of the natural numbers"  → the term `1 / (k : ℝ) ^ 2`
* "∑_{n=1}^{∞}" (summation starts at 1)               → partial sums over `Finset.Icc 1 n`, so the
                                                         index k runs 1, 2, …, n and k = 0 never appears
* "1/1² + 1/2² + 1/3² + ⋯" (an infinite series)        → the limit of those partial sums as n → ∞,
                                                         written as `∀ ε > 0, ∃ N, ∀ n ≥ N, |… - S| < ε`
* "the precise sum … to be"                           → that limit equals S exactly (any ε works)
* "π²/6"                                              → `Real.pi ^ 2 / 6`, a real number
* "the series" (real numbers)                         → everything is in `ℝ`; convergence is part of
                                                         the claim, since a limit is asserted to exist
-/

namespace TuriMath.BaselProblem.B

open Finset

/-- Basel problem: the partial sums of `∑_{n ≥ 1} 1/n²` converge to `π²/6`. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2) - Real.pi ^ 2 / 6| < ε

/-! ## Sanity section

There are no hypotheses besides `0 < ε` and `N ≤ n`; these can hold at once. -/

example : ∃ ε : ℝ, 0 < ε := ⟨1, one_pos⟩
example : ∃ N n : ℕ, N ≤ n := ⟨0, 0, le_rfl⟩

/-! ## Concrete checks of the partial sums

For n = 1 the sum is 1/1² = 1; for n = 2 it is 1 + 1/4 = 5/4; for n = 3 it is
1 + 1/4 + 1/9 = 49/36. -/

example : (∑ k ∈ Icc (1 : ℕ) 1, 1 / (k : ℝ) ^ 2) = 1 := by
  simp

example : (∑ k ∈ Icc (1 : ℕ) 2, 1 / (k : ℝ) ^ 2) = 5 / 4 := by
  rw [Finset.sum_Icc_succ_top (by norm_num)]
  simp
  norm_num

example : (∑ k ∈ Icc (1 : ℕ) 3, 1 / (k : ℝ) ^ 2) = 49 / 36 := by
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num)]
  simp
  norm_num

/-- The index really starts at 1: the term k = 0 is not in the range. -/
example : (0 : ℕ) ∉ Icc 1 5 := by decide

/-- The target is the right size: since π > 3, π²/6 > 9/6 = 1.5, already above the third partial
sum 49/36 ≈ 1.361 (the true value is ≈ 1.6449). And π < 3.15 gives π²/6 < 1.66. -/
example : (49 / 36 : ℝ) < Real.pi ^ 2 / 6 := by
  have h := Real.pi_gt_three
  nlinarith

example : Real.pi ^ 2 / 6 < 1.66 := by
  have h1 := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

/-- Together with the bound above, the target sits in (1.6, 1.66), matching the known value
π²/6 ≈ 1.6449; so `Real.pi ^ 2 / 6` is the intended number, not a mis-typed one. -/
example : (1.6 : ℝ) < Real.pi ^ 2 / 6 := by
  have h := Real.pi_gt_d2
  nlinarith

end TuriMath.BaselProblem.B
