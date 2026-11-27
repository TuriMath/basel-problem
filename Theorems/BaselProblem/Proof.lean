import Theorems.BaselProblem.A
import Mathlib.NumberTheory.ZetaValues

/-!
# Basel problem: proof (Euler)

From Mathlib's `hasSum_zeta_two` (sum over `n : ℕ` from 0, the `1/0` term being `0`):
`HasSum.tendsto_sum_nat` gives convergence of `∑ i ∈ range N`, and
`range (N+1) = {0} ∪ Icc 1 N` turns that into the statement's partial sums.
-/

namespace TuriMath.BaselProblem

open Filter Finset

theorem main : A.Statement := by
  unfold A.Statement
  have h := hasSum_zeta_two.tendsto_sum_nat
  have h' := (tendsto_add_atTop_iff_nat 1).mpr h
  refine h'.congr fun N => ?_
  rw [A.partialSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp
  rfl

end TuriMath.BaselProblem
