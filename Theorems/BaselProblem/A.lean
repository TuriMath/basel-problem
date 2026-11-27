import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Basel problem: statement A (Noether)

Source (issue #1, Wikipedia "Basel problem", Wiedijk 100 item 14):
the infinite series ∑_{n=1}^{∞} 1/n² = 1/1² + 1/2² + 1/3² + ⋯ has exact sum π²/6.
-/

namespace TuriMath.BaselProblem.A

open Filter Finset

/-- The `N`-th partial sum `1/1² + 1/2² + ⋯ + 1/N²` of the source series, in `ℝ`. -/
noncomputable def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ^ 2

/-- **Basel problem.** Mapping from the source quote to the Lean, one line each:

* "the reciprocals of the squares of the natural numbers" — terms `1 / (n : ℝ) ^ 2`, `n : ℕ`,
  computed in `ℝ` (real division, not natural-number division).
* "∑_{n=1}^{∞}" — index starts at `n = 1` (`Finset.Icc 1 N`), so no `1/0` term appears;
  `ℕ` not `ℤ` because the source says natural numbers, starting at 1.
* "the precise sum of the infinite series" — the classical meaning: the partial sums
  `1/1² + ⋯ + 1/N²` converge as `N → ∞` (`Tendsto … atTop`), and the limit is the sum.
  The limit existing is part of the claim, so convergence is asserted, not assumed.
* "π²/6" — `Real.pi ^ 2 / 6`, the real number pi.
-/
def Statement : Prop :=
  Tendsto partialSum atTop (nhds (Real.pi ^ 2 / 6))

/-! ## Sanity section

`Statement` has no hypotheses, so there is nothing to show jointly satisfiable.
Instead, checks that the indexing matches the source: the first partial sums are
`1/1²` and `1/1² + 1/2²`, and the empty sum (`N = 0`) is `0`. -/

example : partialSum 0 = 0 := by
  simp [partialSum]

example : partialSum 1 = 1 := by
  simp [partialSum]

example : partialSum 2 = 1 / 1 ^ 2 + 1 / 2 ^ 2 := by
  rw [partialSum, show Icc 1 2 = {1, 2} by rfl]
  norm_num

end TuriMath.BaselProblem.A
