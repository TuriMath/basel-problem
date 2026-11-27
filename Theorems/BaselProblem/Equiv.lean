import Theorems.BaselProblem.A
import Theorems.BaselProblem.B

/-!
# Basel problem: A ↔ B (Euler)

Matching argument: A says `partialSum → π²/6` (filter form); B is the ε–N form of the same
partial sums.  Both directions unfold the other statement and translate it with
`Metric.tendsto_atTop` and `Real.dist_eq`; no Mathlib copy of the theorem is used.
-/

namespace TuriMath.BaselProblem

theorem equiv : A.Statement ↔ B.Statement := by
  unfold A.Statement B.Statement
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by simpa [A.partialSum, Real.dist_eq] using hN n hn⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by simpa [A.partialSum, Real.dist_eq] using hN n hn⟩

end TuriMath.BaselProblem
