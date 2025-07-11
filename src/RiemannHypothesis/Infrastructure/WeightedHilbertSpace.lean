import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Prime

namespace RH

noncomputable abbrev WeightedL2 := lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2

namespace WeightedL2

noncomputable def deltaBasis (p : {p : ℕ // Nat.Prime p}) : WeightedL2 :=
  lp.single 2 p 1

lemma norm_sq_eq_sum (ψ : WeightedL2) :
    ‖ψ‖ ^ 2 = ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ p‖ ^ 2 := sorry

end WeightedL2

end RH
