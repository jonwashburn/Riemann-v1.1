import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Primality.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-!
# Weighted Hilbert Space ℓ²(P, p^{-2})

This file defines the weighted Hilbert space used in the Riemann Hypothesis proof framework.
The space consists of sequences indexed by primes with weight p^{-2}.
-/

open scoped ENNReal NNReal ComplexConjugate
open Complex

/-- The type of sequences indexed by primes -/
def PrimeSeq (α : Type*) := {p : ℕ // Nat.Prime p} → α

namespace PrimeSeq

variable {α β : Type*}

/-- Coercion from prime sequences to functions on naturals -/
instance : CoeFun (PrimeSeq α) (fun _ => {p : ℕ // Nat.Prime p} → α) where
  coe := id

/-- The zero sequence -/
instance [Zero α] : Zero (PrimeSeq α) where
  zero := fun _ => 0

/-- Addition of sequences -/
instance [Add α] : Add (PrimeSeq α) where
  add f g := fun p => f p + g p

/-- Scalar multiplication -/
instance [SMul β α] : SMul β (PrimeSeq α) where
  smul c f := fun p => c • f p

/-- Negation -/
instance [Neg α] : Neg (PrimeSeq α) where
  neg f := fun p => -f p

/-- Subtraction -/
instance [Sub α] : Sub (PrimeSeq α) where
  sub f g := fun p => f p - g p

end PrimeSeq

/-- The weight function p^{-2} for prime p -/
def primeWeight (p : {p : ℕ // Nat.Prime p}) : ℝ≥0∞ :=
  (p.val : ℝ≥0∞)⁻¹ ^ 2

lemma primeWeight_pos (p : {p : ℕ // Nat.Prime p}) : 0 < primeWeight p := by
  simp [primeWeight]
  rw [ENNReal.pow_pos]
  · exact ENNReal.inv_pos.mpr (ENNReal.coe_ne_top)
  · exact two_ne_zero

/-- The weighted ℓ² space over primes with weight p^{-2} -/
def WeightedHilbertSpace :=
  lp (fun (p : {p : ℕ // Nat.Prime p}) => primeWeight p) 2

namespace WeightedHilbertSpace

/-- WeightedHilbertSpace is a complex vector space -/
instance : AddCommGroup WeightedHilbertSpace := by
  unfold WeightedHilbertSpace
  infer_instance

instance : Module ℂ WeightedHilbertSpace := by
  unfold WeightedHilbertSpace
  infer_instance

/-- The inner product on WeightedHilbertSpace -/
instance : InnerProductSpace ℂ WeightedHilbertSpace := by
  unfold WeightedHilbertSpace
  exact lp.instInnerProductSpace (fun p => primeWeight p)

/-- The norm on WeightedHilbertSpace -/
instance : Norm WeightedHilbertSpace := by
  unfold WeightedHilbertSpace
  infer_instance

/-- Basis vectors δ_p for each prime p -/
def deltaBasis (p : {p : ℕ // Nat.Prime p}) : WeightedHilbertSpace := by
  use fun q => if q = p then 1 else 0
  simp only [mem_lp_infty_iff]
  constructor
  · intro q
    split_ifs
    · simp
    · simp
  · rw [Memℓp.summable_iff]
    · convert summable_of_ne_finset_zero {p} _
      intro q hq
      simp at hq
      simp [hq, Ne.symm hq]
    · norm_num

@[simp]
lemma deltaBasis_apply (p q : {p : ℕ // Nat.Prime p}) :
    (deltaBasis p).val q = if q = p then 1 else 0 := rfl

/-- The delta basis vectors are orthonormal with respect to the weighted inner product -/
lemma deltaBasis_orthonormal :
    ∀ p q : {p : ℕ // Nat.Prime p},
    ⟪deltaBasis p, deltaBasis q⟫_ℂ = if p = q then (primeWeight p : ℂ)⁻¹ else 0 := by
  intro p q
  simp only [lp.inner_apply]
  by_cases h : p = q
  · subst h
    simp [deltaBasis_apply, primeWeight]
    rw [Finset.sum_eq_single p]
    · simp [mul_comm]
      norm_cast
      rw [← ENNReal.coe_inv, ENNReal.coe_pow]
      · simp
      · exact ENNReal.coe_ne_top
    · intro b _ hb
      simp [deltaBasis_apply, hb]
    · intro hp
      simp at hp
  · simp [deltaBasis_apply, h]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hp : r = p
    · subst hp
      simp [h]
    · by_cases hq : r = q
      · subst hq
        simp [Ne.symm h]
      · simp [hp, hq]

/-- Helper function to create elements of WeightedHilbertSpace from coefficients -/
def fromCoeffs (c : PrimeSeq ℂ) (h : Summable fun p => ‖c p‖^2 * (primeWeight p).toReal) :
    WeightedHilbertSpace := by
  use c
  rw [Memℓp.summable_iff]
  · convert h
    ext p
    simp [primeWeight]
    norm_cast
    simp [← sq]
  · norm_num

/-- Extract coefficients from an element of WeightedHilbertSpace -/
def toCoeffs (ψ : WeightedHilbertSpace) : PrimeSeq ℂ := ψ.val

@[simp]
lemma toCoeffs_apply (ψ : WeightedHilbertSpace) (p : {p : ℕ // Nat.Prime p}) :
    toCoeffs ψ p = ψ.val p := rfl

/-- The arithmetic Hamiltonian H: δ_p ↦ (log p)δ_p -/
def arithmeticHamiltonian (ψ : WeightedHilbertSpace) : PrimeSeq ℂ :=
  fun p => (Real.log p.val : ℂ) * ψ.val p

/-- Domain of the arithmetic Hamiltonian -/
def domainH : Set WeightedHilbertSpace :=
  {ψ | Summable fun p => ‖(Real.log p.val : ℂ) * ψ.val p‖^2 * (primeWeight p).toReal}

/-- The operator A(s) = e^{-sH} acting diagonally with entries p^{-s} -/
def operatorA (s : ℂ) (ψ : WeightedHilbertSpace) : PrimeSeq ℂ :=
  fun p => (p.val : ℂ)^(-s) * ψ.val p

/-- Domain of A(s) -/
def domainA (s : ℂ) : Set WeightedHilbertSpace :=
  {ψ | Summable fun p => ‖(p.val : ℂ)^(-s) * ψ.val p‖^2 * (primeWeight p).toReal}

/-- A(s) maps WeightedHilbertSpace to itself for Re(s) > 0 -/
lemma operatorA_wellDefined (s : ℂ) (hs : 0 < s.re) (ψ : WeightedHilbertSpace) :
    ψ ∈ domainA s := by
  sorry

/-- The action functional J_β(ψ) = Σ_p |c_p|²(log p)^{2β} -/
def actionFunctional (β : ℝ) (ψ : WeightedHilbertSpace) : ℝ :=
  ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β)

/-- Domain of the action functional -/
def domainJ (β : ℝ) : Set WeightedHilbertSpace :=
  {ψ | Summable fun p => ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β)}

end WeightedHilbertSpace
