import CorruptedFieldRecovery.FourContractions

/-! Transport of the sampled-basis result across the manuscript's hidden
binary-linear input isomorphism.  The isomorphism is an explicit hypothesis:
this file does not construct it from an unknown field or from a corrupted
tensor. -/

namespace CorruptedFieldRecovery

open Module

/-- A length-`n` binary input, with the coefficient ring written as the prime
field of `K`. Under the characteristic-two hypothesis this is the manuscript
space `F₂ⁿ`. -/
abbrev BinaryInput (K : Type*) [Field K] (n : ℕ) :=
  Fin n → ZMod (ringChar K)

/-- The four contractions on the original input, evaluated by first applying
the hidden binary-linear isomorphism and then the actual sampled determinant
contractions. Thus the equations below concern tensor values on physical
input vectors, not a renamed coordinate predicate. -/
def hiddenFourBalanced
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    {n : ℕ} (ι : BinaryInput K n ≃ₗ[ZMod (ringChar K)] FieldTriple K)
    (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (T : Module.End (ZMod (ringChar K)) (BinaryInput K n)) : Prop :=
  (∀ x y, sampledContraction0 K c basis (ι (T x)) (ι y) =
      sampledContraction0 K c basis (ι x) (ι (T y))) ∧
  (∀ x y, sampledContraction1 K c basis (ι (T x)) (ι y) =
      sampledContraction1 K c basis (ι x) (ι (T y))) ∧
  (∀ x y, sampledContraction2 K c basis (ι (T x)) (ι y) =
      sampledContraction2 K c basis (ι x) (ι (T y))) ∧
  (∀ x y, sampledContraction4 K c v (ι (T x)) (ι y) =
      sampledContraction4 K c v (ι x) (ι (T y)))

/-- The physical equations are equivalent to the sampled equations after
conjugating the endomorphism by the hidden input isomorphism. The proof uses
surjectivity of the isomorphism to transport both quantified arguments. -/
theorem hidden_four_balanced_iff_conjugate
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    {n : ℕ} (ι : BinaryInput K n ≃ₗ[ZMod (ringChar K)] FieldTriple K)
    (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (T : Module.End (ZMod (ringChar K)) (BinaryInput K n)) :
    hiddenFourBalanced K ι basis v c T ↔
      sampledFourBalanced K c basis v
        ((ι.restrictScalars (ZMod (ringChar K))).conj T) := by
  let q := ι.restrictScalars (ZMod (ringChar K))
  let T' := q.conj T
  change
    (∀ x y, sampledContraction0 K c basis (ι (T x)) (ι y) =
        sampledContraction0 K c basis (ι x) (ι (T y))) ∧
    (∀ x y, sampledContraction1 K c basis (ι (T x)) (ι y) =
        sampledContraction1 K c basis (ι x) (ι (T y))) ∧
    (∀ x y, sampledContraction2 K c basis (ι (T x)) (ι y) =
        sampledContraction2 K c basis (ι x) (ι (T y))) ∧
    (∀ x y, sampledContraction4 K c v (ι (T x)) (ι y) =
        sampledContraction4 K c v (ι x) (ι (T y))) ↔
    ((∀ x y, sampledContraction0 K c basis (T' x) y =
        sampledContraction0 K c basis x (T' y)) ∧
     (∀ x y, sampledContraction1 K c basis (T' x) y =
        sampledContraction1 K c basis x (T' y)) ∧
     (∀ x y, sampledContraction2 K c basis (T' x) y =
        sampledContraction2 K c basis x (T' y)) ∧
     (∀ x y, sampledContraction4 K c v (T' x) y =
        sampledContraction4 K c v x (T' y)))
  constructor
  · rintro ⟨h0b, h1b, h2b, h4b⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x y
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h0b (q.symm x) (q.symm y)
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h1b (q.symm x) (q.symm y)
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h2b (q.symm x) (q.symm y)
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h4b (q.symm x) (q.symm y)
  · rintro ⟨h0b, h1b, h2b, h4b⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x y
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h0b (q x) (q y)
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h1b (q x) (q y)
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h2b (q x) (q y)
    · simpa [T', q, LinearEquiv.conj_apply_apply] using h4b (q x) (q y)

/-- The sampled-basis identification theorem applies on the manuscript's
original binary vector space after transporting the endomorphism through the
hidden input isomorphism. The coefficient and generator hypotheses are kept
explicit, including the determinant rescaling performed by the sampled-basis
theorem. -/
theorem hidden_four_contractions_identification
    (K : Type*) [Field K] [Finite K] [Fintype K] [CharP K 2]
    [Algebra (ZMod (ringChar K)) K]
    {n : ℕ} (ι : BinaryInput K n ≃ₗ[ZMod (ringChar K)] FieldTriple K)
    (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).1} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).2.1} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).2.2} = ⊤) :
    (∀ T : Module.End (ZMod (ringChar K)) (BinaryInput K n),
      hiddenFourBalanced K ι basis v c T ↔
        ∃ k : K, ∀ x, T x = ι.symm (k • ι x)) ∧
    Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
      Module.finrank (ZMod (ringChar K)) K := by
  constructor
  · intro T
    rw [hidden_four_balanced_iff_conjugate]
    let q := ι.restrictScalars (ZMod (ringChar K))
    let T' := q.conj T
    have hsample := (sampled_four_contractions_identification_and_finrank
      K basis v c hc hgen).1 T'
    rw [hsample]
    rw [scalarTripleEndRange_mem_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro x
      apply q.injective
      have hx := hk (q x)
      simpa [T', q, LinearEquiv.conj_apply_apply,
        fieldScalarTriple_eq_smul] using hx
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro y
      have hy := congrArg q (hk (q.symm y))
      simpa [T', q, LinearEquiv.conj_apply_apply,
        fieldScalarTriple_eq_smul] using hy
  · exact (sampled_four_contractions_identification_and_finrank
      K basis v c hc hgen).2

end CorruptedFieldRecovery
