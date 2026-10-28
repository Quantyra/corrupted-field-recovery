import CorruptedFieldRecovery.Defect
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-! Dense binary trilinear input semantics for the manuscript. -/

namespace CorruptedFieldRecovery

/-- A physical input vector in the manuscript's binary coordinate model. -/
abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2

/-- An explicitly represented trilinear tensor on `F₂^n`. -/
abbrev BinaryTensor (n : ℕ) := Trilinear (ZMod 2) (BinaryVector n)

/-- The standard coordinate vector indexed by `i`. -/
noncomputable def coordinateVector {n : ℕ} (i : Fin n) : BinaryVector n :=
  Pi.basisFun (ZMod 2) (Fin n) i

/-- The ordered coefficient table of a dense tensor. -/
noncomputable def coefficient {n : ℕ} (C : BinaryTensor n) (i j k : Fin n) : ZMod 2 :=
  C (coordinateVector i) (coordinateVector j) (coordinateVector k)

/-- Vanishing whenever any two arguments agree. -/
def IsAlternating {n : ℕ} (C : BinaryTensor n) : Prop :=
  (∀ x y, C x x y = 0) ∧ (∀ x y, C x y x = 0) ∧ (∀ x y, C x y y = 0)

/-- Equality of every ordered basis coefficient implies equality on all vectors.
The proof expands each of the three vector arguments in the standard basis. -/
theorem binaryTensor_ext_of_coefficients {n : ℕ} {C D : BinaryTensor n}
    (h : ∀ i j k, coefficient C i j k = coefficient D i j k) : C = D := by
  apply (Pi.basisFun (ZMod 2) (Fin n)).ext
  intro i
  apply (Pi.basisFun (ZMod 2) (Fin n)).ext
  intro j
  apply (Pi.basisFun (ZMod 2) (Fin n)).ext
  intro k
  exact h i j k

/-- Alternation in the first two arguments implies symmetry there over `F₂`. -/
theorem alternating_swap12 {n : ℕ} {C : BinaryTensor n}
    (h : IsAlternating C) (x y z : BinaryVector n) :
    C y x z = C x y z := by
  have hdiag := h.1 (x + y) z
  have hcross : C y x z + C x y z = 0 := by
    simpa only [LinearMap.map_add, LinearMap.add_apply, h.1 x z, h.1 y z,
      zero_add, add_zero] using hdiag
  have heq := eq_neg_of_add_eq_zero_left hcross
  simpa using heq

/-- Alternation in the last two arguments implies symmetry there over `F₂`. -/
theorem alternating_swap23 {n : ℕ} {C : BinaryTensor n}
    (h : IsAlternating C) (x y z : BinaryVector n) :
    C x z y = C x y z := by
  have hdiag := h.2.2 x (y + z)
  have hcross : C x z y + C x y z = 0 := by
    simpa only [LinearMap.map_add, LinearMap.add_apply, h.2.2 x y, h.2.2 x z,
      zero_add, add_zero] using hdiag
  have heq := eq_neg_of_add_eq_zero_left hcross
  simpa using heq

/-- Alternation gives symmetry under exchanging the first and third arguments. -/
theorem alternating_swap13 {n : ℕ} {C : BinaryTensor n}
    (h : IsAlternating C) (x y z : BinaryVector n) :
    C z y x = C x y z := by
  calc
    C z y x = C y z x := (alternating_swap12 h z y x).symm
    _ = C y x z := (alternating_swap23 h y z x).symm
    _ = C x y z := (alternating_swap12 h y x z).symm

/-- Alternating tensors are determined by their strictly increasing triple
coefficients, matching the manuscript's dense input encoding. -/
theorem binaryTensor_ext_of_increasing_coefficients {n : ℕ} {C D : BinaryTensor n}
    (hC : IsAlternating C) (hD : IsAlternating D)
    (h : ∀ i j k, i < j → j < k → coefficient C i j k = coefficient D i j k) :
    C = D := by
  apply binaryTensor_ext_of_coefficients
  intro i j k
  have swap12C (a b c : Fin n) : coefficient C a b c = coefficient C b a c := by
    change C (coordinateVector a) (coordinateVector b) (coordinateVector c) =
      C (coordinateVector b) (coordinateVector a) (coordinateVector c)
    exact (alternating_swap12 hC (coordinateVector a) (coordinateVector b)
      (coordinateVector c)).symm
  have swap23C (a b c : Fin n) : coefficient C a b c = coefficient C a c b := by
    change C (coordinateVector a) (coordinateVector b) (coordinateVector c) =
      C (coordinateVector a) (coordinateVector c) (coordinateVector b)
    exact (alternating_swap23 hC (coordinateVector a) (coordinateVector b)
      (coordinateVector c)).symm
  have swap12D (a b c : Fin n) : coefficient D a b c = coefficient D b a c := by
    change D (coordinateVector a) (coordinateVector b) (coordinateVector c) =
      D (coordinateVector b) (coordinateVector a) (coordinateVector c)
    exact (alternating_swap12 hD (coordinateVector a) (coordinateVector b)
      (coordinateVector c)).symm
  have swap23D (a b c : Fin n) : coefficient D a b c = coefficient D a c b := by
    change D (coordinateVector a) (coordinateVector b) (coordinateVector c) =
      D (coordinateVector a) (coordinateVector c) (coordinateVector b)
    exact (alternating_swap23 hD (coordinateVector a) (coordinateVector b)
      (coordinateVector c)).symm
  by_cases hij : i = j
  · subst j
    have hC0 : coefficient C i i k = 0 := by
      simpa [coefficient] using hC.1 (coordinateVector i) (coordinateVector k)
    have hD0 : coefficient D i i k = 0 := by
      simpa [coefficient] using hD.1 (coordinateVector i) (coordinateVector k)
    rw [hC0, hD0]
  · by_cases hik : i = k
    · subst k
      have hC0 : coefficient C i j i = 0 := by
        simpa [coefficient] using hC.2.1 (coordinateVector i) (coordinateVector j)
      have hD0 : coefficient D i j i = 0 := by
        simpa [coefficient] using hD.2.1 (coordinateVector i) (coordinateVector j)
      rw [hC0, hD0]
    · by_cases hjk : j = k
      · subst k
        have hC0 : coefficient C i j j = 0 := by
          simpa [coefficient] using hC.2.2 (coordinateVector i) (coordinateVector j)
        have hD0 : coefficient D i j j = 0 := by
          simpa [coefficient] using hD.2.2 (coordinateVector i) (coordinateVector j)
        rw [hC0, hD0]
      · by_cases hijlt : i < j
        · by_cases hjklt : j < k
          · exact h i j k hijlt hjklt
          · have hkj : k < j := by omega
            by_cases hiklt : i < k
            · calc
                coefficient C i j k = coefficient C i k j := swap23C i j k
                _ = coefficient D i k j := h i k j hiklt hkj
                _ = coefficient D i j k := (swap23D i j k).symm
            · have hki : k < i := by omega
              calc
                coefficient C i j k = coefficient C j i k := swap12C i j k
                _ = coefficient C j k i := swap23C j i k
                _ = coefficient C k j i := swap12C j k i
                _ = coefficient C k i j := swap23C k j i
                _ = coefficient D k i j := h k i j hki hijlt
                _ = coefficient D k j i := (swap23D k j i).symm
                _ = coefficient D j k i := (swap12D j k i).symm
                _ = coefficient D j i k := (swap23D j i k).symm
                _ = coefficient D i j k := (swap12D i j k).symm
        · have hji : j < i := by omega
          by_cases hki : k < i
          · by_cases hkj : k < j
            · calc
                coefficient C i j k = coefficient C j i k := swap12C i j k
                _ = coefficient C j k i := swap23C j i k
                _ = coefficient C k j i := swap12C j k i
                _ = coefficient D k j i := h k j i hkj hji
                _ = coefficient D j k i := (swap12D j k i).symm
                _ = coefficient D j i k := (swap23D j i k).symm
                _ = coefficient D i j k := (swap12D i j k).symm
            · have hjklt : j < k := by omega
              calc
                coefficient C i j k = coefficient C j i k := swap12C i j k
                _ = coefficient C j k i := swap23C j i k
                _ = coefficient D j k i := h j k i hjklt hki
                _ = coefficient D j i k := (swap23D j i k).symm
                _ = coefficient D i j k := (swap12D i j k).symm
          · have hiklt : i < k := by omega
            calc
              coefficient C i j k = coefficient C j i k := swap12C i j k
              _ = coefficient D j i k := h j i k hji hiklt
              _ = coefficient D i j k := (swap12D i j k).symm

end CorruptedFieldRecovery
