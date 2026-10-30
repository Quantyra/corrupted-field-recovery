import CorruptedFieldRecovery.S010GoodTapePhysicalContraction
import Mathlib.LinearAlgebra.BilinearForm.Basic

namespace CorruptedFieldRecovery

noncomputable section

/-- The actual physical bilinear contraction in the first two tensor slots,
with the third slot fixed. -/
def physicalThirdSlotBilinForm {n : Nat} (A : BinaryTensor n)
    (z : BinaryVector n) : LinearMap.BilinForm (ZMod 2) (BinaryVector n) :=
  { toFun := fun x =>
      { toFun := fun y => A x y z
        map_add' := by intro y y'; simp
        map_smul' := by intro a y; simp }
    map_add' := by intro x x'; ext y; simp
    map_smul' := by intro a x; ext y; simp }

/-- The hidden term contributes zero to the entire physical bilinear form on
any clean third-slot vector. Both arguments of the contraction remain
arbitrary. -/
theorem physicalPerturbed_bilinForm_eq_clean_of_modeImage_coannihilator
    {n m : Nat} (C : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (z : BinaryVector n)
    (hz : u z ∈ (modeImage E).dualCoannihilator) :
    physicalThirdSlotBilinForm (physicalPerturbedTensor C E u) z =
      physicalThirdSlotBilinForm C z := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact physicalPerturbedContraction_eq_clean_on_modeImage_coannihilator
    C E u x y z hz

/-- For any endomorphism T, balancing of C on a clean sampled third slot is
preserved by the full perturbed physical contraction form. The compatibility
balance premise remains explicit. -/
theorem physicalPerturbed_balance_of_clean_slot
    {n m : Nat} (C : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (z : BinaryVector n)
    (hz : u z ∈ (modeImage E).dualCoannihilator)
    (T : Module.End (ZMod 2) (BinaryVector n))
    (hC : ∀ x y,
      physicalThirdSlotBilinForm C z (T x) y =
        physicalThirdSlotBilinForm C z x (T y)) :
    ∀ x y,
      physicalThirdSlotBilinForm (physicalPerturbedTensor C E u) z (T x) y =
        physicalThirdSlotBilinForm (physicalPerturbedTensor C E u) z x (T y) := by
  intro x y
  rw [physicalPerturbed_bilinForm_eq_clean_of_modeImage_coannihilator C E u z hz]
  exact hC x y

/-- The previous balance statement specializes to any third word of an actual
good five-tape event. The first two arguments remain arbitrary physical input
vectors, so this is an equality of the complete contraction bilinear forms. -/
theorem modeImage_actual_good_tape_balance_on_clean_slot
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [CharP K 2] [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E C : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (k : Fin 4) (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (hC : ∀ x y,
      physicalThirdSlotBilinForm C (tape.1 k) (T x) y =
        physicalThirdSlotBilinForm C (tape.1 k) x (T y)) :
    ∀ x y,
      physicalThirdSlotBilinForm (physicalPerturbedTensor C E LinearMap.id)
        (tape.1 k) (T x) y =
        physicalThirdSlotBilinForm (physicalPerturbedTensor C E LinearMap.id)
          (tape.1 k) x (T y) := by
  apply physicalPerturbed_balance_of_clean_slot
    C E LinearMap.id (tape.1 k)
    (modeImage_actual_good_tape_words_clean Q E U b tape htape k) T hC

end

end CorruptedFieldRecovery
