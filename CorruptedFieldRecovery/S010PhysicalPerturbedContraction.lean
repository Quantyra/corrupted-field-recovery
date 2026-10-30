import CorruptedFieldRecovery.BinaryTensor
import CorruptedFieldRecovery.Support
import CorruptedFieldRecovery.Defect

namespace CorruptedFieldRecovery

noncomputable section

/-- The physical contraction of a binary trilinear tensor in its first two
slots, retained as the actual covector on the input space. -/
def physicalBinaryContraction {n : Nat} (A : BinaryTensor n)
    (x y : BinaryVector n) : Module.Dual (ZMod 2) (BinaryVector n) := A x y

/-- The manuscript's perturbed physical tensor: a compatible tensor on the
input plus the pullback of the hidden tensor through the observation map. -/
def physicalPerturbedTensor {n m : Nat}
    (C : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m) : BinaryTensor n :=
  C + pullback E u

/-- Evaluating the actual perturbed physical contraction exposes its clean
part and its pulled-back hidden contribution. -/
theorem physicalPerturbedContraction_apply {n m : Nat}
    (C : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (x y z : BinaryVector n) :
    physicalBinaryContraction (physicalPerturbedTensor C E u) x y z =
      C x y z + E (u x) (u y) (u z) := by
  simp [physicalBinaryContraction, physicalPerturbedTensor, pullback_apply]

/-- If the observed third vector lies in the annihilator of the hidden tensor's
mode image, the hidden contribution to the actual physical contraction is
zero. This uses the manuscript support `modeImage E` itself. -/
theorem physicalPerturbedContraction_eq_clean_on_modeImage_coannihilator
    {n m : Nat} (C : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (x y z : BinaryVector n)
    (hz : u z ∈ (modeImage E).dualCoannihilator) :
    physicalBinaryContraction (physicalPerturbedTensor C E u) x y z =
      C x y z := by
  rw [physicalPerturbedContraction_apply]
  rw [Submodule.mem_dualCoannihilator] at hz
  have hmode : E (u x) (u y) ∈ modeImage E :=
    Submodule.subset_span ⟨(u x, u y), rfl⟩
  have hzero := hz (E (u x) (u y)) hmode
  rw [hzero, add_zero]

end

end CorruptedFieldRecovery
