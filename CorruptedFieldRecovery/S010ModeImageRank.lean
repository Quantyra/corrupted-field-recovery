import CorruptedFieldRecovery.S010ModeImageTrialBound

namespace CorruptedFieldRecovery

open Module

noncomputable section

/-- The semantic rank parameter is exactly the rank of the manuscript's
physical mode image, because the accepted transport is a linear equivalence. -/
theorem modeImageSemanticSupport_finrank_eq
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s)) :
    Module.finrank BinaryField (modeImageSemanticSupport Q E) =
      Module.finrank BinaryField (modeImage E) := by
  dsimp [modeImageSemanticSupport, semanticSupportFromPhysical]
  exact (fieldToPhysicalDualEquiv Q).symm.finrank_map_eq (modeImage E)

end

end CorruptedFieldRecovery
