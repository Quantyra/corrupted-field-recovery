import CorruptedFieldRecovery.RawRabinFrobenius
import Mathlib.FieldTheory.Finite.Basic

/-! An irreducible polynomial of degree `d` divides the degree-`d` binary
Frobenius polynomial. The proof uses the actual finite quotient field. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- In the finite field obtained by adjoining a root of a monic irreducible
polynomial over `F₂`, the root satisfies `α^(2^d)=α`; hence the polynomial
divides `X^(2^d)-X`. -/
theorem irreducible_dvd_X_pow_two_pow_natDegree
    {q : Polynomial (ZMod 2)} (hq : Irreducible q) (hmonic : q.Monic) :
    q ∣ X ^ (2 ^ q.natDegree) - X := by
  classical
  letI : Fact (Irreducible q) := ⟨hq⟩
  let pb := AdjoinRoot.powerBasis' hmonic
  letI : Fintype (AdjoinRoot q) :=
    Fintype.ofEquiv (Fin pb.dim → ZMod 2) pb.basis.equivFun.toEquiv.symm
  have hdim : pb.dim = q.natDegree := rfl
  have hcard : Fintype.card (AdjoinRoot q) = 2 ^ q.natDegree := by
    calc
      Fintype.card (AdjoinRoot q) = Fintype.card (Fin pb.dim → ZMod 2) :=
        Fintype.card_congr pb.basis.equivFun.toEquiv
      _ = 2 ^ q.natDegree := by simp [hdim]
  have hpow : (AdjoinRoot.mk q X) ^ (2 ^ q.natDegree) = AdjoinRoot.mk q X := by
    simpa [hcard] using (FiniteField.pow_card (AdjoinRoot.mk q X))
  have hzero : AdjoinRoot.mk q (X ^ (2 ^ q.natDegree) - X) = 0 := by
    simp only [map_sub, map_pow]
    exact sub_eq_zero.mpr hpow
  exact AdjoinRoot.mk_eq_zero.mp hzero

end CorruptedFieldRecovery
