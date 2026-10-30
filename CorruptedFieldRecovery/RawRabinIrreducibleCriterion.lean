import CorruptedFieldRecovery.RawRabinFactorFrobenius
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.FieldDivision

/-! All-degree Frobenius coprimality is equivalent to irreducibility over
`F₂`. Both implications are proved from polynomial factorization and the
finite quotient-field Frobenius theorem. -/

namespace CorruptedFieldRecovery

open Polynomial Finset

/-- Universal common-divisor characterization of coprimality for polynomials. -/
def rawPolynomialCoprime (f g : Polynomial (ZMod 2)) : Prop :=
  ∀ c : Polynomial (ZMod 2), c ∣ f → c ∣ g → IsUnit c

/-- A monic polynomial of positive degree is irreducible exactly when it is
coprime to `X^(2^d)-X` for every `1 ≤ d ≤ degree/2`. -/
theorem monic_irreducible_iff_frobenius_coprime
    {f : Polynomial (ZMod 2)} (hmonic : f.Monic) (s : Nat)
    (hdegree : f.natDegree = s) (hs : 1 ≤ s) :
    Irreducible f ↔
      ∀ d, 1 ≤ d → d ≤ s / 2 →
        rawPolynomialCoprime f (X ^ (2 ^ d) - X) := by
  constructor
  · intro hirr d hdlo hdhi c hcf hcx
    by_contra hnotunit
    have hcne : c ≠ 0 := by
      intro hc
      subst c
      simp [hmonic.ne_zero] at hcf
    obtain ⟨q, hqirr, hqdiv⟩ :=
      WfDvdMonoid.exists_irreducible_factor hnotunit hcne
    have hqf : q ∣ f := hqdiv.trans hcf
    have hqassoc : Associated q f :=
      (hqirr.dvd_irreducible_iff_associated hirr).mp hqf
    have hfq : f ∣ q := hqassoc.symm.dvd
    have hqF : q ∣ X ^ (2 ^ d) - X := hqdiv.trans hcx
    have hfF : f ∣ X ^ (Nat.card (ZMod 2)) ^ d - X := by
      have hcard : Nat.card (ZMod 2) = 2 := by simp
      simpa [hcard] using hfq.trans hqF
    have hdiv := hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (n := d) hfF
    rw [hdegree] at hdiv
    have hsle : s ≤ d := Nat.le_of_dvd (by omega) hdiv
    omega
  · intro hcop
    rw [hmonic.irreducible_iff_natDegree']
    constructor
    · intro h
      rw [h, natDegree_one] at hdegree
      omega
    · intro g h hg hh hprod
      by_contra hnotmem
      have hmem : h.natDegree ∈ Ioc 0 (f.natDegree / 2) := hnotmem
      have hbounds : 0 < h.natDegree ∧ h.natDegree ≤ s / 2 := by
        have hmem' := Finset.mem_Ioc.mp hmem
        rw [hdegree] at hmem'
        exact hmem'
      have hnotunit : ¬ IsUnit h :=
        Polynomial.not_isUnit_of_natDegree_pos h hbounds.1
      obtain ⟨q, hqirr, hqdiv⟩ :=
        WfDvdMonoid.exists_irreducible_factor hnotunit hh.ne_zero
      let qmon := normalize q
      have hqne : q ≠ 0 := hqirr.ne_zero
      have hqmonic : qmon.Monic := by
        dsimp [qmon]
        exact Polynomial.monic_normalize hqne
      have hqassoc : Associated qmon q := by
        dsimp [qmon]
        exact normalize_associated q
      have hqmonirr : Irreducible qmon := hqassoc.symm.irreducible hqirr
      have hqmonDivH : qmon ∣ h := hqassoc.dvd.trans hqdiv
      have hdegreeNormalize : Polynomial.degree qmon = Polynomial.degree q := by
        dsimp [qmon]
        exact Polynomial.degree_normalize
      have hqmonPos : 0 < qmon.natDegree :=
        hqmonic.natDegree_pos_of_not_isUnit hqmonirr.not_isUnit
      have hqmonLe : qmon.natDegree ≤ s / 2 := by
        have hle := Polynomial.natDegree_le_of_dvd hqmonDivH hh.ne_zero
        omega
      have hdivHf : h ∣ f := by
        refine ⟨g, ?_⟩
        calc
          f = g * h := hprod.symm
          _ = h * g := mul_comm _ _
      have hqmonF : qmon ∣ f := hqmonDivH.trans hdivHf
      have hqmonFrob :=
        irreducible_dvd_X_pow_two_pow_natDegree hqmonirr hqmonic
      have hcopAtDegree := hcop qmon.natDegree hqmonPos hqmonLe
      exact hqmonirr.not_isUnit (hcopAtDegree qmon hqmonF hqmonFrob)

end CorruptedFieldRecovery
