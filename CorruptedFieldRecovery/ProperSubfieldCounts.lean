import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A degree-indexed root bound for non-generators of a finite binary field.

The union bound is over degrees, not an assumed count of intermediate fields.
For a proper simple intermediate field of degree d, its elements are roots
of X^(2^d)-X; the polynomial degree bounds that root set by 2^d.
-/

namespace CorruptedFieldRecovery

open Polynomial

noncomputable section

abbrev BinaryField := ZMod 2

variable (K : Type*) [Field K] [Finite K]
  [Algebra BinaryField K] [FiniteDimensional BinaryField K]

local instance : Fintype K := Fintype.ofFinite K

local instance : DecidableEq K := Classical.decEq K

def properDegrees : Finset Nat :=
  (Finset.range (Module.finrank BinaryField K)).filter fun d => d ∣ Module.finrank BinaryField K

def frobeniusRootSet (d : Nat) : Finset K :=
  Finset.univ.filter fun x => x ^ (2 ^ d) = x

def nonGenerators : Finset K :=
  Finset.univ.filter fun x =>
    IntermediateField.adjoin BinaryField ({x} : Set K) ≠ ⊤

omit [Algebra BinaryField K] [FiniteDimensional BinaryField K] in
theorem card_frobeniusRootSet_le (d : Nat) (hd : 0 < d) :
    (frobeniusRootSet K d).card ≤ 2 ^ d := by
  classical
  let p : K[X] := X ^ (2 ^ d) - X
  have hpow : 1 < 2 ^ d := Nat.one_lt_pow (Nat.ne_of_gt hd) (by decide)
  have hdeg : p.natDegree = 2 ^ d := by
    dsimp [p]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq K hpow
  have hp : p ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt
    rw [hdeg]
    exact Nat.pos_of_ne_zero (by positivity)
  rw [← hdeg]
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  have hxmem : x ∈ frobeniusRootSet K d := by simpa using hx
  have hxpow : x ^ (2 ^ d) = x := (Finset.mem_filter.mp hxmem).2
  rw [Polynomial.mem_roots hp]
  simpa only [p, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X] using (sub_eq_zero.mpr hxpow)

omit [Algebra BinaryField K] [FiniteDimensional BinaryField K] in
theorem card_biUnion_frobeniusRootSet_le (D : Finset Nat)
    (hD : ∀ d ∈ D, 0 < d) :
    (D.biUnion fun d => frobeniusRootSet K d).card ≤ ∑ d ∈ D, 2 ^ d := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d D hd ih =>
      rw [Finset.biUnion_insert]
      calc
        (frobeniusRootSet K d ∪ D.biUnion fun e => frobeniusRootSet K e).card ≤
            (frobeniusRootSet K d).card + (D.biUnion fun e => frobeniusRootSet K e).card :=
          Finset.card_union_le _ _
        _ ≤ 2 ^ d + ∑ e ∈ D, 2 ^ e := by
          apply Nat.add_le_add
          · exact card_frobeniusRootSet_le K d (hD d (by simp))
          · apply ih
            intro e he
            exact hD e (Finset.mem_insert_of_mem he)
        _ = ∑ e ∈ insert d D, 2 ^ e := by simp [hd]

theorem nonGenerator_mem_degree_root_union (x : K)
    (hx : x ∈ nonGenerators K) :
    x ∈ (properDegrees K).biUnion fun d => frobeniusRootSet K d := by
  classical
  simp only [nonGenerators, Finset.mem_filter] at hx
  rcases hx with ⟨_, hx⟩
  let E : IntermediateField BinaryField K := IntermediateField.adjoin BinaryField ({x} : Set K)
  let s := Module.finrank BinaryField K
  let d := Module.finrank BinaryField E
  have hE : E ≠ ⊤ := by simpa [E] using hx
  have hdiv : d ∣ s := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (K := BinaryField) (F := E) (E := (⊤ : IntermediateField BinaryField K)) le_top
    simpa [d, s, IntermediateField.finrank_top'] using h
  have hnot : d ≠ s := by
    intro hds
    have hEq : E = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
      simpa [d, s, IntermediateField.finrank_top'] using hds)
    exact hE hEq
  have hdpos : 0 < d := Module.finrank_pos
  have hspos : 0 < s := Module.finrank_pos
  have hdle : d ≤ s := Nat.le_of_dvd hspos hdiv
  have hdlts : d < s := by omega
  have hdD : d ∈ properDegrees K := by
    simp [properDegrees, s, hdiv, hdlts]
  haveI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 2 ^ d := by
    rw [Module.card_eq_pow_finrank (K := BinaryField) (V := E), ZMod.card]
  have hpowE : (⟨x, IntermediateField.mem_adjoin_simple_self BinaryField x⟩ : E) ^
      Fintype.card E = ⟨x, IntermediateField.mem_adjoin_simple_self BinaryField x⟩ :=
    FiniteField.pow_card _
  have hroot : x ^ (2 ^ d) = x := by
    have h := congrArg (fun y : E => (y : K)) hpowE
    simpa [hcardE] using h
  exact Finset.mem_biUnion.2 ⟨d, hdD, by simp [frobeniusRootSet, hroot]⟩

theorem nonGenerators_subset_degree_root_union :
    nonGenerators K ⊆ (properDegrees K).biUnion fun d => frobeniusRootSet K d := by
  intro x hx
  exact nonGenerator_mem_degree_root_union K x hx

theorem card_nonGenerators_le_proper_degree_sum :
    (nonGenerators K).card ≤ ∑ d ∈ properDegrees K, 2 ^ d := by
  classical
  calc
    (nonGenerators K).card ≤
        ((properDegrees K).biUnion fun d => frobeniusRootSet K d).card :=
      Finset.card_le_card (nonGenerators_subset_degree_root_union K)
    _ ≤ ∑ d ∈ properDegrees K, 2 ^ d :=
      card_biUnion_frobeniusRootSet_le (K := K) (properDegrees K) (by
        intro d hd
        simp [properDegrees] at hd
        exact Nat.pos_of_dvd_of_pos hd.2 (Module.finrank_pos))

end

end CorruptedFieldRecovery
