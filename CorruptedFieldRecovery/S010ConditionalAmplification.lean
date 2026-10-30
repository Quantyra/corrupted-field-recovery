import CorruptedFieldRecovery.S010ModeImageRank
import CorruptedFieldRecovery.S010ModeImageTrialBound
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- Repeated independent tapes with at least one member in `S`. -/
def repeatedSuccessSet {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (n : Nat) : Finset (Fin n → α) :=
  Finset.univ.filter fun run => ∃ i, run i ∈ S

/-- Exact finite count for at least one success in `n` independent uniform
draws. The complement consists of functions into the one-trial complement. -/
theorem repeatedSuccessSet_card {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (n : Nat) :
    (repeatedSuccessSet S n).card =
      (Fintype.card α) ^ n - (Fintype.card α - S.card) ^ n := by
  classical
  let BadRun := {run : Fin n → α // ∀ i, run i ∉ S}
  let BadValue := {x : α // x ∉ S}
  let e : BadRun ≃ (Fin n → BadValue) := {
    toFun := fun run i => ⟨run.val i, run.property i⟩
    invFun := fun f => ⟨fun i => (f i).val, fun i => (f i).property⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext i
      rfl
    right_inv := by
      intro f
      funext i
      apply Subtype.ext
      rfl }
  have hbadValue : Fintype.card BadValue = Fintype.card α - S.card := by
    change Fintype.card {x : α // x ∉ S} = Fintype.card α - S.card
    rw [Fintype.card_subtype_compl (p := fun x : α => x ∈ S)]
    have hS : Fintype.card {x : α // x ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hS]
  have hbadRun : Fintype.card BadRun = (Fintype.card α - S.card) ^ n := by
    calc
      Fintype.card BadRun = Fintype.card (Fin n → BadValue) := Fintype.card_congr e
      _ = Fintype.card BadValue ^ n := by simp
      _ = (Fintype.card α - S.card) ^ n := by rw [hbadValue]
  have hbadFinset :
      (Finset.univ.filter (fun run : Fin n → α => ∀ i, run i ∉ S)).card =
        Fintype.card BadRun := by
    change (Finset.univ.filter (fun run : Fin n → α => ∀ i, run i ∉ S)).card =
      Fintype.card {run : Fin n → α // ∀ i, run i ∉ S}
    symm
    rw [Fintype.card_subtype]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → α)))
    (fun run : Fin n → α => ∃ i, run i ∈ S)
  have hcard : (repeatedSuccessSet S n).card +
      (Finset.univ.filter (fun run : Fin n → α => ∀ i, run i ∉ S)).card =
        (Fintype.card α) ^ n := by
    simpa [repeatedSuccessSet, not_exists, Fintype.card_fun] using hpartition
  rw [hbadFinset, hbadRun] at hcard
  omega

/-- Amplification from an explicit one-trial lower count. `C` is the inverse
probability denominator: if `C * |S| ≥ |α|`, then the repeated success count
has the standard `1-(1-1/C)^n` lower bound. -/
theorem repeatedSuccessSet_amplification {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (C n : Nat) (hCpos : 0 < C)
    (htrial : C * S.card ≥ Fintype.card α) :
    C ^ n * (repeatedSuccessSet S n).card ≥
      (C ^ n - (C - 1) ^ n) * (Fintype.card α) ^ n := by
  have hM : S.card ≤ Fintype.card α := Finset.card_le_univ S
  have hfail : C * (Fintype.card α - S.card) ≤
      (C - 1) * Fintype.card α := by
    have hCsub : C - 1 + 1 = C := Nat.sub_add_cancel (by omega : 1 ≤ C)
    have hMsub : (Fintype.card α - S.card) + S.card = Fintype.card α :=
      Nat.sub_add_cancel hM
    nlinarith [htrial, hCsub, hMsub]
  have hpow := Nat.pow_le_pow_left hfail n
  have hpow' : C ^ n * (Fintype.card α - S.card) ^ n ≤
      (C - 1) ^ n * (Fintype.card α) ^ n := by
    calc
      C ^ n * (Fintype.card α - S.card) ^ n =
          (C * (Fintype.card α - S.card)) ^ n := by rw [Nat.mul_pow]
      _ ≤ ((C - 1) * Fintype.card α) ^ n := hpow
      _ = (C - 1) ^ n * (Fintype.card α) ^ n := by rw [Nat.mul_pow]
  rw [repeatedSuccessSet_card]
  calc
    C ^ n * ((Fintype.card α) ^ n - (Fintype.card α - S.card) ^ n) =
        C ^ n * (Fintype.card α) ^ n - C ^ n * (Fintype.card α - S.card) ^ n :=
      Nat.mul_sub_left_distrib _ _ _
    _ ≥ C ^ n * (Fintype.card α) ^ n - (C - 1) ^ n * (Fintype.card α) ^ n :=
      Nat.sub_le_sub_left hpow' _
    _ = (C ^ n - (C - 1) ^ n) * (Fintype.card α) ^ n := by
      rw [Nat.sub_mul]

/-- Conditional one-trial success count for the actual mode-image tape event.
The premise `hgoodSuccess` is the explicit missing algorithmic bridge: every
member of the already-counted good-tape set must make the concrete recovery
procedure succeed. -/
theorem modeImage_actual_success_count_of_good_event
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]
    {s R r : Nat} (hs : Module.finrank BinaryField K = s)
    (hsize : 2 * R + 5 ≤ s) (hrR : r ≤ R)
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (hr : Module.finrank BinaryField (modeImageSemanticSupport Q E) = r)
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (Success : Finset (FiveWordTape s))
    (hgoodSuccess : actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) (modeImageSemanticSupport Q E) b ⊆ Success) :
    2 ^ (4 * R + 3) * Success.card ≥ Fintype.card (FiveWordTape s) := by
  have hcount := modeImage_actual_one_trial_bound hs hsize hrR Q E hr b
  rw [card_fiveWordTape]
  exact le_trans hcount (Nat.mul_le_mul_left _ (Finset.card_le_card hgoodSuccess))

end

end CorruptedFieldRecovery
