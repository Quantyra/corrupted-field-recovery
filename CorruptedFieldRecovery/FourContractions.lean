import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Prod

/-! Algebraic core for the four-contraction field-identification route.

This file deliberately does not claim M2a coverage: the concrete determinant
contractions, their trace radicals, block extraction, and arbitrary sampled-basis
transport still have to be connected to the algebraic core below.
-/

namespace CorruptedFieldRecovery

/-- The finite-field trace pairing is nondegenerate in either argument. -/
theorem tracePairing_nondegenerate
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (scale : K) (hscale : scale ≠ 0) (x : K) (hx : x ≠ 0) :
    ∃ y : K, Algebra.trace (ZMod (ringChar K)) K (scale * x * y) ≠ 0 := by
  obtain ⟨y, hy⟩ := FiniteField.trace_to_zmod_nondegenerate K (mul_ne_zero hscale hx)
  exact ⟨y, by simpa [mul_assoc] using hy⟩

/-- The coordinate model for the clean three-dimensional field space. -/
abbrev FieldTriple (K : Type*) := K × K × K

/-- The determinant of three column vectors in the standard coordinates. -/
def fieldDet3 {K : Type*} [CommRing K]
    (x y z : FieldTriple K) : K :=
  x.1 * (y.2.1 * z.2.2 - y.2.2 * z.2.1) -
    y.1 * (x.2.1 * z.2.2 - x.2.2 * z.2.1) +
    z.1 * (x.2.1 * y.2.2 - x.2.2 * y.2.1)

def fieldBasis0 {K : Type*} [Zero K] [One K] : FieldTriple K := (1, 0, 0)
def fieldBasis1 {K : Type*} [Zero K] [One K] : FieldTriple K := (0, 1, 0)
def fieldBasis2 {K : Type*} [Zero K] [One K] : FieldTriple K := (0, 0, 1)

/-- The first clean contraction of the trace-determinant tensor. -/
noncomputable def fieldContraction0
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y fieldBasis0)

/-- The second clean contraction of the trace-determinant tensor. -/
noncomputable def fieldContraction1
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y fieldBasis1)

/-- The third clean contraction of the trace-determinant tensor. -/
noncomputable def fieldContraction2
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y fieldBasis2)

/-- The radical of the first standard contraction is exactly its K-coordinate
axis. This is the first concrete radical derivation needed for M2a. -/
theorem fieldContraction0_radical
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0) (x : FieldTriple K) :
    (∀ y, fieldContraction0 K c x y = 0) ↔ x.2.1 = 0 ∧ x.2.2 = 0 := by
  constructor
  · intro hx
    constructor
    · by_contra h1
      obtain ⟨t, ht⟩ := tracePairing_nondegenerate K c hc x.2.1 h1
      have hz := hx (0, 0, t)
      have hdet : fieldDet3 x (0, 0, t) fieldBasis0 = x.2.1 * t := by
        simp [fieldDet3, fieldBasis0]
      rw [fieldContraction0, hdet, ← mul_assoc] at hz
      exact ht hz
    · by_contra h2
      obtain ⟨t, ht⟩ := tracePairing_nondegenerate K c hc (-x.2.2) (by simpa using h2)
      have hz := hx (0, t, 0)
      have hdet : fieldDet3 x (0, t, 0) fieldBasis0 = -x.2.2 * t := by
        simp [fieldDet3, fieldBasis0]
      rw [fieldContraction0, hdet, ← mul_assoc] at hz
      exact ht hz
  · rintro ⟨h1, h2⟩ y
    simp [fieldContraction0, fieldDet3, fieldBasis0, h1, h2]

/-- The radical of the second standard contraction is its K-coordinate axis. -/
theorem fieldContraction1_radical
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0) (x : FieldTriple K) :
    (∀ y, fieldContraction1 K c x y = 0) ↔ x.1 = 0 ∧ x.2.2 = 0 := by
  constructor
  · intro hx
    constructor
    · by_contra h0
      obtain ⟨t, ht⟩ := tracePairing_nondegenerate K c hc (-x.1) (by simpa using h0)
      have hz := hx (0, 0, t)
      have hdet : fieldDet3 x (0, 0, t) fieldBasis1 = -x.1 * t := by
        simp [fieldDet3, fieldBasis1]
      rw [fieldContraction1, hdet, ← mul_assoc] at hz
      exact ht hz
    · by_contra h2
      obtain ⟨t, ht⟩ := tracePairing_nondegenerate K c hc x.2.2 h2
      have hz := hx (t, 0, 0)
      have hdet : fieldDet3 x (t, 0, 0) fieldBasis1 = x.2.2 * t := by
        simp [fieldDet3, fieldBasis1]
        ring
      rw [fieldContraction1, hdet, ← mul_assoc] at hz
      exact ht hz
  · rintro ⟨h0, h2⟩ y
    simp [fieldContraction1, fieldDet3, fieldBasis1, h0, h2]

/-- The radical of the third standard contraction is its K-coordinate axis. -/
theorem fieldContraction2_radical
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0) (x : FieldTriple K) :
    (∀ y, fieldContraction2 K c x y = 0) ↔ x.1 = 0 ∧ x.2.1 = 0 := by
  constructor
  · intro hx
    constructor
    · by_contra h0
      obtain ⟨t, ht⟩ := tracePairing_nondegenerate K c hc x.1 h0
      have hz := hx (0, t, 0)
      have hdet : fieldDet3 x (0, t, 0) fieldBasis2 = x.1 * t := by
        simp [fieldDet3, fieldBasis2]
      rw [fieldContraction2, hdet, ← mul_assoc] at hz
      exact ht hz
    · by_contra h1
      obtain ⟨t, ht⟩ := tracePairing_nondegenerate K c hc (-x.2.1) (by simpa using h1)
      have hz := hx (t, 0, 0)
      have hdet : fieldDet3 x (t, 0, 0) fieldBasis2 = -x.2.1 * t := by
        simp [fieldDet3, fieldBasis2]
        ring
      rw [fieldContraction2, hdet, ← mul_assoc] at hz
      exact ht hz
  · rintro ⟨h0, h1⟩ y
    simp [fieldContraction2, fieldDet3, fieldBasis2, h0, h1]

/-- Balancing the first three contractions forces preservation of each of the
three K-coordinate axes. This derives the block-diagonal constraint on an
arbitrary binary-linear endomorphism; it does not assume that constraint. -/
theorem balanced_first_three_preserves_axes
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0)
    (T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K)
    (h0 : ∀ x y, fieldContraction0 K c (T x) y = fieldContraction0 K c x (T y))
    (h1 : ∀ x y, fieldContraction1 K c (T x) y = fieldContraction1 K c x (T y))
    (h2 : ∀ x y, fieldContraction2 K c (T x) y = fieldContraction2 K c x (T y)) :
    (∀ t, (T (t, 0, 0)).2.1 = 0 ∧ (T (t, 0, 0)).2.2 = 0) ∧
    (∀ t, (T (0, t, 0)).1 = 0 ∧ (T (0, t, 0)).2.2 = 0) ∧
    (∀ t, (T (0, 0, t)).1 = 0 ∧ (T (0, 0, t)).2.1 = 0) := by
  constructor
  · intro t
    apply (fieldContraction0_radical K c hc (T (t, 0, 0))).mp
    intro y
    rw [h0]
    exact (fieldContraction0_radical K c hc (t, 0, 0)).mpr (by simp) (T y)
  constructor
  · intro t
    apply (fieldContraction1_radical K c hc (T (0, t, 0))).mp
    intro y
    rw [h1]
    exact (fieldContraction1_radical K c hc (0, t, 0)).mpr (by simp) (T y)
  · intro t
    apply (fieldContraction2_radical K c hc (T (0, 0, t))).mp
    intro y
    rw [h2]
    exact (fieldContraction2_radical K c hc (0, 0, t)).mpr (by simp) (T y)

/-- The first coordinate-axis embedding as an F-linear map. -/
def fieldAxis0 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] :
    K →ₗ[F] FieldTriple K where
  toFun t := (t, 0, 0)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

/-- The second coordinate-axis embedding as an F-linear map. -/
def fieldAxis1 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] :
    K →ₗ[F] FieldTriple K where
  toFun t := (0, t, 0)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

/-- The third coordinate-axis embedding as an F-linear map. -/
def fieldAxis2 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] :
    K →ₗ[F] FieldTriple K where
  toFun t := (0, 0, t)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

def fieldCoordinate0 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] :
    FieldTriple K →ₗ[F] K := LinearMap.fst F K (K × K)

def fieldCoordinate1 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] :
    FieldTriple K →ₗ[F] K :=
  (LinearMap.fst F K K).comp (LinearMap.snd F K (K × K))

def fieldCoordinate2 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K] :
    FieldTriple K →ₗ[F] K :=
  (LinearMap.snd F K K).comp (LinearMap.snd F K (K × K))

/-- The three binary-linear coordinate blocks induced by an endomorphism that
preserves the three field-coordinate axes. -/
def fieldBlock0 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K]
    (T : FieldTriple K →ₗ[F] FieldTriple K) : K →ₗ[F] K :=
  (fieldCoordinate0 F K).comp (T.comp (fieldAxis0 F K))

def fieldBlock1 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K]
    (T : FieldTriple K →ₗ[F] FieldTriple K) : K →ₗ[F] K :=
  (fieldCoordinate1 F K).comp (T.comp (fieldAxis1 F K))

def fieldBlock2 (F K : Type*) [CommSemiring F] [Field K] [Algebra F K]
    (T : FieldTriple K →ₗ[F] FieldTriple K) : K →ₗ[F] K :=
  (fieldCoordinate2 F K).comp (T.comp (fieldAxis2 F K))

/-- Axis preservation, derived from the first three balances, implies an actual
block-diagonal expression for every balanced endomorphism. -/
theorem balanced_first_three_block_form
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0)
    (T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K)
    (h0 : ∀ x y, fieldContraction0 K c (T x) y = fieldContraction0 K c x (T y))
    (h1 : ∀ x y, fieldContraction1 K c (T x) y = fieldContraction1 K c x (T y))
    (h2 : ∀ x y, fieldContraction2 K c (T x) y = fieldContraction2 K c x (T y)) :
    ∀ x, T x = (fieldBlock0 (ZMod (ringChar K)) K T x.1,
      fieldBlock1 (ZMod (ringChar K)) K T x.2.1,
      fieldBlock2 (ZMod (ringChar K)) K T x.2.2) := by
  have haxes := balanced_first_three_preserves_axes K c hc T h0 h1 h2
  have ht0 (t : K) : T (t, 0, 0) = (fieldBlock0 (ZMod (ringChar K)) K T t, 0, 0) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact haxes.1 t |>.1
      · exact haxes.1 t |>.2
  have ht1 (t : K) : T (0, t, 0) = (0, fieldBlock1 (ZMod (ringChar K)) K T t, 0) := by
    apply Prod.ext
    · exact haxes.2.1 t |>.1
    · apply Prod.ext
      · rfl
      · exact haxes.2.1 t |>.2
  have ht2 (t : K) : T (0, 0, t) = (0, 0, fieldBlock2 (ZMod (ringChar K)) K T t) := by
    apply Prod.ext
    · exact haxes.2.2 t |>.1
    · apply Prod.ext
      · exact haxes.2.2 t |>.2
      · rfl
  intro x
  have hx : x = (x.1, 0, 0) + (0, x.2.1, 0) + (0, 0, x.2.2) := by
    rcases x with ⟨x0, x1, x2⟩
    ext <;> simp
  rw [hx, map_add, map_add, ht0, ht1, ht2]
  simp

/-- The trace pairing used in the off-diagonal contraction equations. -/
noncomputable def fieldTracePair
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c x y : K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * (x * y))

/-- The actual first three balance equations, after the axis-derived block
decomposition, become three trace-pairing adjoint relations. -/
theorem balanced_first_three_pair_relations
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0)
    (T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K)
    (h0 : ∀ x y, fieldContraction0 K c (T x) y = fieldContraction0 K c x (T y))
    (h1 : ∀ x y, fieldContraction1 K c (T x) y = fieldContraction1 K c x (T y))
    (h2 : ∀ x y, fieldContraction2 K c (T x) y = fieldContraction2 K c x (T y)) :
    (∀ u v, fieldTracePair K c (fieldBlock1 (ZMod (ringChar K)) K T u) v =
      fieldTracePair K c u (fieldBlock2 (ZMod (ringChar K)) K T v)) ∧
    (∀ u v, fieldTracePair K c (fieldBlock2 (ZMod (ringChar K)) K T u) v =
      fieldTracePair K c u (fieldBlock0 (ZMod (ringChar K)) K T v)) ∧
    (∀ u v, fieldTracePair K c (fieldBlock0 (ZMod (ringChar K)) K T u) v =
      fieldTracePair K c u (fieldBlock1 (ZMod (ringChar K)) K T v)) := by
  have hblock := balanced_first_three_block_form K c hc T h0 h1 h2
  constructor
  · intro u v
    have h := h0 (0, u, 0) (0, 0, v)
    rw [hblock (0, u, 0), hblock (0, 0, v)] at h
    simpa [fieldTracePair, fieldContraction0, fieldDet3, fieldBasis0,
      fieldBlock0, fieldBlock1, fieldBlock2, fieldCoordinate0, fieldCoordinate1,
      fieldCoordinate2, fieldAxis0, fieldAxis1, fieldAxis2] using h
  constructor
  · intro u v
    have h := h1 (0, 0, u) (v, 0, 0)
    rw [hblock (0, 0, u), hblock (v, 0, 0)] at h
    simpa [fieldTracePair, fieldContraction1, fieldDet3, fieldBasis1,
      fieldBlock0, fieldBlock1, fieldBlock2, fieldCoordinate0, fieldCoordinate1,
      fieldCoordinate2, fieldAxis0, fieldAxis1, fieldAxis2, mul_comm] using h
  · intro u v
    have h := h2 (u, 0, 0) (0, v, 0)
    rw [hblock (u, 0, 0), hblock (0, v, 0)] at h
    simpa [fieldTracePair, fieldContraction2, fieldDet3, fieldBasis2,
      fieldBlock0, fieldBlock1, fieldBlock2, fieldCoordinate0, fieldCoordinate1,
      fieldCoordinate2, fieldAxis0, fieldAxis1, fieldAxis2] using h

/-- Nondegeneracy of the finite-field trace pairing makes equality in its
second argument detectable by pairing against every first argument. -/
theorem fieldTracePair_right_injective
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0) {x y : K}
    (h : ∀ z, fieldTracePair K c z x = fieldTracePair K c z y) : x = y := by
  by_contra hxy
  obtain ⟨z, hz⟩ := tracePairing_nondegenerate K c hc (x - y) (sub_ne_zero.mpr hxy)
  have hring : c * ((x - y) * z) = c * (z * x) - c * (z * y) := by ring
  have htrace := congrArg (Algebra.trace (ZMod (ringChar K)) K) hring
  rw [map_sub] at htrace
  have hp := h z
  dsimp [fieldTracePair] at hp
  rw [hp, sub_self] at htrace
  exact hz (by simpa [mul_assoc] using htrace)

/-- The three off-diagonal trace equations force all binary-linear blocks to
coincide, and the common block is self-adjoint for the actual trace pairing. -/
theorem three_pair_relations_common_selfadjoint
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0)
    (A0 A1 A2 : K →ₗ[ZMod (ringChar K)] K)
    (h12 : ∀ u v, fieldTracePair K c (A1 u) v = fieldTracePair K c u (A2 v))
    (h23 : ∀ u v, fieldTracePair K c (A2 u) v = fieldTracePair K c u (A0 v))
    (h01 : ∀ u v, fieldTracePair K c (A0 u) v = fieldTracePair K c u (A1 v)) :
    ∃ A : K →ₗ[ZMod (ringChar K)] K,
      A0 = A ∧ A1 = A ∧ A2 = A ∧
      (∀ u v, fieldTracePair K c (A u) v = fieldTracePair K c u (A v)) := by
  have hA01 : A1 = A0 := by
    ext v
    apply fieldTracePair_right_injective K c hc
    intro u
    calc
      fieldTracePair K c u (A1 v) = fieldTracePair K c (A1 v) u := by
        simp [fieldTracePair, mul_comm]
      _ = fieldTracePair K c v (A2 u) := h12 v u
      _ = fieldTracePair K c (A2 u) v := by simp [fieldTracePair, mul_comm]
      _ = fieldTracePair K c u (A0 v) := h23 u v
  have hself : ∀ u v, fieldTracePair K c (A0 u) v = fieldTracePair K c u (A0 v) := by
    intro u v
    simpa [hA01] using h01 u v
  have hA2 : A2 = A0 := by
    ext v
    apply fieldTracePair_right_injective K c hc
    intro u
    calc
      fieldTracePair K c u (A2 v) = fieldTracePair K c (A1 u) v := (h12 u v).symm
      _ = fieldTracePair K c (A0 u) v := by rw [hA01]
      _ = fieldTracePair K c u (A0 v) := hself u v
  exact ⟨A0, rfl, hA01, hA2, hself⟩

/-- An F-linear map on a finite field that commutes with multiplication by an
algebra generator is multiplication by its value at one. This is the scalar
recognition step used after the first three contractions identify one common
self-adjoint block map. -/
theorem linearMap_scalar_of_commutes_generator
    (F K : Type*) [CommRing F] [Field K] [Algebra F K]
    (A : K →ₗ[F] K) (α : K)
    (hgen : Algebra.adjoin F {α} = ⊤)
    (hcomm : ∀ x : K, A (α * x) = α * A x) :
    ∀ x : K, A x = A 1 * x := by
  have hmul : ∀ r : K, r ∈ Algebra.adjoin F {α} → ∀ x : K,
      A (r * x) = r * A x := by
    intro r hr
    rw [Algebra.mem_adjoin_iff] at hr
    induction hr using Subring.closure_induction with
    | mem r hr =>
        rcases hr with ⟨t, rfl⟩ | hr
        · intro x
          calc
            A ((algebraMap F K t) * x) = A (t • x) := by rw [← Algebra.smul_def]
            _ = t • A x := map_smul A t x
            _ = (algebraMap F K t) * A x := Algebra.smul_def t (A x)
        · have hr : r = α := by simpa using hr
          subst r
          exact hcomm
    | zero =>
        intro x
        simp
    | one =>
        intro x
        simp
    | add r s hr hs ihr ihs =>
        intro x
        rw [add_mul, map_add, ihr x, ihs x, add_mul]
    | neg r hr ihr =>
        intro x
        rw [neg_mul, map_neg, ihr x, neg_mul]
    | mul r s hr hs ihr ihs =>
        intro x
        rw [mul_assoc, ihr (s * x), ihs x, mul_assoc]
  have htop : ∀ r : K, ∀ x : K, A (r * x) = r * A x := by
    intro r x
    apply hmul r
    rw [hgen]
    trivial
  intro x
  simpa [mul_comm] using (htop x 1)

end CorruptedFieldRecovery
