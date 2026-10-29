import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Determinant

/-! Algebraic core for the four-contraction field-identification route.

This file deliberately does not claim M2a coverage: the concrete determinant
contractions, their trace radicals, block extraction, and arbitrary sampled-basis
transport still have to be connected to the algebraic core below.
-/

namespace CorruptedFieldRecovery

open Module

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

/-- The coordinate equivalence from the nested product `K × K × K` to the
three-coordinate function space. -/
def fieldTripleEquivPi (K : Type*) [Field K] :
    FieldTriple K ≃ₗ[K] (Fin 3 → K) where
  toFun x i := if i = 0 then x.1 else if i = 1 then x.2.1 else x.2.2
  invFun f := (f 0, f 1, f 2)
  left_inv x := by
    rcases x with ⟨x₀, x₁, x₂⟩
    rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' r x := by
    funext i
    fin_cases i <;> simp

/-- The standard basis of the nested product `K × K × K`. -/
noncomputable def fieldTripleStandardBasis (K : Type*) [Field K] :
    Basis (Fin 3) K (FieldTriple K) :=
  Basis.ofEquivFun (fieldTripleEquivPi K)

@[simp] theorem fieldTripleStandardBasis_zero (K : Type*) [Field K] :
    fieldTripleStandardBasis K 0 = fieldBasis0 := by
  simp [fieldTripleStandardBasis, fieldTripleEquivPi, fieldBasis0,
    Basis.coe_ofEquivFun]

@[simp] theorem fieldTripleStandardBasis_one (K : Type*) [Field K] :
    fieldTripleStandardBasis K 1 = fieldBasis1 := by
  simp [fieldTripleStandardBasis, fieldTripleEquivPi, fieldBasis1,
    Basis.coe_ofEquivFun]

@[simp] theorem fieldTripleStandardBasis_two (K : Type*) [Field K] :
    fieldTripleStandardBasis K 2 = fieldBasis2 := by
  simp [fieldTripleStandardBasis, fieldTripleEquivPi, fieldBasis2,
    Basis.coe_ofEquivFun]

/-- The coordinates determined by a sampled `K`-basis of the physical triple. -/
noncomputable def sampledBasisCoordinateEquiv
    (K : Type*) [Field K] (b : Basis (Fin 3) K (FieldTriple K)) :
    FieldTriple K ≃ₗ[K] FieldTriple K :=
  b.equiv (fieldTripleStandardBasis K) (Equiv.refl (Fin 3))

@[simp] theorem sampledBasisCoordinateEquiv_apply_basis
    (K : Type*) [Field K] (b : Basis (Fin 3) K (FieldTriple K)) (i : Fin 3) :
    sampledBasisCoordinateEquiv K b (b i) = fieldTripleStandardBasis K i := by
  simp [sampledBasisCoordinateEquiv]

/-- The determinant of the sampled basis relative to the standard triple basis. -/
noncomputable def sampledBasisDeterminant
    (K : Type*) [Field K] (b : Basis (Fin 3) K (FieldTriple K)) : K :=
  (fieldTripleStandardBasis K).det b

/-- The sampled-basis determinant factor is nonzero. -/
theorem sampledBasisDeterminant_ne_zero
    (K : Type*) [Field K] (b : Basis (Fin 3) K (FieldTriple K)) :
    sampledBasisDeterminant K b ≠ 0 := by
  exact (fieldTripleStandardBasis K).isUnit_det b |>.ne_zero

/-- The explicit three-coordinate determinant is the determinant form of the
standard product basis. -/
theorem fieldDet3_eq_standardBasis_det
    (K : Type*) [Field K] (x y z : FieldTriple K) :
    fieldDet3 x y z = (fieldTripleStandardBasis K).det ![x, y, z] := by
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp [Basis.toMatrix, fieldTripleStandardBasis,
    Basis.ofEquivFun_repr_apply, fieldTripleEquivPi, fieldDet3]
  ring

/-- Determinants in sampled coordinates equal ambient determinants divided by
the sampled basis factor. Equivalently, in the standard coordinate model the
ambient coefficient `c` becomes `c * sampledBasisDeterminant`. -/
theorem fieldDet3_sampledBasis_change
    (K : Type*) [Field K] (b : Basis (Fin 3) K (FieldTriple K))
    (x y z : FieldTriple K) :
    fieldDet3 x y z = sampledBasisDeterminant K b *
      fieldDet3 (sampledBasisCoordinateEquiv K b x)
        (sampledBasisCoordinateEquiv K b y)
        (sampledBasisCoordinateEquiv K b z) := by
  let e := fieldTripleStandardBasis K
  let q := sampledBasisCoordinateEquiv K b
  have hqb (i : Fin 3) : q (b i) = e i := by
    simp [q, e, sampledBasisCoordinateEquiv]
  have hmap : e.det.compLinearMap q.toLinearMap = b.det := by
    apply Module.Basis.ext_alternating b
    intro v hv
    let σ : Equiv.Perm (Fin 3) :=
      Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
    have hv' : v = σ := by
      funext i
      rfl
    rw [hv']
    rw [AlternatingMap.compLinearMap_apply]
    have hqv : (fun i : Fin 3 => q (b (σ i))) = fun i => e (σ i) := by
      funext i
      exact hqb (σ i)
    change e.det (fun i => q (b (σ i))) = b.det (fun i => b (σ i))
    rw [hqv]
    change e.det (e ∘ σ) = b.det (b ∘ σ)
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
    simp only [Basis.det_self]
  have hdet : e.det = e.det b • b.det :=
    AlternatingMap.eq_smul_basis_det (e := b) e.det
  have hcoord : b.det ![x, y, z] = e.det ![q x, q y, q z] := by
    have h := congrArg (fun f => f ![x, y, z]) hmap
    simpa [AlternatingMap.compLinearMap_apply] using h.symm
  calc
    fieldDet3 x y z = e.det ![x, y, z] := fieldDet3_eq_standardBasis_det K x y z
    _ = (e.det b) * b.det ![x, y, z] := by
      have h := congrArg (fun f => f ![x, y, z]) hdet
      simpa [smul_eq_mul] using h
    _ = (e.det b) * e.det ![q x, q y, q z] := by rw [hcoord]
    _ = (e.det b) * fieldDet3 (q x) (q y) (q z) := by
      rw [fieldDet3_eq_standardBasis_det]
    _ = _ := rfl

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

/-- The fourth clean contraction, with its three field coefficients retained
inside the trace. -/
noncomputable def fieldContraction4
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c a b d : K) (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y (a, b, d))

/-- Coordinatewise multiplication by a scalar on the three-dimensional field
space. -/
def fieldScalarTriple {K : Type*} [Semiring K]
    (k : K) (x : FieldTriple K) : FieldTriple K :=
  (k * x.1, k * x.2.1, k * x.2.2)

theorem fieldScalarTriple_eq_smul {K : Type*} [Semiring K]
    (k : K) (x : FieldTriple K) : fieldScalarTriple k x = k • x := by
  rcases x with ⟨x0, x1, x2⟩
  simp [fieldScalarTriple]

theorem fieldDet3_smul_left {K : Type*} [CommRing K]
    (k : K) (x y z : FieldTriple K) :
    fieldDet3 (k • x) y z = k * fieldDet3 x y z := by
  rcases x with ⟨x0, x1, x2⟩
  simp [fieldDet3, smul_eq_mul]
  ring

theorem fieldDet3_smul_right {K : Type*} [CommRing K]
    (k : K) (x y z : FieldTriple K) :
    fieldDet3 x (k • y) z = k * fieldDet3 x y z := by
  rcases y with ⟨y0, y1, y2⟩
  simp [fieldDet3, smul_eq_mul]
  ring

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

/-- The first three actual contractions derive a block-diagonal action by one
common self-adjoint binary-linear map. -/
theorem first_three_common_block
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (hc : c ≠ 0)
    (T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K)
    (h0 : ∀ x y, fieldContraction0 K c (T x) y = fieldContraction0 K c x (T y))
    (h1 : ∀ x y, fieldContraction1 K c (T x) y = fieldContraction1 K c x (T y))
    (h2 : ∀ x y, fieldContraction2 K c (T x) y = fieldContraction2 K c x (T y)) :
    ∃ A : K →ₗ[ZMod (ringChar K)] K,
      (∀ x, T x = (A x.1, A x.2.1, A x.2.2)) ∧
      (∀ u v, fieldTracePair K c (A u) v = fieldTracePair K c u (A v)) := by
  have hpair := balanced_first_three_pair_relations K c hc T h0 h1 h2
  obtain ⟨A, hA0, hA1, hA2, hself⟩ :=
    three_pair_relations_common_selfadjoint K c hc
      (fieldBlock0 (ZMod (ringChar K)) K T)
      (fieldBlock1 (ZMod (ringChar K)) K T)
      (fieldBlock2 (ZMod (ringChar K)) K T)
      hpair.1 hpair.2.1 hpair.2.2
  refine ⟨A, ?_, hself⟩
  intro x
  have hx := balanced_first_three_block_form K c hc T h0 h1 h2 x
  simpa [hA0, hA1, hA2] using hx

/-- The fourth balance equations yield coefficient-weighted pairings. Each
coefficient remains inside the trace; no F-linear combination of the
F-valued contraction forms is asserted. -/
theorem fourth_balance_weighted_pairs
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c a b d : K) (A : K →ₗ[ZMod (ringChar K)] K)
    (T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K)
    (hform : ∀ x, T x = (A x.1, A x.2.1, A x.2.2))
    (h4 : ∀ x y, fieldContraction4 K c a b d (T x) y =
      fieldContraction4 K c a b d x (T y)) :
    (∀ u v, fieldTracePair K c (A u) (a * v) =
      fieldTracePair K c u (a * A v)) ∧
    (∀ u v, fieldTracePair K c (A u) (b * v) =
      fieldTracePair K c u (b * A v)) ∧
    (∀ u v, fieldTracePair K c (A u) (d * v) =
      fieldTracePair K c u (d * A v)) := by
  constructor
  · intro u v
    have h := h4 (0, u, 0) (0, 0, v)
    rw [hform (0, u, 0), hform (0, 0, v)] at h
    simpa [fieldTracePair, fieldContraction4, fieldDet3, mul_assoc, mul_comm,
      mul_left_comm] using h
  constructor
  · intro u v
    have h := h4 (0, 0, u) (v, 0, 0)
    rw [hform (0, 0, u), hform (v, 0, 0)] at h
    simpa [fieldTracePair, fieldContraction4, fieldDet3, mul_assoc, mul_comm,
      mul_left_comm] using h
  · intro u v
    have h := h4 (u, 0, 0) (0, v, 0)
    rw [hform (u, 0, 0), hform (0, v, 0)] at h
    simpa [fieldTracePair, fieldContraction4, fieldDet3, mul_assoc, mul_comm,
      mul_left_comm] using h

/-- Simultaneous balance for the four standard clean contractions. -/
noncomputable def fieldFourBalanced
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c a b d : K) (T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K) : Prop :=
    (∀ x y, fieldContraction0 K c (T x) y = fieldContraction0 K c x (T y)) ∧
    (∀ x y, fieldContraction1 K c (T x) y = fieldContraction1 K c x (T y)) ∧
    (∀ x y, fieldContraction2 K c (T x) y = fieldContraction2 K c x (T y)) ∧
    (∀ x y, fieldContraction4 K c a b d (T x) y =
      fieldContraction4 K c a b d x (T y))

/-- The physical first contraction paired with the first vector of a sampled
`K`-basis, using the ambient standard-coordinate determinant. -/
noncomputable def sampledContraction0
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (b : Basis (Fin 3) K (FieldTriple K))
    (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y (b 0))

/-- The physical second contraction paired with the second sampled basis
vector. -/
noncomputable def sampledContraction1
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (b : Basis (Fin 3) K (FieldTriple K))
    (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y (b 1))

/-- The physical third contraction paired with the third sampled basis
vector. -/
noncomputable def sampledContraction2
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (b : Basis (Fin 3) K (FieldTriple K))
    (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y (b 2))

/-- The physical fourth contraction paired with a sampled vector `v`. -/
noncomputable def sampledContraction4
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (v : FieldTriple K) (x y : FieldTriple K) : ZMod (ringChar K) :=
  Algebra.trace (ZMod (ringChar K)) K (c * fieldDet3 x y v)

/-- The actual four ambient-determinant balance equations for a sampled basis
and fourth vector. -/
noncomputable def sampledFourBalanced
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (T : Module.End (ZMod (ringChar K)) (FieldTriple K)) : Prop :=
  (∀ x y, sampledContraction0 K c basis (T x) y =
      sampledContraction0 K c basis x (T y)) ∧
  (∀ x y, sampledContraction1 K c basis (T x) y =
      sampledContraction1 K c basis x (T y)) ∧
  (∀ x y, sampledContraction2 K c basis (T x) y =
      sampledContraction2 K c basis x (T y)) ∧
  (∀ x y, sampledContraction4 K c v (T x) y =
      sampledContraction4 K c v x (T y))

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

/-- For four standard clean contractions with a coordinate that generates the
base field, the common balanced endomorphisms are exactly scalar
multiplications. This is the standard-coordinate equality; sampled-basis
transport and dimension are separate obligations. -/
theorem standard_four_contractions_iff_scalar
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c a b d : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K)) {a} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {b} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {d} = ⊤) :
    ∀ T : FieldTriple K →ₗ[ZMod (ringChar K)] FieldTriple K,
      fieldFourBalanced K c a b d T ↔
        ∃ k : K, ∀ x, T x = fieldScalarTriple k x := by
  intro T
  constructor
  · rintro ⟨h0, h1, h2, h4⟩
    obtain ⟨A, hform, hself⟩ := first_three_common_block K c hc T h0 h1 h2
    have hpairs := fourth_balance_weighted_pairs K c a b d A T hform h4
    rcases hgen with ha | hb | hd
    · have hcomm : ∀ x, A (a * x) = a * A x := by
        intro x
        apply fieldTracePair_right_injective K c hc
        intro u
        calc
          fieldTracePair K c u (A (a * x)) =
              fieldTracePair K c (A u) (a * x) := (hself u (a * x)).symm
          _ = fieldTracePair K c u (a * A x) := hpairs.1 u x
      have hscalar := linearMap_scalar_of_commutes_generator
        (ZMod (ringChar K)) K A a ha hcomm
      refine ⟨A 1, ?_⟩
      intro x
      calc
        T x = (A x.1, A x.2.1, A x.2.2) := hform x
        _ = fieldScalarTriple (A 1) x := by
          simp only [fieldScalarTriple]
          rw [hscalar x.1, hscalar x.2.1, hscalar x.2.2]
    · have hcomm : ∀ x, A (b * x) = b * A x := by
        intro x
        apply fieldTracePair_right_injective K c hc
        intro u
        calc
          fieldTracePair K c u (A (b * x)) =
              fieldTracePair K c (A u) (b * x) := (hself u (b * x)).symm
          _ = fieldTracePair K c u (b * A x) := hpairs.2.1 u x
      have hscalar := linearMap_scalar_of_commutes_generator
        (ZMod (ringChar K)) K A b hb hcomm
      refine ⟨A 1, ?_⟩
      intro x
      calc
        T x = (A x.1, A x.2.1, A x.2.2) := hform x
        _ = fieldScalarTriple (A 1) x := by
          simp only [fieldScalarTriple]
          rw [hscalar x.1, hscalar x.2.1, hscalar x.2.2]
    · have hcomm : ∀ x, A (d * x) = d * A x := by
        intro x
        apply fieldTracePair_right_injective K c hc
        intro u
        calc
          fieldTracePair K c u (A (d * x)) =
              fieldTracePair K c (A u) (d * x) := (hself u (d * x)).symm
          _ = fieldTracePair K c u (d * A x) := hpairs.2.2 u x
      have hscalar := linearMap_scalar_of_commutes_generator
        (ZMod (ringChar K)) K A d hd hcomm
      refine ⟨A 1, ?_⟩
      intro x
      calc
        T x = (A x.1, A x.2.1, A x.2.2) := hform x
        _ = fieldScalarTriple (A 1) x := by
          simp only [fieldScalarTriple]
          rw [hscalar x.1, hscalar x.2.1, hscalar x.2.2]
  · rintro ⟨k, hk⟩
    constructor
    · intro x y
      rw [hk x, hk y, fieldScalarTriple_eq_smul k x, fieldScalarTriple_eq_smul k y]
      change Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 (k • x) y fieldBasis0) =
        Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 x (k • y) fieldBasis0)
      rw [fieldDet3_smul_left, fieldDet3_smul_right]
    constructor
    · intro x y
      rw [hk x, hk y, fieldScalarTriple_eq_smul k x, fieldScalarTriple_eq_smul k y]
      change Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 (k • x) y fieldBasis1) =
        Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 x (k • y) fieldBasis1)
      rw [fieldDet3_smul_left, fieldDet3_smul_right]
    constructor
    · intro x y
      rw [hk x, hk y, fieldScalarTriple_eq_smul k x, fieldScalarTriple_eq_smul k y]
      change Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 (k • x) y fieldBasis2) =
        Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 x (k • y) fieldBasis2)
      rw [fieldDet3_smul_left, fieldDet3_smul_right]
    · intro x y
      rw [hk x, hk y, fieldScalarTriple_eq_smul k x, fieldScalarTriple_eq_smul k y]
      change Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 (k • x) y (a, b, d)) =
        Algebra.trace (ZMod (ringChar K)) K
          (c * fieldDet3 x (k • y) (a, b, d))
      rw [fieldDet3_smul_left, fieldDet3_smul_right]

/-! ### Change of sampled coordinates

The standard theorem transports along any `K`-linear coordinate equivalence. The
coefficient supplied here is the coefficient *in the chosen coordinates*; for
an ambient determinant tensor and a basis matrix `P`, it is `c * det P`.
-/

/-- The four balance equations on a space `V`, expressed in the coordinates
provided by `q : V ≃ₗ[K] K³`. -/
def fourContractionsBalancedVia
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    (q : FieldTriple K ≃ₗ[K] FieldTriple K)
    (c a b d : K)
    (T : Module.End (ZMod (ringChar K)) (FieldTriple K)) : Prop :=
  fieldFourBalanced K c a b d ((q.restrictScalars (ZMod (ringChar K))).conj T)

/-- The standard-coordinate identification theorem transports through an
arbitrary `K`-linear coordinate equivalence. Scalar maps are preserved by
conjugation because the coordinate equivalence is `K`-linear. -/
theorem four_contractions_via_iff_scalar
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    (q : FieldTriple K ≃ₗ[K] FieldTriple K)
    (c a b d : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K)) {a} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {b} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {d} = ⊤) :
    ∀ T : Module.End (ZMod (ringChar K)) (FieldTriple K),
      fourContractionsBalancedVia K q c a b d T ↔
        ∃ k : K, ∀ x, T x = k • x := by
  let F := ZMod (ringChar K)
  intro T
  change fieldFourBalanced K c a b d
      ((q.restrictScalars F).conj T) ↔ ∃ k : K, ∀ x, T x = k • x
  have hstd := standard_four_contractions_iff_scalar K c a b d hc hgen
      ((q.restrictScalars F).conj T)
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hstd.mp h
    refine ⟨k, ?_⟩
    intro x
    apply q.injective
    have hx := hk (q x)
    have hx' : q (T x) = k • q x := by
      simpa [LinearEquiv.conj_apply_apply, fieldScalarTriple_eq_smul] using hx
    change q (T x) = q (k • x)
    rw [map_smul]
    exact hx'
  · rintro ⟨k, hk⟩
    apply hstd.mpr
    refine ⟨k, ?_⟩
    intro y
    have hconj : ((q.restrictScalars F).conj T) y = q (T (q.symm y)) := by
      simp [LinearEquiv.conj_apply_apply]
    rw [hconj]
    calc
      q (T (q.symm y)) = q (k • q.symm y) := congrArg q (hk (q.symm y))
      _ = k • y := by rw [map_smul, q.apply_symm_apply]
      _ = fieldScalarTriple k y := (fieldScalarTriple_eq_smul k y).symm

/-! ### The dimension of the scalar family

The range of the scalar action is the balance space once the identification
theorem has been applied. This first packages the scalar maps as an actual
`F`-submodule and computes their dimension; the membership theorem below then
identifies it with the balanced endomorphisms.
-/

/-- Scalar multiplication as an `F`-linear family of endomorphisms. -/
noncomputable def scalarTripleEndLinearMap
    (K : Type*) [Field K] [Algebra (ZMod (ringChar K)) K] :
    K →ₗ[ZMod (ringChar K)] Module.End (ZMod (ringChar K)) (FieldTriple K) :=
  (Algebra.lsmul (ZMod (ringChar K)) (ZMod (ringChar K)) (FieldTriple K) :
    K →ₐ[ZMod (ringChar K)]
      Module.End (ZMod (ringChar K)) (FieldTriple K)).toLinearMap

/-- The scalar-action submodule of binary-linear endomorphisms. -/
noncomputable def scalarTripleEndRange
    (K : Type*) [Field K] [Algebra (ZMod (ringChar K)) K] :
    Submodule (ZMod (ringChar K))
      (Module.End (ZMod (ringChar K)) (FieldTriple K)) :=
  LinearMap.range (scalarTripleEndLinearMap K)

/-- The scalar-action map is injective, as witnessed by its value on the first
standard coordinate vector. -/
theorem scalarTripleEndLinearMap_injective
    (K : Type*) [Field K] [Algebra (ZMod (ringChar K)) K] :
    Function.Injective (scalarTripleEndLinearMap K) := by
  intro k₁ k₂ h
  have hv := congrArg (fun T : Module.End (ZMod (ringChar K)) (FieldTriple K) =>
    T (fieldBasis0 : FieldTriple K)) h
  have hv' : k₁ • (fieldBasis0 : FieldTriple K) =
      k₂ • (fieldBasis0 : FieldTriple K) := by
    simpa [scalarTripleEndLinearMap, Algebra.lsmul_apply] using hv
  have h0 := congrArg Prod.fst hv'
  simpa [fieldBasis0, smul_eq_mul] using h0

/-- The scalar-action submodule has dimension `finrank F K`. -/
theorem scalarTripleEndRange_finrank
    (K : Type*) [Field K] [Algebra (ZMod (ringChar K)) K] :
    Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
      Module.finrank (ZMod (ringChar K)) K := by
  exact LinearMap.finrank_range_of_inj (scalarTripleEndLinearMap_injective K)

/-- Under the generator hypothesis, membership in the scalar-action submodule
is exactly the four balance equations. -/
theorem standard_four_balance_iff_mem_scalarTripleEndRange
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    (c a b d : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K)) {a} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {b} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {d} = ⊤)
    (T : Module.End (ZMod (ringChar K)) (FieldTriple K)) :
    fieldFourBalanced K c a b d T ↔ T ∈ scalarTripleEndRange K := by
  rw [standard_four_contractions_iff_scalar K c a b d hc hgen T]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply LinearMap.ext
    intro x
    change k • x = T x
    calc
      k • x = fieldScalarTriple k x := (fieldScalarTriple_eq_smul k x).symm
      _ = T x := (hk x).symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    intro x
    have hx := congrArg (fun f : Module.End (ZMod (ringChar K)) (FieldTriple K) => f x) hk
    have hx' : k • x = T x := by
      simpa [scalarTripleEndLinearMap, Algebra.lsmul_apply] using hx
    calc
      T x = k • x := hx'.symm
      _ = fieldScalarTriple k x := (fieldScalarTriple_eq_smul k x).symm

/-- The standard four-contraction balance space has dimension `finrank F K`.
The preceding membership theorem establishes that this range is exactly the
set of balanced endomorphisms. -/
theorem standard_four_contractions_balance_finrank
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    (c a b d : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K)) {a} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {b} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K)) {d} = ⊤) :
    (∀ T : Module.End (ZMod (ringChar K)) (FieldTriple K),
      fieldFourBalanced K c a b d T ↔ T ∈ scalarTripleEndRange K) ∧
    Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
      Module.finrank (ZMod (ringChar K)) K := by
  constructor
  · intro T
    exact standard_four_balance_iff_mem_scalarTripleEndRange K c a b d hc hgen T
  · exact scalarTripleEndRange_finrank K

/-- The physical first contraction becomes its coordinate form after scaling
by the sampled-basis determinant. -/
theorem sampledContraction0_eq_coordinate
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (basis : Basis (Fin 3) K (FieldTriple K))
    (x y : FieldTriple K) :
    sampledContraction0 K c basis x y =
      fieldContraction0 K (c * sampledBasisDeterminant K basis)
        (sampledBasisCoordinateEquiv K basis x)
        (sampledBasisCoordinateEquiv K basis y) := by
  unfold sampledContraction0 fieldContraction0
  apply congrArg (Algebra.trace (ZMod (ringChar K)) K)
  rw [fieldDet3_sampledBasis_change K basis x y (basis 0)]
  simp only [sampledBasisCoordinateEquiv_apply_basis, fieldTripleStandardBasis_zero]
  ring

/-- Coordinate form of the second physical contraction. -/
theorem sampledContraction1_eq_coordinate
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (basis : Basis (Fin 3) K (FieldTriple K))
    (x y : FieldTriple K) :
    sampledContraction1 K c basis x y =
      fieldContraction1 K (c * sampledBasisDeterminant K basis)
        (sampledBasisCoordinateEquiv K basis x)
        (sampledBasisCoordinateEquiv K basis y) := by
  unfold sampledContraction1 fieldContraction1
  apply congrArg (Algebra.trace (ZMod (ringChar K)) K)
  rw [fieldDet3_sampledBasis_change K basis x y (basis 1)]
  simp only [sampledBasisCoordinateEquiv_apply_basis, fieldTripleStandardBasis_one]
  ring

/-- Coordinate form of the third physical contraction. -/
theorem sampledContraction2_eq_coordinate
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (basis : Basis (Fin 3) K (FieldTriple K))
    (x y : FieldTriple K) :
    sampledContraction2 K c basis x y =
      fieldContraction2 K (c * sampledBasisDeterminant K basis)
        (sampledBasisCoordinateEquiv K basis x)
        (sampledBasisCoordinateEquiv K basis y) := by
  unfold sampledContraction2 fieldContraction2
  apply congrArg (Algebra.trace (ZMod (ringChar K)) K)
  rw [fieldDet3_sampledBasis_change K basis x y (basis 2)]
  simp only [sampledBasisCoordinateEquiv_apply_basis, fieldTripleStandardBasis_two]
  ring

/-- Coordinate form of the actual fourth contraction. -/
theorem sampledContraction4_eq_coordinate
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (c : K) (basis : Basis (Fin 3) K (FieldTriple K))
    (v x y : FieldTriple K) :
    sampledContraction4 K c v x y =
      fieldContraction4 K (c * sampledBasisDeterminant K basis)
        (sampledBasisCoordinateEquiv K basis v).1
        (sampledBasisCoordinateEquiv K basis v).2.1
        (sampledBasisCoordinateEquiv K basis v).2.2
        (sampledBasisCoordinateEquiv K basis x)
        (sampledBasisCoordinateEquiv K basis y) := by
  unfold sampledContraction4 fieldContraction4
  apply congrArg (Algebra.trace (ZMod (ringChar K)) K)
  rw [fieldDet3_sampledBasis_change K basis x y v]
  ring

/-- Balance of a scalar-valued pair form is invariant under K-linear
coordinate conjugation when the form is transported on both inputs. -/
private theorem pairBalance_via_coordinateEquiv
    (K : Type*) [Field K] [Algebra (ZMod (ringChar K)) K]
    (q : FieldTriple K ≃ₗ[K] FieldTriple K)
    (T : Module.End (ZMod (ringChar K)) (FieldTriple K))
    (P Q : FieldTriple K → FieldTriple K → ZMod (ringChar K))
    (hform : ∀ x y, P x y = Q (q x) (q y)) :
    (∀ x y, P (T x) y = P x (T y)) ↔
      (∀ x y, Q ((q.restrictScalars (ZMod (ringChar K))).conj T x) y =
        Q x ((q.restrictScalars (ZMod (ringChar K))).conj T y)) := by
  let qF := q.restrictScalars (ZMod (ringChar K))
  let T' := qF.conj T
  constructor
  · intro h x y
    let u := q.symm x
    let v := q.symm y
    calc
      Q (T' x) y = P (T u) v := by rw [hform]; simp [T', qF, u, v]
      _ = P u (T v) := h u v
      _ = Q x (T' y) := by rw [hform]; simp [T', qF, u, v]
  · intro h x y
    calc
      P (T x) y = Q (T' (q x)) (q y) := by rw [hform]; simp [T', qF]
      _ = Q (q x) (T' (q y)) := h (q x) (q y)
      _ = P x (T y) := by rw [hform]; simp [T', qF]

/-- The actual first-three and fourth ambient contractions for a sampled basis
are exactly the coordinate contractions with coefficient `c * det(P)`, and
their balance predicate is equivalent in both directions to the coordinate
balance predicate. -/
theorem sampled_four_contractions_iff_via
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (T : Module.End (ZMod (ringChar K)) (FieldTriple K)) :
    sampledFourBalanced K c basis v T ↔
      fourContractionsBalancedVia K (sampledBasisCoordinateEquiv K basis)
        (c * sampledBasisDeterminant K basis)
        (sampledBasisCoordinateEquiv K basis v).1
        (sampledBasisCoordinateEquiv K basis v).2.1
        (sampledBasisCoordinateEquiv K basis v).2.2 T := by
  let q := sampledBasisCoordinateEquiv K basis
  let c' := c * sampledBasisDeterminant K basis
  let qT := (q.restrictScalars (ZMod (ringChar K))).conj T
  have h0 : ∀ x y, sampledContraction0 K c basis x y =
      fieldContraction0 K c' (q x) (q y) := by
    intro x y
    simpa [q, c'] using sampledContraction0_eq_coordinate K c basis x y
  have h1 : ∀ x y, sampledContraction1 K c basis x y =
      fieldContraction1 K c' (q x) (q y) := by
    intro x y
    simpa [q, c'] using sampledContraction1_eq_coordinate K c basis x y
  have h2 : ∀ x y, sampledContraction2 K c basis x y =
      fieldContraction2 K c' (q x) (q y) := by
    intro x y
    simpa [q, c'] using sampledContraction2_eq_coordinate K c basis x y
  have h4 : ∀ x y, sampledContraction4 K c v x y =
      fieldContraction4 K c' (q v).1 (q v).2.1 (q v).2.2 (q x) (q y) := by
    intro x y
    simpa [q, c'] using sampledContraction4_eq_coordinate K c basis v x y
  change sampledFourBalanced K c basis v T ↔
    fieldFourBalanced K c' (q v).1 (q v).2.1 (q v).2.2 qT
  unfold sampledFourBalanced fieldFourBalanced
  constructor
  · rintro ⟨h0b, h1b, h2b, h4b⟩
    exact ⟨
      (pairBalance_via_coordinateEquiv K q T _ _ h0).mp h0b,
      (pairBalance_via_coordinateEquiv K q T _ _ h1).mp h1b,
      (pairBalance_via_coordinateEquiv K q T _ _ h2).mp h2b,
      (pairBalance_via_coordinateEquiv K q T _ _ h4).mp h4b⟩
  · rintro ⟨h0b, h1b, h2b, h4b⟩
    exact ⟨
      (pairBalance_via_coordinateEquiv K q T _ _ h0).mpr h0b,
      (pairBalance_via_coordinateEquiv K q T _ _ h1).mpr h1b,
      (pairBalance_via_coordinateEquiv K q T _ _ h2).mpr h2b,
      (pairBalance_via_coordinateEquiv K q T _ _ h4).mpr h4b⟩

/-- Membership in the scalar-action range is exactly pointwise scalar
multiplication. -/
theorem scalarTripleEndRange_mem_iff
    (K : Type*) [Field K] [Algebra (ZMod (ringChar K)) K]
    (T : Module.End (ZMod (ringChar K)) (FieldTriple K)) :
    T ∈ scalarTripleEndRange K ↔
      ∃ k : K, ∀ x, T x = fieldScalarTriple k x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    intro x
    have hx := congrArg
      (fun f : Module.End (ZMod (ringChar K)) (FieldTriple K) => f x) hk
    have hx' : k • x = T x := by
      simpa [scalarTripleEndLinearMap, Algebra.lsmul_apply] using hx
    rw [← hx', fieldScalarTriple_eq_smul]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply LinearMap.ext
    intro x
    change k • x = T x
    calc
      k • x = fieldScalarTriple k x := (fieldScalarTriple_eq_smul k x).symm
      _ = T x := (hk x).symm

/-- Actual arbitrary-sampled-basis identification, including both directions
and the dimension of its balance submodule. -/
theorem sampled_four_contractions_identification_and_finrank
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).1} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).2.1} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).2.2} = ⊤) :
    (∀ T : Module.End (ZMod (ringChar K)) (FieldTriple K),
      sampledFourBalanced K c basis v T ↔ T ∈ scalarTripleEndRange K) ∧
    Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
      Module.finrank (ZMod (ringChar K)) K := by
  have hc' : c * sampledBasisDeterminant K basis ≠ 0 :=
    mul_ne_zero hc (sampledBasisDeterminant_ne_zero K basis)
  constructor
  · intro T
    exact (sampled_four_contractions_iff_via K basis v c T).trans
      ((four_contractions_via_iff_scalar K
        (sampledBasisCoordinateEquiv K basis)
        (c * sampledBasisDeterminant K basis)
        (sampledBasisCoordinateEquiv K basis v).1
        (sampledBasisCoordinateEquiv K basis v).2.1
        (sampledBasisCoordinateEquiv K basis v).2.2 hc' hgen T).trans
        (scalarTripleEndRange_mem_iff K T).symm)
  · exact scalarTripleEndRange_finrank K

/-- For a binary field of cardinality `2^s`, the sampled-basis balance
submodule has dimension `s` over `F₂`. -/
theorem sampled_four_contractions_balance_finrank_eq_s
    (K : Type*) [Field K] [Finite K] [Fintype K] [CharP K 2]
    [Algebra (ZMod (ringChar K)) K]
    (basis : Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).1} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).2.1} = ⊤ ∨
      Algebra.adjoin (ZMod (ringChar K))
        {(sampledBasisCoordinateEquiv K basis v).2.2} = ⊤)
    (s : ℕ) (hcard : Fintype.card K = 2 ^ s) :
    Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) = s := by
  classical
  letI : NeZero (ringChar K) := ⟨CharP.ringChar_ne_zero_of_finite K⟩
  letI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hF : Fintype.card (ZMod (ringChar K)) = 2 := by
    exact (ZMod.card (ringChar K)).trans hchar
  have hdim := (sampled_four_contractions_identification_and_finrank
    K basis v c hc hgen).2
  have hcard' : Fintype.card K =
      Fintype.card (ZMod (ringChar K)) ^ Module.finrank (ZMod (ringChar K)) K :=
    Module.card_eq_pow_finrank (K := ZMod (ringChar K)) (V := K)
  rw [hF, hcard] at hcard'
  have hpow : 2 ^ s = 2 ^ Module.finrank (ZMod (ringChar K)) K :=
    hcard'
  rw [hdim]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hpow).symm

end CorruptedFieldRecovery
