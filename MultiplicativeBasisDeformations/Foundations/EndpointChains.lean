import MultiplicativeBasisDeformations.Foundations.Rays
import MultiplicativeBasisDeformations.Foundations.RepFinite
import MultiplicativeBasisDeformations.Foundations.CornerRepFinite
import MBDVendor.Magnitude.LinearAlgebra.LocalAlgebraResidue

/-!
# Endpoint subbimodules form chains

Lemma 3.1(3) (`lem:endpoint-chains`, `projective-rays.tex`). For a
representation-finite algebra `A` over an algebraically closed field with
primitive idempotents `e_x`, put `R_x = e_xAe_x`.

* Each `R_x` is local with residue field `k`: `R_x = k e_x + rad R_x`, with
  `rad R_x = R_x ∩ rad A` nilpotent.
* An `R_x`--`R_y`-subbimodule `N` of `A(x, y)` is recovered from the ideal it
  generates, `e_x(ANA)e_y = N`; so there are finitely many.
* Two incomparable subbimodules would give `k²` in the socle of
  `(N₁ + N₂)/(N₁ ∩ N₂)`, whose infinitely many lines lift to distinct
  subbimodules; so the subbimodules form a chain, with one-dimensional
  successive quotients.
* For `f ≠ 0`, `R_xfR_y = R_xf` or `fR_y`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

section Jacobson

variable {R : Type*} [Ring R]

/-- Jacobson's lemma. -/
theorem isUnit_one_sub_mul_of_comm {a b : R} (h : IsUnit (1 - b * a)) : IsUnit (1 - a * b) := by
  obtain ⟨c, hc⟩ := h
  set d : R := ((c⁻¹ : Rˣ) : R)
  have h1 : (1 - b * a) * d = 1 := by rw [← hc]; exact c.mul_inv
  have h2 : d * (1 - b * a) = 1 := by rw [← hc]; exact c.inv_mul
  refine ⟨⟨1 - a * b, 1 + a * d * b, ?_, ?_⟩, rfl⟩
  · calc (1 - a * b) * (1 + a * d * b) = 1 - a * b + a * ((1 - b * a) * d) * b := by noncomm_ring
      _ = 1 := by rw [h1]; noncomm_ring
  · calc (1 + a * d * b) * (1 - a * b) = 1 - a * b + a * (d * (1 - b * a)) * b := by noncomm_ring
      _ = 1 := by rw [h2]; noncomm_ring

/-- An element `x` with `1 - yx` invertible for all `y` lies in the Jacobson
radical. -/
theorem mem_jacobson_of_forall_isUnit {x : R} (h : ∀ y, IsUnit (1 - y * x)) :
    x ∈ Ring.jacobson R := by
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
  intro I hI
  by_contra hx
  have hI' : Ideal.IsMaximal I := hI
  have htop : I ⊔ Submodule.span R {x} = ⊤ := by
    apply hI'.1.2
    refine lt_of_le_of_ne le_sup_left fun he ↦ hx ?_
    rw [he]
    exact le_sup_right (a := I) (Submodule.mem_span_singleton_self x)
  have h1 : (1 : R) ∈ I ⊔ Submodule.span R {x} := htop ▸ Submodule.mem_top
  obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hi1 : i = 1 - y * x := by rw [← hiz, smul_eq_mul]; abel
  exact hI'.ne_top (Ideal.eq_top_of_isUnit_mem I hi (hi1 ▸ h y))

end Jacobson

section Corners

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (F : PrimitiveIdempotents A)

namespace PrimitiveIdempotents

variable (k) in
include k in
theorem corner_isLocalRing (x : Fin F.m) : IsLocalRing (F.complete.idem x).Corner := by
  have he := F.complete.idem x
  haveI : Nontrivial he.Corner := ⟨⟨1, 0, fun h ↦ (F.primitive x).2.1 (by
    have := congrArg (cornerVal he) h
    simpa using this)⟩⟩
  haveI : FiniteDimensional k he.Corner := corner_finite he
  apply MBDVendor.Magnitude.finiteDimensional_isLocalRing_of_idempotents (k := k)
  intro c hc
  have hcA : IsIdempotentElem (cornerVal he c) := by
    change cornerVal he c * cornerVal he c = cornerVal he c
    rw [← corner_mul_val, hc.eq]
  rcases (F.primitive x).2.2 _ hcA (corner_mul_left he c) (corner_mul_right he c) with h | h
  · left; exact corner_ext he (by simpa using h)
  · right; exact corner_ext he (by simpa using h)

theorem mem_corner_iff' {x y : Fin F.m} {a : A} :
    a ∈ F.corner (k := k) x y ↔ F.e x * a * F.e y = a := by
  constructor
  · rintro ⟨r, rfl⟩
    change F.e x * (F.e x * (r * F.e y)) * F.e y = F.e x * (r * F.e y)
    rw [← mul_assoc, (F.complete.idem x).eq, mul_assoc, mul_assoc, (F.complete.idem y).eq]
  · intro h
    exact ⟨a, by change F.e x * (a * F.e y) = a; rw [← mul_assoc, h]⟩

theorem corner_mem_sub (x : Fin F.m) {a : A} (ha : a ∈ F.corner (k := k) x x) :
    a ∈ Subsemigroup.corner (F.e x) := ⟨a, (F.mem_corner_iff' (k := k)).1 ha⟩

variable (k) in
/-- **`R_x = k e_x + rad R_x`.** -/
theorem exists_sub_smul_mem_radical (x : Fin F.m) {a : A} (ha : a ∈ F.corner (k := k) x x) :
    ∃ c : k, a - c • F.e x ∈ algebraRadical k A := by
  have he := F.complete.idem x
  haveI := F.corner_isLocalRing k x
  haveI : FiniteDimensional k he.Corner := corner_finite he
  let a' : he.Corner := cornerMk he a (F.corner_mem_sub x ha)
  let c := MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k a'
  refine ⟨c, ?_⟩
  let z : he.Corner := a' - algebraMap k he.Corner c
  have hzA : cornerVal he z = a - c • F.e x := by
    change cornerVal he (a' - c • (1 : he.Corner)) = _
    rfl
  have hz0 : MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k z = 0 := by
    rw [show z = a' + -(algebraMap k he.Corner c) from sub_eq_add_neg _ _]
    rw [MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_add, ← map_neg,
      MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_algebraMap, add_neg_cancel]
  change a - c • F.e x ∈ Ring.jacobson A
  rw [← hzA]
  apply mem_jacobson_of_forall_isUnit
  intro y
  let u : he.Corner := cornerMk he (F.e x * y * F.e x) ⟨y, rfl⟩
  let w : he.Corner := z * u
  have hneg : MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k (-(z * u)) = 0 := by
    have := MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_add (k := k) (z * u) (-(z * u))
    rw [add_neg_cancel, MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_zero,
      MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_mul, hz0, zero_mul, zero_add] at this
    exact this.symm
  have hres : MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k (1 - w) = 1 := by
    rw [show (1 : he.Corner) - w = 1 + -(z * u) from sub_eq_add_neg _ _]
    rw [MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_add, hneg, add_zero,
      show (1 : he.Corner) = algebraMap k he.Corner 1 from (map_one _).symm,
      MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_algebraMap]
  have hunit : IsUnit (1 - w) := by
    by_contra hnu
    have := (MBDVendor.Magnitude.LocalAlgebraResidue.mem_ker_residueLinearMap_iff (k := k)
      (1 - w)).2 hnu
    rw [LinearMap.mem_ker, MBDVendor.Magnitude.LocalAlgebraResidue.residueLinearMap_apply,
      hres] at this
    exact one_ne_zero this
  obtain ⟨v, hv⟩ := hunit
  have hvl : cornerVal he ((1 - w) * v⁻¹.1) = F.e x := by rw [← hv, v.mul_inv]; rfl
  have hvr : cornerVal he (v⁻¹.1 * (1 - w)) = F.e x := by rw [← hv, v.inv_mul]; rfl
  have hwA : cornerVal he w = cornerVal he z * (y * F.e x) := by
    change cornerVal he z * (F.e x * y * F.e x) = _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, corner_mul_right]
  have key : IsUnit (1 - cornerVal he z * (y * F.e x)) := by
    rw [← hwA]
    set vA := cornerVal he v⁻¹.1
    set wA := cornerVal he w
    have h1 : (F.e x - wA) * vA = F.e x := by
      have := hvl; rw [corner_mul_val] at this; exact this
    have h2 : vA * (F.e x - wA) = F.e x := by
      have := hvr; rw [corner_mul_val] at this; exact this
    have hwe : wA * F.e x = wA := corner_mul_right he w
    have hew : F.e x * wA = wA := corner_mul_left he w
    have hve : vA * F.e x = vA := corner_mul_right he _
    have hev : F.e x * vA = vA := corner_mul_left he _
    refine ⟨⟨1 - wA, 1 - F.e x + vA, ?_, ?_⟩, rfl⟩
    · calc (1 - wA) * (1 - F.e x + vA) = 1 - F.e x + vA - wA + wA * F.e x - wA * vA := by
            noncomm_ring
        _ = 1 - F.e x + (F.e x - wA) * vA := by rw [hwe, sub_mul, hev]; abel
        _ = 1 := by rw [h1]; abel
    · calc (1 - F.e x + vA) * (1 - wA) = 1 - F.e x + vA - wA + F.e x * wA - vA * wA := by
            noncomm_ring
        _ = 1 - F.e x + vA * (F.e x - wA) := by rw [hew, mul_sub, hve]; abel
        _ = 1 := by rw [h2]; abel
  have := isUnit_one_sub_mul_of_comm key
  rwa [mul_assoc, show F.e x * cornerVal he z = cornerVal he z from corner_mul_left he z] at this

end PrimitiveIdempotents

omit [IsAlgClosed k] in
/-- The radical of a finite-dimensional algebra is nilpotent. -/
theorem algebraRadical_pow_eq_bot : ∃ K : ℕ, algebraRadical k A ^ K = ⊥ := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨K, hK⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨K, eq_bot_iff.2 ?_⟩
  have hle : ∀ n, algebraRadical k A ^ n ≤ ((Ideal.jacobson (⊥ : Ideal A)) ^ n).restrictScalars k := by
    intro n
    induction n with
    | zero =>
        intro x _
        change x ∈ (Ideal.jacobson (⊥ : Ideal A)) ^ 0
        rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial
    | succ n ih =>
        rw [pow_succ]
        apply Submodule.mul_le.2
        intro a ha b hb
        have hb' : b ∈ Ideal.jacobson (⊥ : Ideal A) := by
          rw [Ideal.jacobson_bot]; exact hb
        change a * b ∈ (Ideal.jacobson (⊥ : Ideal A)) ^ (n + 1)
        rw [Submodule.pow_succ]
        exact Submodule.mul_mem_mul (ih ha) hb'
  intro a ha
  have := hle K ha
  rw [hK] at this
  exact this

namespace PrimitiveIdempotents

/-- The two-sided ideal generated by a subspace: the span of all `a n b`. -/
def genIdeal (N : Submodule k A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (Submodule.span k {z | ∃ a b : A, ∃ n ∈ N, z = a * n * b} : Set A)
    (Submodule.zero_mem _) (fun hx hy ↦ Submodule.add_mem _ hx hy)
    (fun hx ↦ Submodule.neg_mem _ hx)
    (fun {x y} hy ↦ by
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨a, b, n, hn, rfl⟩ := hz
          exact Submodule.subset_span ⟨x * a, b, n, hn, by noncomm_ring⟩
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy)
    (fun {x y} hx ↦ by
      induction hx using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨a, b, n, hn, rfl⟩ := hz
          exact Submodule.subset_span ⟨a, b * y, n, hn, by noncomm_ring⟩
      | zero => simp
      | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
      | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx)

theorem mem_genIdeal_iff {N : Submodule k A} {z : A} :
    z ∈ genIdeal N ↔ z ∈ Submodule.span k {z | ∃ a b : A, ∃ n ∈ N, z = a * n * b} :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

theorem mem_genIdeal {N : Submodule k A} {n : A} (hn : n ∈ N) : n ∈ genIdeal N :=
  mem_genIdeal_iff.2 (Submodule.subset_span ⟨1, 1, n, hn, by simp⟩)

theorem corner_mul_mem {x y : Fin F.m} {n : A} (hn : n ∈ F.corner (k := k) x y) :
    F.e x * n = n ∧ n * F.e y = n := by
  have h := (F.mem_corner_iff' (k := k)).1 hn
  constructor
  · calc F.e x * n = F.e x * (F.e x * n * F.e y) := by rw [h]
      _ = F.e x * n * F.e y := by rw [← mul_assoc, ← mul_assoc, (F.complete.idem x).eq]
      _ = n := h
  · calc n * F.e y = (F.e x * n * F.e y) * F.e y := by rw [h]
      _ = F.e x * n * F.e y := by rw [mul_assoc, (F.complete.idem y).eq]
      _ = n := h

theorem eAe_mem (x : Fin F.m) (a : A) : F.e x * a * F.e x ∈ F.corner (k := k) x x :=
  (F.mem_corner_iff' (k := k)).2 (by
    rw [← mul_assoc, ← mul_assoc, (F.complete.idem x).eq, mul_assoc, mul_assoc,
      (F.complete.idem x).eq, ← mul_assoc])

theorem genIdeal_corner {x y : Fin F.m} {N : Submodule k A} (hN : F.IsEndpointSubbimodule x y N)
    {z : A} (hz : z ∈ genIdeal N) : F.e x * z * F.e y ∈ N := by
  rw [mem_genIdeal_iff] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, b, n, hn, rfl⟩ := hz
      obtain ⟨hl, hr⟩ := F.corner_mul_mem (hN.1 hn)
      have hl' : ∀ X, F.e x * (n * X) = n * X := fun X ↦ by rw [← mul_assoc, hl]
      have hr' : ∀ X, n * (F.e y * X) = n * X := fun X ↦ by rw [← mul_assoc, hr]
      have : F.e x * (a * n * b) * F.e y =
          (F.e x * a * F.e x) * n * (F.e y * b * F.e y) := by
        simp only [mul_assoc, hl', hr']
      rw [this]
      exact hN.2.2 _ (F.eAe_mem y b) _ (hN.2.1 _ (F.eAe_mem x a) _ hn)
  | zero => simp
  | add z w _ _ hz hw => rw [mul_add, add_mul]; exact N.add_mem hz hw
  | smul c z _ hz => rw [mul_smul_comm, smul_mul_assoc]; exact N.smul_mem c hz

/-- **Finitely many endpoint subbimodules**: each is recovered from the ideal
it generates. -/
theorem finite_subbimodules (hA : IsRepresentationFinite k A) (x y : Fin F.m) :
    {N : Submodule k A | F.IsEndpointSubbimodule x y N}.Finite := by
  apply Set.Finite.of_finite_image (f := genIdeal)
  · exact (finite_twoSidedIdeals_of hA).subset (Set.subset_univ _)
  · intro N hN N' hN' h
    apply le_antisymm
    · intro n hn
      have := F.genIdeal_corner hN' (h ▸ mem_genIdeal hn)
      rwa [(F.corner_mul_mem (hN.1 hn)).1, (F.corner_mul_mem (hN.1 hn)).2] at this
    · intro n hn
      have := F.genIdeal_corner hN (h.symm ▸ mem_genIdeal hn)
      rwa [(F.corner_mul_mem (hN'.1 hn)).1, (F.corner_mul_mem (hN'.1 hn)).2] at this

theorem cornerRadical_le_corner (x : Fin F.m) : F.cornerRadical (k := k) x ≤ F.corner x x :=
  inf_le_left

theorem cornerRadical_le_radical (x : Fin F.m) :
    F.cornerRadical (k := k) x ≤ algebraRadical k A := inf_le_right

theorem cornerRadical_pow_eq_bot : ∃ K : ℕ, ∀ x : Fin F.m, F.cornerRadical (k := k) x ^ K = ⊥ := by
  obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := A)
  exact ⟨K, fun x ↦ eq_bot_iff.2 (hK ▸ pow_le_pow_left' (F.cornerRadical_le_radical x) K)⟩

/-- **Nakayama's lemma for subbimodules.** If `P ≤ (rad R_x) P + P (rad R_y) + L`
for a subbimodule `L`, then `P ≤ L`. -/
theorem le_of_le_rad {x y : Fin F.m} {P L : Submodule k A}
    (hL₁ : F.cornerRadical (k := k) x * L ≤ L) (hL₂ : L * F.cornerRadical (k := k) y ≤ L)
    (hP : P ≤ F.cornerRadical (k := k) x * P ⊔ P * F.cornerRadical (k := k) y ⊔ L) : P ≤ L := by
  set Rx := F.cornerRadical (k := k) x
  set Ry := F.cornerRadical (k := k) y
  let G : ℕ → Submodule k A := fun M ↦ ⨆ (i : ℕ) (j : ℕ) (_ : i + j = M), Rx ^ i * P * Ry ^ j
  have hstep : ∀ M, G M ≤ G (M + 1) ⊔ L := by
    intro M
    refine iSup₂_le fun i j ↦ iSup_le fun hij ↦ ?_
    calc Rx ^ i * P * Ry ^ j ≤ Rx ^ i * (Rx * P ⊔ P * Ry ⊔ L) * Ry ^ j := by
          gcongr
      _ ≤ G (M + 1) ⊔ L := by
          rw [Submodule.mul_sup, Submodule.mul_sup, Submodule.sup_mul, Submodule.sup_mul]
          refine sup_le (sup_le ?_ ?_) ?_
          · apply le_sup_of_le_left
            refine le_iSup₂_of_le (i + 1) j (le_iSup_of_le (by omega) (le_of_eq ?_))
            simp only [pow_succ, mul_assoc]
          · apply le_sup_of_le_left
            refine le_iSup₂_of_le i (j + 1) (le_iSup_of_le (by omega) (le_of_eq ?_))
            simp only [pow_succ', mul_assoc]
          · apply le_sup_of_le_right
            have h1 : ∀ n, Rx ^ n * L ≤ L := by
              intro n; induction n with
              | zero => rw [pow_zero, Submodule.one_mul]
              | succ n ih => rw [pow_succ', mul_assoc]; exact (_root_.mul_le_mul_right ih Rx).trans hL₁
            have h2 : ∀ n, L * Ry ^ n ≤ L := by
              intro n; induction n with
              | zero => rw [pow_zero, Submodule.mul_one]
              | succ n ih => rw [pow_succ, ← mul_assoc]; exact (_root_.mul_le_mul_left ih Ry).trans hL₂
            exact (_root_.mul_le_mul_left (h1 i) _).trans (h2 j)
  have hall : ∀ M, P ≤ G M ⊔ L := by
    intro M
    induction M with
    | zero =>
        apply le_sup_of_le_left
        refine le_iSup₂_of_le 0 0 (le_iSup_of_le rfl (le_of_eq ?_))
        rw [pow_zero, pow_zero, Submodule.one_mul, Submodule.mul_one]
    | succ M ih =>
        exact ih.trans (sup_le (hstep M) le_sup_right)
  obtain ⟨K, hK⟩ := F.cornerRadical_pow_eq_bot (k := k)
  have hbot : G (2 * K) = ⊥ := by
    refine eq_bot_iff.2 (iSup₂_le fun i j ↦ iSup_le fun hij ↦ ?_)
    rcases le_or_gt K i with hi | hi
    · rw [show i = K + (i - K) by omega, pow_add, hK x, Submodule.bot_mul, Submodule.bot_mul,
        Submodule.bot_mul]
    · rw [show j = K + (j - K) by omega, pow_add, hK y, Submodule.bot_mul, Submodule.mul_bot]
  have := hall (2 * K)
  rwa [hbot, bot_sup_eq] at this

theorem e_mem_corner (x : Fin F.m) : F.e x ∈ F.corner (k := k) x x :=
  (F.mem_corner_iff' (k := k)).2 (by rw [(F.complete.idem x).eq, (F.complete.idem x).eq])

theorem isEndpoint_sup {x y : Fin F.m} {N N' : Submodule k A} (h : F.IsEndpointSubbimodule x y N)
    (h' : F.IsEndpointSubbimodule x y N') : F.IsEndpointSubbimodule x y (N ⊔ N') := by
  refine ⟨sup_le h.1 h'.1, fun a ha n hn ↦ ?_, fun b hb n hn ↦ ?_⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hn
    rw [mul_add]; exact Submodule.add_mem_sup (h.2.1 a ha u hu) (h'.2.1 a ha v hv)
  · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hn
    rw [add_mul]; exact Submodule.add_mem_sup (h.2.2 b hb u hu) (h'.2.2 b hb v hv)

theorem isEndpoint_inf {x y : Fin F.m} {N N' : Submodule k A} (h : F.IsEndpointSubbimodule x y N)
    (h' : F.IsEndpointSubbimodule x y N') : F.IsEndpointSubbimodule x y (N ⊓ N') :=
  ⟨inf_le_left.trans h.1, fun a ha n hn ↦ ⟨h.2.1 a ha n hn.1, h'.2.1 a ha n hn.2⟩,
    fun b hb n hn ↦ ⟨h.2.2 b hb n hn.1, h'.2.2 b hb n hn.2⟩⟩

theorem radL_mem {x : Fin F.m} {a r : A} (ha : a ∈ F.corner (k := k) x x)
    (hr : r ∈ F.cornerRadical (k := k) x) : a * r ∈ F.cornerRadical (k := k) x := by
  refine ⟨?_, ?_⟩
  · have h1 := (F.mem_corner_iff' (k := k)).1 ha
    have h2 := (F.mem_corner_iff' (k := k)).1 hr.1
    exact (F.mem_corner_iff' (k := k)).2 (by
      rw [← h1, ← h2]; simp only [mul_assoc, (F.complete.idem x).eq]
      rw [← mul_assoc (F.e x) (F.e x), (F.complete.idem x).eq])
  · change a * r ∈ Ring.jacobson A
    exact (Ring.jacobson A).mul_mem_left a hr.2

theorem radR_mem {y : Fin F.m} {b r : A} (hb : b ∈ F.corner (k := k) y y)
    (hr : r ∈ F.cornerRadical (k := k) y) : r * b ∈ F.cornerRadical (k := k) y := by
  refine ⟨?_, ?_⟩
  · have h1 := (F.mem_corner_iff' (k := k)).1 hb
    have h2 := (F.mem_corner_iff' (k := k)).1 hr.1
    exact (F.mem_corner_iff' (k := k)).2 (by
      rw [← h1, ← h2]; simp only [mul_assoc, (F.complete.idem y).eq]
      rw [← mul_assoc (F.e y) (F.e y), (F.complete.idem y).eq])
  · change r * b ∈ Ring.jacobson A
    haveI : (Ring.jacobson A).IsTwoSided := inferInstance
    exact Ideal.mul_mem_right b (Ring.jacobson A) hr.2

/-- `(rad R_x) N + N (rad R_y)` is a subbimodule. -/
theorem isEndpoint_rad {x y : Fin F.m} {N : Submodule k A} (h : F.IsEndpointSubbimodule x y N) :
    F.IsEndpointSubbimodule x y
      (F.cornerRadical (k := k) x * N ⊔ N * F.cornerRadical (k := k) y) := by
  have hle1 : F.cornerRadical (k := k) x * N ≤ N := Submodule.mul_le.2 fun r hr n hn ↦
    h.2.1 r (F.cornerRadical_le_corner x hr) n hn
  have hle2 : N * F.cornerRadical (k := k) y ≤ N := Submodule.mul_le.2 fun n hn r hr ↦
    h.2.2 r (F.cornerRadical_le_corner y hr) n hn
  refine ⟨(sup_le hle1 hle2).trans h.1, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    rw [mul_add]
    refine Submodule.add_mem_sup ?_ ?_
    · refine Submodule.mul_induction_on hu (fun r hr n hn ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (F.radL_mem ha hr) hn
      · rw [mul_add]; exact Submodule.add_mem _ hp hq
    · refine Submodule.mul_induction_on hv (fun n hn r hr ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (h.2.1 a ha n hn) hr
      · rw [mul_add]; exact Submodule.add_mem _ hp hq
  · obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    rw [add_mul]
    refine Submodule.add_mem_sup ?_ ?_
    · refine Submodule.mul_induction_on hu (fun r hr n hn ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hr (h.2.2 b hb n hn)
      · rw [add_mul]; exact Submodule.add_mem _ hp hq
    · refine Submodule.mul_induction_on hv (fun n hn r hr ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hn (F.radR_mem hb hr)
      · rw [add_mul]; exact Submodule.add_mem _ hp hq

/-- Subspaces between `N'` and `N`, where `N/N'` is killed by the radicals, are
subbimodules. -/
theorem isEndpoint_between {x y : Fin F.m} {N N' P : Submodule k A}
    (hN : F.IsEndpointSubbimodule x y N) (h1 : N' ≤ P) (h2 : P ≤ N)
    (hr : F.cornerRadical (k := k) x * N ⊔ N * F.cornerRadical (k := k) y ≤ N') :
    F.IsEndpointSubbimodule x y P := by
  refine ⟨h2.trans hN.1, fun a ha p hp ↦ ?_, fun b hb p hp ↦ ?_⟩
  · obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k x ha
    have hrad : a - c • F.e x ∈ F.cornerRadical (k := k) x :=
      ⟨Submodule.sub_mem _ ha (Submodule.smul_mem _ c (F.e_mem_corner x)), hc⟩
    have hp' := (F.corner_mul_mem (hN.1 (h2 hp))).1
    have : a * p = c • p + (a - c • F.e x) * p := by
      rw [sub_mul, smul_mul_assoc, hp']; abel
    rw [this]
    exact P.add_mem (P.smul_mem c hp)
      (h1 (hr (Submodule.mem_sup_left (Submodule.mul_mem_mul hrad (h2 hp)))))
  · obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k y hb
    have hrad : b - c • F.e y ∈ F.cornerRadical (k := k) y :=
      ⟨Submodule.sub_mem _ hb (Submodule.smul_mem _ c (F.e_mem_corner y)), hc⟩
    have hp' := (F.corner_mul_mem (hN.1 (h2 hp))).2
    have : p * b = c • p + p * (b - c • F.e y) := by
      rw [mul_sub, mul_smul_comm, hp']; abel
    rw [this]
    exact P.add_mem (P.smul_mem c hp)
      (h1 (hr (Submodule.mem_sup_right (Submodule.mul_mem_mul (h2 hp) hrad))))

/-- A subbimodule properly above `L ≤ N` inside `N` has a minimal member `P`
with `(rad R_x) P + P (rad R_y) ≤ L`. -/
theorem exists_socle_layer {x y : Fin F.m} {L N : Submodule k A}
    (hL : F.IsEndpointSubbimodule x y L) (hN : F.IsEndpointSubbimodule x y N) (hLN : L < N) :
    ∃ P, F.IsEndpointSubbimodule x y P ∧ L < P ∧ P ≤ N ∧
      F.cornerRadical (k := k) x * P ⊔ P * F.cornerRadical (k := k) y ≤ L := by
  obtain ⟨P, ⟨hP, hLP, hPN⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun P : Submodule k A ↦ F.IsEndpointSubbimodule x y P ∧ L < P ∧ P ≤ N) ⟨N, hN, hLN, le_rfl⟩
  refine ⟨P, hP, hLP, hPN, ?_⟩
  set Q := L ⊔ (F.cornerRadical (k := k) x * P ⊔ P * F.cornerRadical (k := k) y)
  have hQ : F.IsEndpointSubbimodule x y Q := F.isEndpoint_sup hL (F.isEndpoint_rad hP)
  have hrle : F.cornerRadical (k := k) x * P ⊔ P * F.cornerRadical (k := k) y ≤ P :=
    sup_le (Submodule.mul_le.2 fun r hr n hn ↦ hP.2.1 r (F.cornerRadical_le_corner x hr) n hn)
      (Submodule.mul_le.2 fun n hn r hr ↦ hP.2.2 r (F.cornerRadical_le_corner y hr) n hn)
  have hQP : Q ≤ P := sup_le hLP.le hrle
  by_cases hQL : Q ≤ L
  · exact le_sup_right.trans hQL
  · exfalso
    have hLQ : L < Q := lt_of_le_of_ne le_sup_left (fun h ↦ hQL (h ▸ le_rfl))
    have hPQ : P ≤ Q := hmin ⟨hQ, hLQ, hQP.trans hPN⟩ hQP
    have := F.le_of_le_rad (x := x) (y := y)
      (Submodule.mul_le.2 fun r hr n hn ↦ hL.2.1 r (F.cornerRadical_le_corner x hr) n hn)
      (Submodule.mul_le.2 fun n hn r hr ↦ hL.2.2 r (F.cornerRadical_le_corner y hr) n hn)
      (P := P) (hPQ.trans (le_of_eq (sup_comm L _)))
    exact (not_le_of_gt hLP) this

/-- **Lemma 3.1(3)**: the endpoint subbimodules form a chain. -/
theorem isChain_subbimodules (hA : IsRepresentationFinite k A) (x y : Fin F.m) :
    IsChain (· ≤ ·) {N : Submodule k A | F.IsEndpointSubbimodule x y N} := by
  intro N₁ h₁ N₂ h₂ _
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h21⟩ := hcon
  have hI := F.isEndpoint_inf h₁ h₂
  obtain ⟨P₁, hP₁, hlt₁, hle₁, hr₁⟩ := F.exists_socle_layer hI h₁
    (lt_of_le_of_ne inf_le_left fun h ↦ h12 (h ▸ inf_le_right))
  obtain ⟨P₂, hP₂, hlt₂, hle₂, hr₂⟩ := F.exists_socle_layer hI h₂
    (lt_of_le_of_ne inf_le_right fun h ↦ h21 (h ▸ inf_le_left))
  obtain ⟨s₁, hs₁, hs₁'⟩ := SetLike.exists_of_lt hlt₁
  obtain ⟨s₂, hs₂, hs₂'⟩ := SetLike.exists_of_lt hlt₂
  have hs₁N₂ : s₁ ∉ N₂ := fun h ↦ hs₁' ⟨hle₁ hs₁, h⟩
  have hs₂N₁ : s₂ ∉ N₁ := fun h ↦ hs₂' ⟨h, hle₂ hs₂⟩
  let L : k → Submodule k A := fun t ↦ (N₁ ⊓ N₂) ⊔ Submodule.span k {s₁ + t • s₂}
  have hPP := F.isEndpoint_sup hP₁ hP₂
  have hrad : F.cornerRadical (k := k) x * (P₁ ⊔ P₂) ⊔ (P₁ ⊔ P₂) * F.cornerRadical (k := k) y ≤
      N₁ ⊓ N₂ := by
    rw [Submodule.mul_sup, Submodule.sup_mul]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_left.trans hr₁
    · exact le_sup_left.trans hr₂
    · exact le_sup_right.trans hr₁
    · exact le_sup_right.trans hr₂
  have hL : ∀ t, F.IsEndpointSubbimodule x y (L t) := fun t ↦
    F.isEndpoint_between hPP le_sup_left
      (sup_le (hlt₁.le.trans le_sup_left)
        ((Submodule.span_le).2 (Set.singleton_subset_iff.2
          (Submodule.add_mem _ (Submodule.mem_sup_left hs₁)
            (Submodule.smul_mem _ t (Submodule.mem_sup_right hs₂)))))) hrad
  have hinj : Function.Injective L := by
    intro t t' h
    have hmem : s₁ + t • s₂ ∈ L t' := h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hn' : n = s₁ + t • s₂ - c • (s₁ + t' • s₂) := by rw [← hnz]; abel
    have key : (1 - c) • s₁ + (t - c * t') • s₂ = n := by
      rw [hn']
      simp only [sub_smul, one_smul, smul_add, mul_smul]
      abel
    have hc : c = 1 := by
      by_contra hc1
      have : (1 - c) • s₁ ∈ N₂ := by
        have h2 : (t - c * t') • s₂ ∈ N₂ := Submodule.smul_mem _ _ (hle₂ hs₂)
        have := Submodule.sub_mem _ hn.2 h2
        rwa [← key, add_sub_cancel_right] at this
      apply hs₁N₂
      have h1c : (1 - c) ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
      have := Submodule.smul_mem _ (1 - c)⁻¹ this
      rwa [smul_smul, inv_mul_cancel₀ h1c, one_smul] at this
    subst hc
    by_contra htt
    have : (t - 1 * t') • s₂ ∈ N₁ := by
      have := hn.1
      rwa [← key, sub_self, zero_smul, zero_add] at this
    apply hs₂N₁
    have hne : t - 1 * t' ≠ 0 := by rw [one_mul]; exact sub_ne_zero.2 htt
    have := Submodule.smul_mem _ (t - 1 * t')⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hfin := F.finite_subbimodules hA x y
  exact Set.infinite_of_injective_forall_mem hinj hL hfin

/-- Consecutive endpoint subbimodules have one-dimensional quotient. -/
theorem finrank_succ_of_consecutive {x y : Fin F.m} {N N' : Submodule k A}
    (hN : F.IsEndpointSubbimodule x y N) (hN' : F.IsEndpointSubbimodule x y N') (hlt : N < N')
    (hcons : ∀ N'', F.IsEndpointSubbimodule x y N'' → N ≤ N'' → N'' ≤ N' → N'' = N ∨ N'' = N') :
    Module.finrank k N' = Module.finrank k N + 1 := by
  obtain ⟨P, hP, hNP, hPN', hr⟩ := F.exists_socle_layer hN hN' hlt
  rcases hcons P hP hNP.le hPN' with h | h
  · exact absurd h (ne_of_gt hNP)
  subst h
  obtain ⟨v, hv, hvN⟩ := SetLike.exists_of_lt hNP
  have hQ := F.isEndpoint_between hP (le_sup_left : N ≤ N ⊔ Submodule.span k {v})
    (sup_le hNP.le ((Submodule.span_singleton_le_iff_mem v P).2 hv)) hr
  rcases hcons _ hQ le_sup_left (sup_le hNP.le ((Submodule.span_singleton_le_iff_mem v P).2 hv))
    with h | h
  · exact absurd (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)) hvN
  · rw [← h]
    have hv0 : v ≠ 0 := fun h0 ↦ hvN (h0 ▸ N.zero_mem)
    have hinf : N ⊓ Submodule.span k {v} = ⊥ := by
      rw [eq_bot_iff]
      intro z ⟨hzN, hzv⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hzv
      rw [Submodule.mem_bot]
      by_contra hc
      have hc' : c ≠ 0 := fun h0 ↦ hc (by rw [h0, zero_smul])
      apply hvN
      have := N.smul_mem c⁻¹ hzN
      rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    have := Submodule.finrank_sup_add_finrank_inf_eq N (Submodule.span k {v})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at this
    exact this

/-- **Lemma 3.1(3)**, last part: `R_x f R_y = R_x f` or `f R_y`. -/
theorem endpointSpan_one_sided (hA : IsRepresentationFinite k A) {x y : Fin F.m} {f : A}
    (hf : f ∈ F.corner (k := k) x y) :
    F.endpointSpan (k := k) x y f =
        Submodule.span k {g | ∃ a ∈ F.corner (k := k) x x, g = a * f} ∨
      F.endpointSpan (k := k) x y f =
        Submodule.span k {g | ∃ b ∈ F.corner (k := k) y y, g = f * b} := by
  classical
  set Cx := F.corner (k := k) x x
  set Cy := F.corner (k := k) y y
  set Rx := F.cornerRadical (k := k) x
  set Ry := F.cornerRadical (k := k) y
  set U := F.endpointSpan (k := k) x y f
  set Lx := Submodule.span k {g | ∃ a ∈ Cx, g = a * f}
  set Ly := Submodule.span k {g | ∃ b ∈ Cy, g = f * b}
  have hfl := (F.corner_mul_mem hf).1
  have hfr := (F.corner_mul_mem hf).2
  have hmulx : ∀ {a a'}, a ∈ Cx → a' ∈ Cx → a * a' ∈ Cx := fun {a a'} ha ha' ↦
    (F.mem_corner_iff' (k := k)).2 (by
      rw [← (F.mem_corner_iff' (k := k)).1 ha, ← (F.mem_corner_iff' (k := k)).1 ha']
      simp only [mul_assoc, (F.complete.idem x).eq]
      rw [← mul_assoc (F.e x) (F.e x), (F.complete.idem x).eq])
  have hmuly : ∀ {b b'}, b ∈ Cy → b' ∈ Cy → b * b' ∈ Cy := fun {b b'} hb hb' ↦
    (F.mem_corner_iff' (k := k)).2 (by
      rw [← (F.mem_corner_iff' (k := k)).1 hb, ← (F.mem_corner_iff' (k := k)).1 hb']
      simp only [mul_assoc, (F.complete.idem y).eq]
      rw [← mul_assoc (F.e y) (F.e y), (F.complete.idem y).eq])
  have hgenU : ∀ {a b}, a ∈ Cx → b ∈ Cy → a * f * b ∈ U := fun ha hb ↦
    Submodule.subset_span ⟨_, ha, _, hb, rfl⟩
  have hfU : f ∈ U := by
    have := hgenU (F.e_mem_corner x) (F.e_mem_corner y)
    rwa [hfl, hfr] at this
  -- `U` is a subbimodule
  have hU : F.IsEndpointSubbimodule x y U := by
    refine ⟨Submodule.span_le.2 ?_, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact (F.mem_corner_iff' (k := k)).2 (by
        rw [← (F.mem_corner_iff' (k := k)).1 ha, ← (F.mem_corner_iff' (k := k)).1 hb]
        simp only [mul_assoc, (F.complete.idem x).eq, (F.complete.idem y).eq]
        rw [← mul_assoc (F.e x) (F.e x), (F.complete.idem x).eq])
    · induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨a', ha', b, hb, rfl⟩ := hg
          rw [← mul_assoc, ← mul_assoc]; exact hgenU (hmulx ha ha') hb
      | zero => simp
      | add g h _ _ hg hh => rw [mul_add]; exact U.add_mem hg hh
      | smul c g _ hg => rw [mul_smul_comm]; exact U.smul_mem c hg
    · induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨a, ha, b', hb', rfl⟩ := hg
          rw [mul_assoc]; exact hgenU ha (hmuly hb' hb)
      | zero => simp
      | add g h _ _ hg hh => rw [add_mul]; exact U.add_mem hg hh
      | smul c g _ hg => rw [smul_mul_assoc]; exact U.smul_mem c hg
  have hRxU_le : Rx * U ≤ U := Submodule.mul_le.2 fun r hr u hu ↦
    hU.2.1 r (F.cornerRadical_le_corner x hr) u hu
  have hURy_le : U * Ry ≤ U := Submodule.mul_le.2 fun u hu r hr ↦
    hU.2.2 r (F.cornerRadical_le_corner y hr) u hu
  have hRxU : F.IsEndpointSubbimodule x y (Rx * U) := by
    refine ⟨hRxU_le.trans hU.1, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
    · refine Submodule.mul_induction_on hz (fun r hr u hu ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (F.radL_mem ha hr) hu
      · rw [mul_add]; exact Submodule.add_mem _ hp hq
    · refine Submodule.mul_induction_on hz (fun r hr u hu ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hr (hU.2.2 b hb u hu)
      · rw [add_mul]; exact Submodule.add_mem _ hp hq
  have hURy : F.IsEndpointSubbimodule x y (U * Ry) := by
    refine ⟨hURy_le.trans hU.1, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
    · refine Submodule.mul_induction_on hz (fun u hu r hr ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (hU.2.1 a ha u hu) hr
      · rw [mul_add]; exact Submodule.add_mem _ hp hq
    · refine Submodule.mul_induction_on hz (fun u hu r hr ↦ ?_) (fun p q hp hq ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hu (F.radR_mem hb hr)
      · rw [add_mul]; exact Submodule.add_mem _ hp hq
  obtain ⟨K, hK⟩ := F.cornerRadical_pow_eq_bot (k := k)
  rcases (F.isChain_subbimodules hA x y).total hRxU hURy with hPQ | hQP
  · -- `(rad R_x) U ≤ U (rad R_y)`: `U = f R_y`
    right
    have hCyLy : ∀ b ∈ Cy, ∀ z ∈ Ly, z * b ∈ Ly := by
      intro b hb z hz
      induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨b', hb', rfl⟩ := hg
          rw [mul_assoc]; exact Submodule.subset_span ⟨_, hmuly hb' hb, rfl⟩
      | zero => simp
      | add g h _ _ hg hh => rw [add_mul]; exact Ly.add_mem hg hh
      | smul c g _ hg => rw [smul_mul_assoc]; exact Ly.smul_mem c hg
    have hCypow : ∀ n, ∀ b ∈ Cy, ∀ z ∈ U * Ry ^ n, z * b ∈ U * Ry ^ n := by
      intro n
      induction n with
      | zero => intro b hb z hz; rw [pow_zero, Submodule.mul_one] at hz ⊢; exact hU.2.2 b hb z hz
      | succ n ih =>
          intro b hb z hz
          rw [pow_succ, ← mul_assoc] at hz ⊢
          refine Submodule.mul_induction_on hz (fun w hw r hr ↦ ?_) (fun p q hp hq ↦ ?_)
          · rw [mul_assoc w r b]; exact Submodule.mul_mem_mul hw (F.radR_mem hb hr)
          · rw [add_mul]; exact Submodule.add_mem _ hp hq
    have key : ∀ n, ∀ a ∈ Cx, a * f ∈ Ly ⊔ U * Ry ^ n := by
      intro n
      induction n with
      | zero =>
          intro a ha
          rw [pow_zero, Submodule.mul_one]
          apply Submodule.mem_sup_right
          have := hgenU ha (F.e_mem_corner y); rwa [mul_assoc, hfr] at this
      | succ n ih =>
          intro a ha
          obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k x ha
          have hr : a - c • F.e x ∈ Rx :=
            ⟨Submodule.sub_mem _ ha (Submodule.smul_mem _ c (F.e_mem_corner x)), hc⟩
          have hsplit : a * f = c • f + (a - c • F.e x) * f := by
            rw [sub_mul, smul_mul_assoc, hfl]; abel
          rw [hsplit]
          refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ c ?_)) ?_
          · exact Submodule.subset_span ⟨F.e y, F.e_mem_corner y, hfr.symm⟩
          · have h1 : (a - c • F.e x) * f ∈ Rx * U := Submodule.mul_mem_mul hr hfU
            have hUle : U ≤ Ly ⊔ U * Ry ^ n := by
              refine Submodule.span_le.2 ?_
              rintro _ ⟨a', ha', b, hb, rfl⟩
              obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.1 (ih a' ha')
              rw [← hlw, add_mul]
              exact Submodule.add_mem_sup (hCyLy b hb l hl) (hCypow n b hb w hw)
            have h2 : U * Ry ≤ Ly ⊔ U * Ry ^ (n + 1) := by
              calc U * Ry ≤ (Ly ⊔ U * Ry ^ n) * Ry := _root_.mul_le_mul_left hUle Ry
                _ = Ly * Ry ⊔ U * Ry ^ (n + 1) := by rw [Submodule.sup_mul, pow_succ, mul_assoc]
                _ ≤ Ly ⊔ U * Ry ^ (n + 1) := sup_le_sup_right (Submodule.mul_le.2 fun z hz r hr ↦
                    hCyLy r (F.cornerRadical_le_corner y hr) z hz) _
            exact h2 (hPQ h1)
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have := key K a ha
      rw [hK y, Submodule.mul_bot, sup_bot_eq] at this
      exact hCyLy b hb _ this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have := hgenU (F.e_mem_corner x) hb
      rwa [hfl] at this
  · -- `U (rad R_y) ≤ (rad R_x) U`: `U = R_x f`
    left
    have hCxLx : ∀ a ∈ Cx, ∀ z ∈ Lx, a * z ∈ Lx := by
      intro a ha z hz
      induction hz using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨a', ha', rfl⟩ := hg
          rw [← mul_assoc]; exact Submodule.subset_span ⟨_, hmulx ha ha', rfl⟩
      | zero => simp
      | add g h _ _ hg hh => rw [mul_add]; exact Lx.add_mem hg hh
      | smul c g _ hg => rw [mul_smul_comm]; exact Lx.smul_mem c hg
    have hCxpow : ∀ n, ∀ a ∈ Cx, ∀ z ∈ Rx ^ n * U, a * z ∈ Rx ^ n * U := by
      intro n
      induction n with
      | zero => intro a ha z hz; rw [pow_zero, Submodule.one_mul] at hz ⊢; exact hU.2.1 a ha z hz
      | succ n ih =>
          intro a ha z hz
          rw [pow_succ', mul_assoc] at hz ⊢
          refine Submodule.mul_induction_on hz (fun r hr w hw ↦ ?_) (fun p q hp hq ↦ ?_)
          · rw [← mul_assoc a r w]; exact Submodule.mul_mem_mul (F.radL_mem ha hr) hw
          · rw [mul_add]; exact Submodule.add_mem _ hp hq
    have key : ∀ n, ∀ b ∈ Cy, f * b ∈ Lx ⊔ Rx ^ n * U := by
      intro n
      induction n with
      | zero =>
          intro b hb
          rw [pow_zero, Submodule.one_mul]
          apply Submodule.mem_sup_right
          have := hgenU (F.e_mem_corner x) hb; rwa [hfl] at this
      | succ n ih =>
          intro b hb
          obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k y hb
          have hr : b - c • F.e y ∈ Ry :=
            ⟨Submodule.sub_mem _ hb (Submodule.smul_mem _ c (F.e_mem_corner y)), hc⟩
          have hsplit : f * b = c • f + f * (b - c • F.e y) := by
            rw [mul_sub, mul_smul_comm, hfr]; abel
          rw [hsplit]
          refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ c ?_)) ?_
          · exact Submodule.subset_span ⟨F.e x, F.e_mem_corner x, hfl.symm⟩
          · have h1 : f * (b - c • F.e y) ∈ U * Ry := Submodule.mul_mem_mul hfU hr
            have hUle : U ≤ Lx ⊔ Rx ^ n * U := by
              refine Submodule.span_le.2 ?_
              rintro _ ⟨a, ha, b', hb', rfl⟩
              obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.1 (ih b' hb')
              rw [mul_assoc, ← hlw, mul_add]
              exact Submodule.add_mem_sup (hCxLx a ha l hl) (hCxpow n a ha w hw)
            have h2 : Rx * U ≤ Lx ⊔ Rx ^ (n + 1) * U := by
              calc Rx * U ≤ Rx * (Lx ⊔ Rx ^ n * U) := _root_.mul_le_mul_right hUle Rx
                _ = Rx * Lx ⊔ Rx ^ (n + 1) * U := by rw [Submodule.mul_sup, pow_succ', mul_assoc]
                _ ≤ Lx ⊔ Rx ^ (n + 1) * U := sup_le_sup_right (Submodule.mul_le.2 fun r hr z hz ↦
                    hCxLx r (F.cornerRadical_le_corner x hr) z hz) _
            exact h2 (hQP h1)
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have := key K b hb
      rw [hK x, Submodule.bot_mul, sup_bot_eq] at this
      rw [mul_assoc]
      exact hCxLx a ha _ this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      have := hgenU ha (F.e_mem_corner y)
      rwa [mul_assoc, hfr] at this

end PrimitiveIdempotents

end Corners

end MultiplicativeBasisDeformations
