import MultiplicativeBasisDeformations.Foundations.GradedRays
import MultiplicativeBasisDeformations.Foundations.NormedTransport
import MultiplicativeBasisDeformations.Foundations.BasicLabels
import MultiplicativeBasisDeformations.Foundations.BasicCorner

/-!
# Transport of ray bases

Corollary 5.5 (`mesh-deformations.tex:265–268`): the isomorphism `A ≅ A₀`
"preserves endpoint actions and the subspaces `M(f,h)` of Definition 3.4, and
therefore identifies `ray A` with `P`". Here: an algebra isomorphism matching
the chosen primitive idempotents carries corners, corner radicals, corner units,
rays and the spaces `M(f,h)` (`ray_fwd`, `insertionSpan_fwd`), hence ray bases
(`hasRayBasis_of_algEquiv`).

The rays are defined relative to a complete set of primitive idempotents. In a
basic algebra any two complete sets are conjugate (`exists_algEquiv_idempotents`),
so a ray basis for one set gives one for any other.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

section NormedMap

variable {k : Type u} [Field k] {A B : Type v} [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- **Transport of a normed multiplicative basis** along an algebra isomorphism. -/
theorem IsNormedMultiplicativeBasis.map_algEquiv (φ : A ≃ₐ[k] B) {ι : Type*}
    {b : Module.Basis ι k B} (hb : IsNormedMultiplicativeBasis b) :
    IsNormedMultiplicativeBasis (b.map φ.symm.toLinearEquiv) := by
  have hb' : ∀ i, b.map φ.symm.toLinearEquiv i = φ.symm (b i) := fun i ↦ rfl
  refine ⟨fun i j ↦ ?_, ?_, fun n hn ↦ ?_⟩
  · rw [hb', hb', ← map_mul]
    rcases hb.multiplicative i j with h0 | ⟨l, hl⟩
    · left; rw [h0, map_zero]
    · right; exact ⟨l, by rw [hl, hb']⟩
  · obtain ⟨E, hE, hprim⟩ := hb.idempotents
    refine ⟨E, ?_, fun i hi ↦ ?_⟩
    · exact hE.map (φ.symm : B →+* A)
    · rw [hb']
      exact isPrimitiveIdempotent_map φ.symm (hprim i hi)
  · have h := hb.radicalPow n hn
    have hmap := congrArg (Submodule.map φ.symm.toLinearMap) h
    rw [Submodule.map_span, map_algebraRadicalPow φ.symm n] at hmap
    refine Eq.trans ?_ hmap
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨b i, ⟨i, ?_, rfl⟩, rfl⟩
      have := Submodule.mem_map_of_mem (f := φ.toLinearMap) hi
      rw [map_algebraRadicalPow φ n] at this
      change φ (φ.symm (b i)) ∈ _ at this
      rwa [φ.apply_symm_apply] at this
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨i, ?_, rfl⟩
      rw [← map_algebraRadicalPow φ.symm n]
      exact Submodule.mem_map_of_mem hi

end NormedMap

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Type v} [Ring A] [Ring B] [Algebra k A]
  [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
  (ψ : A ≃ₐ[k] B) (F : PrimitiveIdempotents A) (F' : PrimitiveIdempotents B)
  (σ : Fin F.m ≃ Fin F'.m) (hψ : ∀ i, ψ (F.e i) = F'.e (σ i))

include hψ

theorem corner_fwd {i j : Fin F.m} {a : A} (ha : a ∈ F.corner (k := k) i j) :
    ψ a ∈ F'.corner (k := k) (σ i) (σ j) := by
  rw [F'.mem_corner_iff', ← hψ, ← hψ, ← map_mul, ← map_mul, (F.mem_corner_iff').1 ha]

omit hψ in
theorem radical_fwd {a : A} (ha : a ∈ algebraRadical k A) : ψ a ∈ algebraRadical k B :=
  jacobson_map_mem ψ.toRingEquiv ha

theorem cornerRadical_fwd {i : Fin F.m} {a : A} (ha : a ∈ F.cornerRadical (k := k) i) :
    ψ a ∈ F'.cornerRadical (k := k) (σ i) :=
  ⟨F.corner_fwd ψ F' σ hψ ha.1, radical_fwd ψ ha.2⟩

theorem unit_fwd {i : Fin F.m} {u : A} (hu : F.IsCornerUnit (k := k) i u) :
    F'.IsCornerUnit (k := k) (σ i) (ψ u) := by
  obtain ⟨hu, u', hu', h1, h2⟩ := hu
  exact ⟨F.corner_fwd ψ F' σ hψ hu, ψ u', F.corner_fwd ψ F' σ hψ hu',
    by rw [← map_mul, h1, hψ], by rw [← map_mul, h2, hψ]⟩

theorem ray_fwd {i j : Fin F.m} {f g : A} (hg : g ∈ F.ray (k := k) i j f) :
    ψ g ∈ F'.ray (k := k) (σ i) (σ j) (ψ f) := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hg
  exact ⟨ψ u, ψ w, F.unit_fwd ψ F' σ hψ hu, F.unit_fwd ψ F' σ hψ hw, by simp only [map_mul]⟩

theorem insertionSpan_fwd {i j l : Fin F.m} {f h g : A}
    (hg : g ∈ F.insertionSpan (k := k) i j l f h) :
    ψ g ∈ F'.insertionSpan (k := k) (σ i) (σ j) (σ l) (ψ f) (ψ h) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, ha, r, hr, b, hb, rfl⟩ := hg
      exact Submodule.subset_span ⟨ψ a, F.corner_fwd ψ F' σ hψ ha, ψ r,
        F.cornerRadical_fwd ψ F' σ hψ hr, ψ b, F.corner_fwd ψ F' σ hψ hb, by simp only [map_mul]⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add g g' _ _ hg hg' => rw [map_add]; exact Submodule.add_mem _ hg hg'
  | smul c g _ hg => rw [map_smul]; exact Submodule.smul_mem _ c hg

theorem symm_e (j : Fin F'.m) : ψ.symm (F'.e j) = F.e (σ.symm j) := by
  rw [← σ.apply_symm_apply j, ← hψ, ψ.symm_apply_apply, σ.symm_apply_apply]

theorem image_ray (i j : Fin F.m) (f : A) :
    ψ '' F.ray (k := k) i j f = F'.ray (k := k) (σ i) (σ j) (ψ f) := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact F.ray_fwd ψ F' σ hψ hg
  · intro hg'
    have := F'.ray_fwd ψ.symm F σ.symm (F.symm_e ψ F' σ hψ) hg'
    rw [σ.symm_apply_apply, σ.symm_apply_apply, ψ.symm_apply_apply] at this
    exact ⟨_, this, ψ.apply_symm_apply g'⟩

/-- The image of a nonzero ray. -/
def rayMap (r : F.NonzeroRay k) : F'.NonzeroRay k :=
  ⟨ψ '' r.1, by
    obtain ⟨i, j, f, hf, hf0, hr⟩ := r.2
    exact ⟨σ i, σ j, ψ f, F.corner_fwd ψ F' σ hψ hf,
      fun h ↦ hf0 (ψ.injective (by rw [h, map_zero])), by rw [hr, F.image_ray ψ F' σ hψ]⟩⟩

theorem rayMap_val (r : F.NonzeroRay k) : (F.rayMap ψ F' σ hψ r).1 = ψ '' r.1 := rfl

/-- Nonzero rays correspond under `ψ`. -/
def rayEquiv : F.NonzeroRay k ≃ F'.NonzeroRay k where
  toFun := F.rayMap ψ F' σ hψ
  invFun := F'.rayMap ψ.symm F σ.symm (F.symm_e ψ F' σ hψ)
  left_inv r := Subtype.ext (by
    change ψ.symm '' (ψ '' r.1) = r.1
    rw [Set.image_image]
    simp only [AlgEquiv.symm_apply_apply, Set.image_id'])
  right_inv r := Subtype.ext (by
    change ψ '' (ψ.symm '' r.1) = r.1
    rw [Set.image_image]
    simp only [AlgEquiv.apply_symm_apply, Set.image_id'])

/-- **Ray bases transport along an algebra isomorphism matching the idempotents.** -/
theorem hasRayBasis_of_algEquiv (h : F'.HasRayBasis k) : F.HasRayBasis k := by
  obtain ⟨b', hn, ⟨hmem, hid⟩, hkill⟩ := h
  set R := F.rayEquiv ψ F' σ hψ
  let b : Module.Basis (F.NonzeroRay k) k A := (b'.map ψ.symm.toLinearEquiv).reindex R.symm
  have hb : ∀ r, b r = ψ.symm (b' (R r)) := fun r ↦ by
    simp only [b, Module.Basis.reindex_apply, Equiv.symm_symm]; rfl
  have hbψ : ∀ r, ψ (b r) = b' (R r) := fun r ↦ by rw [hb, ψ.apply_symm_apply]
  refine ⟨b, (hn.map_algEquiv ψ).reindex R.symm, ⟨fun r ↦ ?_, fun r i hi ↦ ?_⟩,
    fun r s i j l hr hs hM ↦ ?_⟩
  · obtain ⟨g, hg, hgb⟩ := (hmem (R r))
    rw [hb, ← hgb, ψ.symm_apply_apply]
    exact hg
  · have : F'.e (σ i) ∈ (R r).1 := ⟨F.e i, hi, hψ i⟩
    rw [hb, hid (R r) (σ i) this, F.symm_e ψ F' σ hψ, σ.symm_apply_apply]
  · have hr' := F.corner_fwd ψ F' σ hψ hr
    have hs' := F.corner_fwd ψ F' σ hψ hs
    have hM' := F.insertionSpan_fwd ψ F' σ hψ hM
    rw [map_mul, hbψ, hbψ] at hM'
    rw [hbψ] at hr' hs'
    have := hkill (R r) (R s) _ _ _ hr' hs' hM'
    apply ψ.injective
    rw [map_mul, hbψ, hbψ, this, map_zero]

end PrimitiveIdempotents

section Conjugacy

open BasicCorner

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

/-- Conjugation `a ↦ W' a W` by mutually inverse elements. -/
def conjAlgEquiv (W W' : A) (h1 : W * W' = 1) (h2 : W' * W = 1) : A ≃ₐ[k] A where
  toFun a := W' * a * W
  invFun a := W * a * W'
  left_inv a := by
    change W * (W' * a * W) * W' = a
    calc W * (W' * a * W) * W' = (W * W') * a * (W * W') := by simp only [mul_assoc]
      _ = a := by rw [h1, one_mul, mul_one]
  right_inv a := by
    change W' * (W * a * W') * W = a
    calc W' * (W * a * W') * W = (W' * W) * a * (W' * W) := by simp only [mul_assoc]
      _ = a := by rw [h2, one_mul, mul_one]
  map_mul' a b := by
    change W' * (a * b) * W = W' * a * W * (W' * b * W)
    calc W' * (a * b) * W = W' * a * 1 * b * W := by rw [mul_one]; simp only [mul_assoc]
      _ = _ := by rw [← h1]; simp only [mul_assoc]
  map_add' a b := by
    change W' * (a + b) * W = W' * a * W + W' * b * W
    rw [mul_add, add_mul]
  commutes' c := by
    change W' * algebraMap k A c * W = algebraMap k A c
    rw [← Algebra.commutes, mul_assoc, h2, mul_one]

variable [IsAlgClosed k] [FiniteDimensional k A]

/-- **A basic set of idempotents is conjugate to any complete set of primitive
orthogonal idempotents.** -/
theorem exists_conj_to {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
    (hprim : ∀ i, IsPrimitiveIdempotent (e i))
    (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
      y * x = e j) → i = j) (F : PrimitiveIdempotents A) :
    ∃ (τ : Fin n ≃ Fin F.m) (ψ : A ≃ₐ[k] A), ∀ j, ψ (e j) = F.e (τ j) := by
  classical
  have hiso : ∀ j, ∃ i, IsoData (e j) (F.e i) := fun j ↦ by
    obtain ⟨i, ⟨φ⟩⟩ := exists_iso_ideal k (hprim j) F.complete F.primitive
    exact ⟨i, basic_data_of_iso (hprim j).1 (F.primitive i).1 φ⟩
  choose τ hτ using hiso
  choose x y h1 h2 h3 h4 using hτ
  have hτinj : Function.Injective τ := by
    intro j j' h
    apply hbasic
    have hd : IsoData (e j) (e j') := by
      refine (IsoData.trans (hprim j).1 (F.primitive _).1 (hprim j').1 ⟨x j, y j, h1 j, h2 j, h3 j,
        h4 j⟩ ?_)
      rw [h]
      exact IsoData.symm ⟨x j', y j', h1 j', h2 j', h3 j', h4 j'⟩
    exact hd
  have hxe : ∀ j, x j * F.e (τ j) = x j := fun j ↦ right_of_sandwich (F.primitive _).1 (h1 j)
  have hfy : ∀ j, F.e (τ j) * y j = y j := fun j ↦ left_of_sandwich (F.primitive _).1 (h2 j)
  have hye : ∀ j, y j * e j = y j := fun j ↦ right_of_sandwich (hprim j).1 (h2 j)
  have hex : ∀ j, e j * x j = x j := fun j ↦ left_of_sandwich (hprim j).1 (h1 j)
  have hxy : ∀ j j', x j * y j' = if j = j' then e j else 0 := by
    intro j j'
    split_ifs with h
    · subst h; exact h3 j
    · rw [← hxe j, ← hfy j', mul_assoc, ← mul_assoc (F.e (τ j)),
        F.complete.ortho (hτinj.ne h), zero_mul, mul_zero]
  have hyx : ∀ j j', y j' * x j = if j' = j then F.e (τ j) else 0 := by
    intro j j'
    split_ifs with h
    · subst h; exact h4 j'
    · rw [← hye j', ← hex j, mul_assoc, ← mul_assoc (e j'), he.ortho h, zero_mul, mul_zero]
  set W := ∑ j, x j
  set W' := ∑ j, y j
  have hWW' : W * W' = 1 := by
    simp only [W, W', Finset.sum_mul, Finset.mul_sum, hxy, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact he.complete
  have := dedekindFinite k A
  have hW'W : W' * W = 1 := mul_eq_one_comm.1 hWW'
  have hsum : ∑ j, F.e (τ j) = 1 := by
    rw [← hW'W]
    simp only [W, W', Finset.sum_mul, Finset.mul_sum, hyx, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have hτsurj : Function.Surjective τ := by
    intro i
    by_contra hi
    push Not at hi
    apply (F.primitive i).2.1
    rw [← mul_one (F.e i), ← hsum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ ↦ F.complete.ortho (Ne.symm (hi j))
  refine ⟨Equiv.ofBijective τ ⟨hτinj, hτsurj⟩, conjAlgEquiv W W' hWW' hW'W, fun j ↦ ?_⟩
  change W' * e j * W = F.e (τ j)
  have hW'e : W' * e j = y j := by
    simp only [W', Finset.sum_mul]
    rw [Finset.sum_eq_single j (fun j' _ hj' ↦ by rw [← hye j', mul_assoc, he.ortho hj',
      mul_zero]) (fun h ↦ absurd (Finset.mem_univ j) h), hye]
  rw [hW'e]
  simp only [W, Finset.mul_sum, hyx, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **In a basic algebra any two complete sets of primitive orthogonal
idempotents are conjugate.** -/
theorem exists_algEquiv_idempotents {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hbasic : IsBasicAlgebra A) (F F' : PrimitiveIdempotents A) :
    ∃ (ψ : A ≃ₐ[k] A) (σ : Fin F.m ≃ Fin F'.m), ∀ i, ψ (F.e i) = F'.e (σ i) := by
  obtain ⟨n, e, he, hprim, hb⟩ := hbasic
  obtain ⟨τ, ψ, hψ⟩ := exists_conj_to (k := k) he hprim hb F
  obtain ⟨τ', ψ', hψ'⟩ := exists_conj_to (k := k) he hprim hb F'
  refine ⟨ψ.symm.trans ψ', τ.symm.trans τ', fun i ↦ ?_⟩
  rw [AlgEquiv.trans_apply, ← τ.apply_symm_apply i, ← hψ, ψ.symm_apply_apply, hψ',
    τ.apply_symm_apply]
  rfl

end Conjugacy

end MultiplicativeBasisDeformations
