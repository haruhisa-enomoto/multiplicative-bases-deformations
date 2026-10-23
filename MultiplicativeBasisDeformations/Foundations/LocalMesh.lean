module

public import MultiplicativeBasisDeformations.Foundations.CategoryAlgebra

/-!
# Local families with exact right meshes

The structure of `C = gr_J ind(mod A)` used in the proof of Proposition 2.10
(`graded-category.tex`): the positive-degree ideal is the
categorical radical, it is nilpotent, each degree-zero endomorphism ring is `k`,
and degree-zero maps between distinct objects vanish (Lemma 2.7); the right
mesh map at each label has image the radical (Lemma 2.7), and at a
nonprojective label the right mesh is exact in both variables
(Proposition 2.6(1)); at a projective label the mesh map is monic
(Proposition 2.6(2)).

We record these properties for a finite family of objects of a `k`-linear
category (`LocalFamily`, `MeshData`), and derive the module-theoretic
consequences over the category algebra `Λ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → 𝒞)

/-- A family of objects with local endomorphism rings with residue field `k`
and a nilpotent radical containing all maps between distinct objects. -/
structure LocalFamily where
  /-- The radical. -/
  rad : ∀ x y : ι, Submodule k (F x ⟶ F y)
  comp_left : ∀ {x y z : ι} (f : F x ⟶ F y) {g : F y ⟶ F z}, g ∈ rad y z → f ≫ g ∈ rad x z
  comp_right : ∀ {x y z : ι} {f : F x ⟶ F y}, f ∈ rad x y → ∀ g : F y ⟶ F z, f ≫ g ∈ rad x z
  mem_of_ne : ∀ {x y : ι}, x ≠ y → ∀ f : F x ⟶ F y, f ∈ rad x y
  diag : ∀ (x : ι) (f : F x ⟶ F x), ∃ c : k, f - c • 𝟙 (F x) ∈ rad x x
  id_not_mem : ∀ x : ι, 𝟙 (F x) ∉ rad x x
  nilpotent : ∀ (x : ι) (f : End (F x)), f ∈ rad x x → IsNilpotent f
  /-- The radical ideal of `Λ` is nilpotent. -/
  idealNilp : ∃ N : ℕ, ∀ l : List (Alg F), N ≤ l.length →
    (∀ a ∈ l, ∀ y z, a y z ∈ rad y z) → l.prod = 0

/-- The right meshes: at each `x`, arrows `p_a : F (mid a) → F x` whose sums of
composites give exactly the radical; at a nonprojective `x` a translate `τ x`
with `q_a : F (τ x) → F (mid a)`, exact in both variables; at a projective `x`
the mesh map is monic. -/
structure MeshData (L : LocalFamily (k := k) F) where
  Mid : ι → Type
  [fin : ∀ x, Fintype (Mid x)]
  [decMid : ∀ x, DecidableEq (Mid x)]
  mid : ∀ x, Mid x → ι
  p : ∀ x (a : Mid x), F (mid x a) ⟶ F x
  p_rad : ∀ x a, p x a ∈ L.rad _ _
  image : ∀ (x w : ι) (f : F w ⟶ F x), f ∈ L.rad w x →
    ∃ g : ∀ a : Mid x, F w ⟶ F (mid x a), f = ∑ a, g a ≫ p x a
  proj : ι → Prop
  [decProj : DecidablePred proj]
  tau : ∀ x, ¬ proj x → ι
  q : ∀ x (hx : ¬ proj x) (a : Mid x), F (tau x hx) ⟶ F (mid x a)
  comp_zero : ∀ x (hx : ¬ proj x), ∑ a, q x hx a ≫ p x a = 0
  cov_exact : ∀ x (hx : ¬ proj x) (w : ι) (g : ∀ a : Mid x, F w ⟶ F (mid x a)),
    ∑ a, g a ≫ p x a = 0 → ∃ z : F w ⟶ F (tau x hx), ∀ a, g a = z ≫ q x hx a
  cov_mono : ∀ x (hx : ¬ proj x) (w : ι) (z : F w ⟶ F (tau x hx)), (∀ a, z ≫ q x hx a = 0) → z = 0
  contra_exact : ∀ x (hx : ¬ proj x) (w : ι) (v : ∀ a : Mid x, F (mid x a) ⟶ F w),
    ∑ a, q x hx a ≫ v a = 0 → ∃ u : F x ⟶ F w, ∀ a, v a = p x a ≫ u
  contra_mono : ∀ x (hx : ¬ proj x) (w : ι) (u : F x ⟶ F w), (∀ a, p x a ≫ u = 0) → u = 0
  proj_mono : ∀ x, proj x → ∀ (w : ι) (g : ∀ a : Mid x, F w ⟶ F (mid x a)),
    ∑ a, g a ≫ p x a = 0 → ∀ a, g a = 0

attribute [instance] MeshData.fin MeshData.decMid MeshData.decProj

namespace LocalFamily

variable {F} (L : LocalFamily (k := k) F)

/-- The radical of `R_X`. -/
def radRep (x : ι) : Submodule (Alg F) (Rep F (F x)) where
  carrier := {m | ∀ y, m y ∈ L.rad y x}
  add_mem' hm hn y := add_mem (hm y) (hn y)
  zero_mem' y := zero_mem _
  smul_mem' a m hm y := by
    rw [Rep.smul_apply]
    exact Submodule.sum_mem _ fun z _ ↦ L.comp_left _ (hm z)

/-- An endomorphism `c 1 + r` with `c ≠ 0` and `r` radical is invertible. -/
theorem isUnit_of_not_mem {x : ι} {f : End (F x)} (hf : f ∉ L.rad x x) : IsUnit f := by
  obtain ⟨c, hc⟩ := L.diag x f
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_zero] at hc
    exact hf hc
  have hu : IsUnit (c • (1 : End (F x))) := by
    rw [← Algebra.algebraMap_eq_smul_one]; exact (IsUnit.mk0 c hc0).map _
  have hnil := L.nilpotent x (f - c • 1) hc
  have := hnil.isUnit_add_left_of_commute hu (Commute.smul_right (Commute.one_right _) c)
  rwa [add_sub_cancel] at this

theorem unit_mem_span {x : ι} {m : Rep F (F x)} (hm : m x ∉ L.rad x x) :
    unit x ∈ Submodule.span (Alg F) {m} := by
  have hu := L.isUnit_of_not_mem (f := (m x : End (F x))) hm
  set v : F x ⟶ F x := ((hu.unit⁻¹ : (End (F x))ˣ) : End (F x))
  have hv : v ≫ m x = 𝟙 _ := hu.mul_val_inv
  set r : Rep F (F x) := fun y ↦ if y = x then idTo y x ≫ v else 0
  have : colAlg x r • m = unit x := by
    ext y
    rw [Rep.smul_apply]
    simp only [colAlg, Category.assoc]
    rw [← Preadditive.comp_sum, sum_idTo_comp x m]
    simp only [r, unit]
    split_ifs with h
    · subst h; simp [hv]
    · rw [Limits.zero_comp, idTo_ne h]
  rw [← this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m)

theorem unit_not_mem (x : ι) : unit x ∉ L.radRep x := fun h ↦ L.id_not_mem x (by
  have := h x; simpa [unit] using this)

/-- **`R_x` is local**: a submodule not contained in the radical is everything. -/
theorem eq_top_of_not_le {x : ι} {N : Submodule (Alg F) (Rep F (F x))} (h : ¬ N ≤ L.radRep x) :
    N = ⊤ := by
  obtain ⟨m, hmN, hm⟩ := Set.not_subset.1 h
  have hmx : m x ∉ L.rad x x := by
    intro hx
    apply hm
    intro y
    by_cases hy : y = x
    · subst hy; exact hx
    · exact L.mem_of_ne hy _
  have hunit : unit x ∈ N :=
    (Submodule.span_le.2 (Set.singleton_subset_iff.2 hmN)) (L.unit_mem_span hmx)
  rw [eq_top_iff]
  intro r _
  rw [← colAlg_smul_unit x r]
  exact Submodule.smul_mem _ _ hunit

theorem isCoatom_radRep (x : ι) : IsCoatom (L.radRep x) := by
  refine ⟨fun h ↦ L.unit_not_mem x (h ▸ Submodule.mem_top), fun N hN ↦ ?_⟩
  exact L.eq_top_of_not_le (fun h ↦ hN.not_ge h)

/-- The simple top `L_x = R_x / rad R_x`. -/
abbrev Top (x : ι) := Rep F (F x) ⧸ L.radRep x

instance (x : ι) : IsSimpleModule (Alg F) (L.Top x) :=
  (isSimpleModule_iff_isCoatom).2 (L.isCoatom_radRep x)

theorem sum_idem : ∑ x, idem (F := F) x = 1 := by
  ext y z
  rw [sum_apply, one_apply]
  simp only [idem, colAlg, unit]
  exact sum_idTo_comp y (fun x ↦ idTo (F := F) x z)

/-- A simple module with a nonzero `x`-part is the top `L_x`. -/
theorem iso_top_of_idem {S : Type*} [AddCommGroup S] [Module (Alg F) S] [IsSimpleModule (Alg F) S]
    (x : ι) (s : S) (hx : idem (F := F) x • s ≠ 0) : Nonempty (S ≃ₗ[Alg F] L.Top x) := by
  set φ : Rep F (F x) →ₗ[Alg F] S := ofElem x (idem (F := F) x • s)
  have hφ : φ (unit x) ≠ 0 := by
    rw [ofElem_unit, smul_smul, idem_mul_idem]; exact hx
  have hsurj : Function.Surjective φ := by
    have hr : LinearMap.range φ = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range φ) with h | h
      · exact absurd (h ▸ LinearMap.mem_range_self φ (unit x)) (by
          rw [Submodule.mem_bot]; exact hφ)
      · exact h
    exact LinearMap.range_eq_top.1 hr
  have hker : LinearMap.ker φ = L.radRep x := by
    have hco : IsCoatom (LinearMap.ker φ) := by
      have : IsSimpleModule (Alg F) (Rep F (F x) ⧸ LinearMap.ker φ) :=
        IsSimpleModule.congr (φ.quotKerEquivOfSurjective hsurj)
      exact (isSimpleModule_iff_isCoatom).1 this
    have hle : LinearMap.ker φ ≤ L.radRep x := by
      by_contra h
      exact hco.1 (L.eq_top_of_not_le h)
    exact eq_of_le_of_not_lt hle fun hlt ↦ (L.isCoatom_radRep x).1 (hco.2 _ hlt)
  exact ⟨((φ.quotKerEquivOfSurjective hsurj).symm.trans (Submodule.quotEquivOfEq _ _ hker))⟩

/-- **Simple modules are the tops** `L_x`. -/
theorem exists_iso_top {S : Type*} [AddCommGroup S] [Module (Alg F) S] [IsSimpleModule (Alg F) S] :
    ∃ x, Nonempty (S ≃ₗ[Alg F] L.Top x) := by
  haveI : Nontrivial S := IsSimpleModule.nontrivial (Alg F) S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  have : ∃ x, idem (F := F) x • s ≠ 0 := by
    by_contra h
    push Not at h
    apply hs
    rw [← one_smul (Alg F) s, ← sum_idem (F := F), Finset.sum_smul]
    exact Finset.sum_eq_zero fun x _ ↦ h x
  obtain ⟨x, hx⟩ := this
  exact ⟨x, L.iso_top_of_idem x s hx⟩

end LocalFamily

namespace MeshData

variable {F} {L : LocalFamily (k := k) F} (D : MeshData F L)

/-- The right mesh map `⊕_a R_{mid a} → R_x`. -/
def meshMap (x : ι) : (∀ a : D.Mid x, Rep F (F (D.mid x a))) →ₗ[Alg F] Rep F (F x) :=
  ∑ a, (repMap (D.p x a)).comp (LinearMap.proj a)

theorem meshMap_apply (x : ι) (m : ∀ a : D.Mid x, Rep F (F (D.mid x a))) (y : ι) :
    D.meshMap x m y = ∑ a, m a y ≫ D.p x a := by
  rw [meshMap, LinearMap.sum_apply, Rep.sum_apply]
  rfl

/-- **Lemma 2.7**: the image of the right mesh map is the radical. -/
theorem range_meshMap (x : ι) : LinearMap.range (D.meshMap x) = L.radRep x := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩ y
    rw [meshMap_apply]
    exact Submodule.sum_mem _ fun a _ ↦ L.comp_left _ (D.p_rad x a)
  · intro r hr
    choose g hg using fun y ↦ D.image x y (r y) (hr y)
    refine ⟨fun a ↦ (fun y ↦ g y a : Rep F (F (D.mid x a))), ?_⟩
    ext y
    exact (D.meshMap_apply x _ y).trans (hg y).symm

/-- The left map `R_{τ x} → ⊕_a R_{mid a}` of the mesh resolution. -/
def tauMap (x : ι) (hx : ¬ D.proj x) :
    Rep F (F (D.tau x hx)) →ₗ[Alg F] (∀ a : D.Mid x, Rep F (F (D.mid x a))) :=
  LinearMap.pi fun a ↦ repMap (D.q x hx a)

theorem tauMap_injective (x : ι) (hx : ¬ D.proj x) : Function.Injective (D.tauMap x hx) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro r hr
  rw [LinearMap.mem_ker] at hr
  rw [Submodule.mem_bot]
  ext y
  exact D.cov_mono x hx y (r y) fun a ↦ by
    have := congrFun (congrFun hr a) y
    simpa [tauMap] using this

theorem range_tauMap (x : ι) (hx : ¬ D.proj x) :
    LinearMap.range (D.tauMap x hx) = LinearMap.ker (D.meshMap x) := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker]
    ext y
    rw [meshMap_apply]
    simp only [tauMap, LinearMap.pi_apply, repMap_apply, Category.assoc]
    rw [← Preadditive.comp_sum, D.comp_zero, Limits.comp_zero]
    rfl
  · intro m hm
    rw [LinearMap.mem_ker] at hm
    choose z hz using fun y ↦ D.cov_exact x hx y (fun a ↦ m a y) (by
      have := congrFun hm y
      rwa [meshMap_apply] at this)
    refine ⟨(z : Rep F (F (D.tau x hx))), ?_⟩
    ext a y
    change z y ≫ D.q x hx a = m a y
    exact (hz y a).symm

theorem meshMap_injective (x : ι) (hx : D.proj x) : Function.Injective (D.meshMap x) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  rw [Submodule.mem_bot]
  ext a y
  exact D.proj_mono x hx y (fun a ↦ m a y) (by
    have := congrFun hm y
    rwa [meshMap_apply] at this) a

theorem meshMap_single (x : ι) (a : D.Mid x) :
    (D.meshMap x).comp (LinearMap.single (Alg F) (fun a ↦ Rep F (F (D.mid x a))) a) =
      repMap (D.p x a) := by
  classical
  ext m y
  simp only [LinearMap.comp_apply]
  rw [meshMap_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

/-- **Second sequence of Proposition 2.6(1), on modules**: maps
`⊕_a R_{mid a} → R_w` killed by the translation map factor uniquely through the
mesh map. -/
theorem contra_factor (x : ι) (hx : ¬ D.proj x) (w : ι)
    (ψ : (∀ a : D.Mid x, Rep F (F (D.mid x a))) →ₗ[Alg F] Rep F (F w))
    (hψ : ψ.comp (D.tauMap x hx) = 0) :
    ∃ φ : Rep F (F x) →ₗ[Alg F] Rep F (F w), φ.comp (D.meshMap x) = ψ := by
  classical
  set ψa : ∀ a, Rep F (F (D.mid x a)) →ₗ[Alg F] Rep F (F w) :=
    fun a ↦ ψ.comp (LinearMap.single (Alg F) (fun a ↦ Rep F (F (D.mid x a))) a)
  set v : ∀ a, F (D.mid x a) ⟶ F w := fun a ↦ ((ψa a) (unit _)) _
  have hv : ∀ a, ψa a = repMap (v a) := fun a ↦ eq_repMap (ψa a)
  have hdec : ∀ m : ∀ a, Rep F (F (D.mid x a)), ψ m = ∑ a, ψa a (m a) := by
    intro m
    conv_lhs => rw [← Finset.univ_sum_single m]
    rw [map_sum]
    rfl
  have hsum : ∑ a, D.q x hx a ≫ v a = 0 := by
    have h0 : ψ (D.tauMap x hx (unit _)) = 0 := by
      have := LinearMap.congr_fun hψ (unit (D.tau x hx))
      rwa [LinearMap.comp_apply, LinearMap.zero_apply] at this
    have h1 := congrArg (fun r : Rep F (F w) ↦ r (D.tau x hx)) h0
    simp only [Rep.zero_apply] at h1
    rw [hdec, Rep.sum_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hv a, repMap_apply]
    simp [tauMap, unit]
  obtain ⟨u, hu⟩ := D.contra_exact x hx w v hsum
  refine ⟨repMap u, LinearMap.pi_ext' fun a ↦ ?_⟩
  rw [LinearMap.comp_assoc, meshMap_single, ← repMap_comp, ← hu a, ← hv a]

theorem contra_unique (x : ι) (hx : ¬ D.proj x) (w : ι) (φ : Rep F (F x) →ₗ[Alg F] Rep F (F w))
    (hφ : φ.comp (D.meshMap x) = 0) : φ = 0 := by
  rw [eq_repMap φ]
  have : ((φ (unit x)) x) = 0 := by
    refine D.contra_mono x hx w _ fun a ↦ repMap_injective (F := F) ?_
    rw [repMap_comp, ← eq_repMap φ, ← meshMap_single, ← LinearMap.comp_assoc, hφ,
      LinearMap.zero_comp, repMap_zero]
  rw [this, repMap_zero]

theorem meshMap_mem_rad (x : ι) (s : ∀ a : D.Mid x, Rep F (F (D.mid x a))) :
    D.meshMap x s ∈ L.radRep x := by
  rw [← D.range_meshMap]; exact LinearMap.mem_range_self _ s

/-- **`Hom(L_x, R_w) = 0`** at a nonprojective `x`. -/
theorem hom_top_eq_zero (x : ι) (hx : ¬ D.proj x) (w : ι) (θ : L.Top x →ₗ[Alg F] Rep F (F w)) :
    θ = 0 := by
  have h := D.contra_unique x hx w (θ.comp (L.radRep x).mkQ) (LinearMap.ext fun s ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (D.meshMap_mem_rad x s), map_zero,
      LinearMap.zero_apply])
  apply Submodule.linearMap_qext
  rw [h, LinearMap.zero_comp]

/-- **`Ext¹(L_x, R_w) = 0`** at a nonprojective `x`, in extension form: a map
into `R_w` from a submodule with quotient `L_x` extends. -/
theorem extend_top (x : ι) (hx : ¬ D.proj x) (w : ι) {M : Type*} [AddCommGroup M]
    [Module (Alg F) M] (U : Submodule (Alg F) M) (e : (M ⧸ U) ≃ₗ[Alg F] L.Top x)
    (g : U →ₗ[Alg F] Rep F (F w)) :
    ∃ f : M →ₗ[Alg F] Rep F (F w), f.comp U.subtype = g := by
  set π : M →ₗ[Alg F] L.Top x := e.toLinearMap.comp U.mkQ
  have hπU : ∀ m, π m = 0 ↔ m ∈ U := by
    intro m
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hπsurj : Function.Surjective π := e.surjective.comp (Submodule.mkQ_surjective U)
  obtain ⟨m₀, hm₀⟩ := hπsurj ((L.radRep x).mkQ (unit x))
  set h : Rep F (F x) →ₗ[Alg F] M := ofElem x (idem (F := F) x • m₀)
  have hiu : idem (F := F) x • unit x = unit x := colAlg_smul_unit x (unit x)
  have hπh : π.comp h = (L.radRep x).mkQ := by
    refine hom_ext ?_
    rw [LinearMap.comp_apply, ofElem_unit, smul_smul, idem_mul_idem, map_smul, hm₀, ← map_smul,
      hiu]
  have hhU : ∀ r ∈ L.radRep x, h r ∈ U := by
    intro r hr
    rw [← hπU, ← LinearMap.comp_apply, hπh, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hr
  set ψ : (∀ a : D.Mid x, Rep F (F (D.mid x a))) →ₗ[Alg F] Rep F (F w) :=
    g.comp (LinearMap.codRestrict U (h.comp (D.meshMap x)) fun s ↦ hhU _ (D.meshMap_mem_rad x s))
  have hψ : ψ.comp (D.tauMap x hx) = 0 := by
    ext r : 1
    simp only [ψ, LinearMap.comp_apply, LinearMap.zero_apply]
    have : D.meshMap x (D.tauMap x hx r) = 0 := by
      have := D.range_tauMap x hx ▸ LinearMap.mem_range_self (D.tauMap x hx) r
      exact this
    have h0 : (LinearMap.codRestrict U (h.comp (D.meshMap x)) fun s ↦ hhU _
        (D.meshMap_mem_rad x s)) (D.tauMap x hx r) = 0 := by
      apply Subtype.ext
      simp [this]
    rw [h0, map_zero]
  obtain ⟨φ, hφ⟩ := D.contra_factor x hx w ψ hψ
  -- glue `g` on `U` and `φ` on `R_x`
  set Φ : (U × Rep F (F x)) →ₗ[Alg F] M := U.subtype.coprod h
  set Ψ : (U × Rep F (F x)) →ₗ[Alg F] Rep F (F w) := g.coprod φ
  have hΦ : Function.Surjective Φ := by
    intro m
    obtain ⟨r, hr⟩ := Submodule.mkQ_surjective (L.radRep x) (π m)
    have hmem : m - h r ∈ U := by
      rw [← hπU, map_sub, ← LinearMap.comp_apply π h, hπh, hr, sub_self]
    exact ⟨(⟨_, hmem⟩, r), by simp [Φ]⟩
  have hker : LinearMap.ker Φ ≤ LinearMap.ker Ψ := by
    rintro ⟨u, r⟩ hur
    rw [LinearMap.mem_ker] at hur ⊢
    simp only [Φ, LinearMap.coprod_apply, Submodule.subtype_apply] at hur
    simp only [Ψ, LinearMap.coprod_apply]
    have hhr : h r = -(u : M) := eq_neg_of_add_eq_zero_right hur
    have hr : r ∈ L.radRep x := by
      have := congrArg π hhr
      rw [← LinearMap.comp_apply π h, hπh, Submodule.mkQ_apply, map_neg,
        (hπU _).2 u.2, neg_zero, Submodule.Quotient.mk_eq_zero] at this
      exact this
    obtain ⟨s, rfl⟩ : r ∈ LinearMap.range (D.meshMap x) := by rwa [D.range_meshMap]
    have h1 : φ (D.meshMap x s) = ψ s := LinearMap.congr_fun hφ s
    rw [h1]
    simp only [ψ, LinearMap.comp_apply]
    have h2 : (LinearMap.codRestrict U (h.comp (D.meshMap x)) fun s ↦ hhU _
        (D.meshMap_mem_rad x s)) s = -u := by
      apply Subtype.ext
      simp [hhr]
    rw [h2, map_neg, add_neg_cancel]
  refine ⟨((LinearMap.ker Φ).liftQ Ψ hker).comp
    (Φ.quotKerEquivOfSurjective hΦ).symm.toLinearMap, ?_⟩
  ext u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
  have : (Φ.quotKerEquivOfSurjective hΦ).symm (u : M) = Submodule.Quotient.mk (u, 0) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [Φ]
  rw [this, Submodule.liftQ_apply]
  simp [Ψ]

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
