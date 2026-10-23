module

public import MultiplicativeBasisDeformations.Foundations.GradedRealizationIso
public import MultiplicativeBasisDeformations.Foundations.LayerExactnessDual

/-!
# The mesh sequences of `k(Γ_A)` on homogeneous paths

Proposition 2.6(1)(2) transported to `k(Γ_A) = C(Γ_A, c)` through the
realization of Proposition 2.6(3) (`graded-category.tex`). For a
homogeneous family of morphisms of `kQ` the statements read, modulo the mesh
ideal:

* (`cov_homog`) if `∑_a G_a a` lies in the mesh ideal, then at a projective
  vertex every `G_a` does, and at a nonprojective vertex `y` there is `H` with
  `G_a ≡ c_{y,a} H (σa)` for every arrow `a` ending at `y` (the manuscript's
  "comes from `h ∈ C_{n-2}(W, τY)`", as in the injectivity step of (3));
* (`cov_mono_homog`) if every `H (σa)` lies in the mesh ideal, so does `H`;
* (`contra_homog`) if `∑_a c_{y,a} (σa) V_a` lies in the mesh ideal, then
  `V_a ≡ a U` for one `U`;
* (`contra_mono_homog`) if every `a U` lies in the mesh ideal, so does `U`.

The first two use the first sequence of (1), the last two the second
sequence (`LayerExactnessDual.lean`).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- Every arrow ending at `Y` is the arrow of a summand of the middle term. -/
theorem exists_occ {Y : S.ARVertex} (a : Σ X : S.ARVertex, X ⟶ Y) :
    ∃ i, a = ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ := by
  obtain ⟨i, rfl⟩ := (S.occEquiv Y).surjective a
  exact ⟨i, rfl⟩

/-- A homogeneous element of the mesh ideal is realized one radical degree
higher. -/
theorem realize_mem_of_mem_ideal {d : ℕ} {x y : S.ARVertex}
    {g : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hd : g ∈ LinearPaths.degreePart (k := k) d x y) (hg : g ∈ (S.meshIdeal b).hom _ _) :
    S.realize b x y g ∈ S.radPow (d + 1) _ _ := by
  have := S.realize_proj_mem_of_mem_ideal b d hg
  rwa [LinearPaths.proj_of_mem hd, if_pos rfl] at this

set_option maxHeartbeats 800000 in
/-- **Proposition 2.6(1)(2)** for `k(Γ_A)`, covariant form on homogeneous
families. -/
theorem cov_homog (d : ℕ) {W Y : S.ARVertex}
    (G : ∀ a : Σ X : S.ARVertex, X ⟶ Y, LinearPaths.obj (k := k) W ⟶ LinearPaths.obj a.1)
    (hG : ∀ a, G a ∈ LinearPaths.degreePart (k := k) d W a.1)
    (hsum : ∑ a, G a ≫ LinearPaths.arrow a.2 ∈ (S.meshIdeal b).hom _ _) :
    (Y ∉ S.nonprojectiveVertices → ∀ a, G a ∈ (S.meshIdeal b).hom _ _) ∧
    ∀ hY : Y ∈ S.nonprojectiveVertices,
      ∃ H : LinearPaths.obj (k := k) W ⟶ LinearPaths.obj (S.arTranslationQuiver.tau ⟨Y, hY⟩).1,
        ∀ a, G a - ((S.arCoefficients b ⟨Y, hY⟩ a.1 a.2 : kˣ) : k) •
          (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate ⟨Y, hY⟩ a.1 a.2)) ∈
          (S.meshIdeal b).hom _ _ := by
  have hdeg : ∑ a, G a ≫ LinearPaths.arrow a.2 ∈ LinearPaths.degreePart (k := k) (d + 1) W Y :=
    Submodule.sum_mem _ fun a _ ↦ LinearPaths.comp_arrow_mem_degreePart (hG a) _
  have hreal := S.realize_mem_of_mem_ideal b hdeg hsum
  have hsumInd := S.sum_inv_v_betaI_mem b G hG hreal
  let w : ∀ i, S.fg (S.index W) ⟶ S.fg (S.midLabel (S.index Y) i) := fun i ↦
    S.toFG.map ((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩))
  have hw : ∀ i, w i ∈ (StrictLayers.Ipow d : HomIdeal (ModCat A)).hom _ _ := by
    intro i
    have h0 := S.realize_mem b (hG ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)
    exact (S.mem_radPow_iff d _).1 (Submodule.smul_mem _ _ h0)
  have hsum' : ∑ i, w i ≫ S.beta (S.index Y) i ∈
      (StrictLayers.Ipow (d + 2) : HomIdeal (ModCat A)).hom _ _ := by
    have e : ∀ i, w i ≫ S.beta (S.index Y) i = S.toFG.map
        (((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)) ≫ S.betaI Y i) := by
      intro i
      rw [Functor.map_comp]
      congr 1
      exact (S.map_homEquivFG_symm _).symm
    rw [Finset.sum_congr rfl (fun i _ ↦ e i), ← Functor.map_sum]
    exact (S.mem_radPow_iff (d + 2) _).1 hsumInd
  have hstep : ∀ i, w i ∈ (StrictLayers.Ipow (d + 1) : HomIdeal (ModCat A)).hom _ _ →
      G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ ∈ (S.meshIdeal b).hom _ _ := by
    intro i hi
    apply S.mem_meshIdeal_of_realize_mem b d (hG _)
    have h1 := (S.mem_radPow_iff (d + 1) _).2 hi
    have := Submodule.smul_mem _ (S.vCoeff b Y i) h1
    rwa [smul_smul, mul_inv_cancel₀ (S.vCoeff_ne_zero b Y i), one_smul] at this
  -- every summand in the ideal: enough for both conclusions
  have hall : (∀ i, w i ∈ (StrictLayers.Ipow (d + 1) : HomIdeal (ModCat A)).hom _ _) →
      (Y ∉ S.nonprojectiveVertices → ∀ a, G a ∈ (S.meshIdeal b).hom _ _) ∧
      ∀ hY : Y ∈ S.nonprojectiveVertices,
        ∃ H : LinearPaths.obj (k := k) W ⟶ LinearPaths.obj (S.arTranslationQuiver.tau ⟨Y, hY⟩).1,
          ∀ a, G a - ((S.arCoefficients b ⟨Y, hY⟩ a.1 a.2 : kˣ) : k) •
            (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate ⟨Y, hY⟩ a.1 a.2)) ∈
            (S.meshIdeal b).hom _ _ := by
    intro hwi
    have hG0 : ∀ a, G a ∈ (S.meshIdeal b).hom _ _ := by
      intro a
      obtain ⟨i, rfl⟩ := S.exists_occ a
      exact hstep i (hwi i)
    exact ⟨fun _ ↦ hG0, fun hY ↦ ⟨0, fun a ↦ by simpa using hG0 a⟩⟩
  cases d with
  | zero => exact hall fun i ↦ S.layer_exact_zero (S.index Y) w hsum' i
  | succ m =>
      obtain ⟨z, hz, hwz⟩ := S.layer_exact (S.index Y) w hw hsum'
      by_cases hY : Y ∈ S.nonprojectiveVertices
      · refine ⟨fun h ↦ absurd hY h, fun hY' ↦ ?_⟩
        let y : S.nonprojectiveVertices := ⟨Y, hY⟩
        let h : S.fg (S.index W) ⟶ S.fg (S.index (S.arTranslationQuiver.tau y).1) :=
          z ≫ (S.tau.tauPlusIso (S.vendorNonprojective y)).hom
        have hh : h ∈ (StrictLayers.Ipow m : HomIdeal (ModCat A)).hom _ _ :=
          (StrictLayers.Ipow m : HomIdeal (ModCat A)).postcomp _ hz
        let hInd : S.label W ⟶ S.label (S.arTranslationQuiver.tau y).1 :=
          (S.homEquivFG (S.ind (S.index W)) (S.ind (S.index (S.arTranslationQuiver.tau y).1))).symm h
        have hIndMap : S.toFG.map hInd = h := S.map_homEquivFG_symm _
        have hIndMem : hInd ∈ S.radPow m _ _ := by
          rw [S.mem_radPow_iff, hIndMap]; exact hh
        obtain ⟨H, hH, hHdiff⟩ := S.exists_realize_sub_mem b m hInd hIndMem
        refine ⟨H, fun a ↦ ?_⟩
        obtain ⟨i, rfl⟩ := S.exists_occ a
        apply S.mem_meshIdeal_of_realize_mem b (m + 1)
        · refine sub_mem (hG _) (Submodule.smul_mem _ _ ?_)
          exact LinearPaths.comp_arrow_mem_degreePart hH _
        · apply S.realize_corrected_mem b y i _ H hH hInd hHdiff
          have e : S.toFG.map ((S.vCoeff b y.1 i)⁻¹ •
              S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩) -
                hInd ≫ S.alphaI y i) =
              w i - z ≫ (S.rightMesh (S.index Y)).f ≫ S.midProj (S.index Y) i := by
            rw [Functor.map_sub, Functor.map_comp, hIndMap, S.alphaI_map]
            simp only [h, Category.assoc, Iso.hom_inv_id_assoc]
            rfl
          rw [S.mem_radPow_iff, e]
          exact hwz i
      · have hz0 : z = 0 := (S.isZero_rightMesh_X₁_of_not_mem Y hY).eq_of_tgt _ _
        exact hall fun i ↦ by simpa [hz0] using hwz i

/-- **Proposition 2.6(1)** for `k(Γ_A)`: the first map of a mesh is injective
on homogeneous families. -/
theorem cov_mono_homog (m : ℕ) {W : S.ARVertex} (y : S.nonprojectiveVertices)
    (H : LinearPaths.obj (k := k) W ⟶ LinearPaths.obj (S.arTranslationQuiver.tau y).1)
    (hH : H ∈ LinearPaths.degreePart (k := k) m W _)
    (h : ∀ a : Σ X : S.ARVertex, X ⟶ y.1,
      H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate y a.1 a.2) ∈ (S.meshIdeal b).hom _ _) :
    H ∈ (S.meshIdeal b).hom _ _ := by
  apply S.mem_meshIdeal_of_realize_mem b m hH
  -- `realize H ≫ α_i ∈ J^{m+2}` for every summand
  have hα : ∀ i, S.realize b _ _ H ≫ S.alphaI y i ∈ S.radPow (m + 2) _ _ := by
    intro i
    have h1 := S.realize_mem_of_mem_ideal b
      (LinearPaths.comp_arrow_mem_degreePart hH _) (h ⟨_, S.occArrow y.1 i⟩)
    rw [S.realize_comp, realize_arrow] at h1
    have e : S.realize b _ _ H ≫ S.alphaI y i =
        S.realize b _ _ H ≫ (S.alphaI y i -
          S.uCoeff b y i • S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i))) +
        S.uCoeff b y i • (S.realize b _ _ H ≫
          S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i))) := by
      rw [Preadditive.comp_sub, Linear.comp_smul, sub_add_cancel]
    rw [e]
    exact add_mem (S.comp_mem_radPow (S.realize_mem b hH) (S.alphaI_sub_mem b y i))
      (Submodule.smul_mem _ _ h1)
  let z : S.fg (S.index W) ⟶ (S.rightMesh (S.index y.1)).X₁ :=
    S.toFG.map (S.realize b _ _ H) ≫ (S.tau.tauPlusIso (S.vendorNonprojective y)).inv
  have hz : z ∈ (StrictLayers.Ipow (m + 1) : HomIdeal (ModCat A)).hom _ _ := by
    apply S.layer_injective (S.index y.1) z
    intro i
    have := (S.mem_radPow_iff (m + 2) _).1 (hα i)
    rw [Functor.map_comp, S.alphaI_map] at this
    simp only [z, Category.assoc]
    exact this
  rw [S.mem_radPow_iff]
  have := (StrictLayers.Ipow (m + 1) : HomIdeal (ModCat A)).postcomp
    (S.tau.tauPlusIso (S.vendorNonprojective y)).hom hz
  simp only [z, Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
  exact this

/-- **Proposition 2.6(1)** for `k(Γ_A)`, second sequence: precomposition with
the arrows into a nonprojective vertex is injective on homogeneous
morphisms. -/
theorem contra_mono_homog (m : ℕ) {W : S.ARVertex} (y : S.nonprojectiveVertices)
    (U : LinearPaths.obj (k := k) y.1 ⟶ LinearPaths.obj W)
    (hU : U ∈ LinearPaths.degreePart (k := k) m _ W)
    (h : ∀ a : Σ X : S.ARVertex, X ⟶ y.1, LinearPaths.arrow a.2 ≫ U ∈ (S.meshIdeal b).hom _ _) :
    U ∈ (S.meshIdeal b).hom _ _ := by
  apply S.mem_meshIdeal_of_realize_mem b m hU
  have hβ : ∀ i, S.betaI y.1 i ≫ S.realize b _ _ U ∈ S.radPow (m + 2) _ _ := by
    intro i
    have hd : LinearPaths.arrow (k := k) (S.occArrow y.1 i) ≫ U ∈
        LinearPaths.degreePart (k := k) (m + 1) _ W := by
      have := LinearPaths.comp_mem_degreePart (LinearPaths.arrow_mem_degreePart (k := k)
        (S.occArrow y.1 i)) hU
      rwa [add_comm] at this
    have h1 := S.realize_mem_of_mem_ideal b hd (h ⟨_, S.occArrow y.1 i⟩)
    rw [S.realize_comp, realize_arrow] at h1
    have e : S.betaI y.1 i ≫ S.realize b _ _ U =
        (S.betaI y.1 i - S.vCoeff b y.1 i • S.rep b (S.occArrow y.1 i)) ≫ S.realize b _ _ U +
        S.vCoeff b y.1 i • (S.rep b (S.occArrow y.1 i) ≫ S.realize b _ _ U) := by
      rw [Preadditive.sub_comp, Linear.smul_comp, sub_add_cancel]
    rw [e]
    refine add_mem ?_ (Submodule.smul_mem _ _ h1)
    simpa [add_comm] using S.comp_mem_radPow (S.betaI_sub_mem b y.1 i) (S.realize_mem b hU)
  rw [S.mem_radPow_iff]
  apply S.colayer_injective y
  intro i
  have := (S.mem_radPow_iff (m + 2) _).1 (hβ i)
  rw [Functor.map_comp, betaI, map_homEquivFG_symm] at this
  exact this

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem mem_of_smul_mem {n : ℕ} {X Y : S.Ind} {f : X ⟶ Y} {v : k} (hv : v ≠ 0)
    (h : v • f ∈ S.radPow n X Y) : f ∈ S.radPow n X Y := by
  have := Submodule.smul_mem _ v⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hv, one_smul] at this

set_option maxHeartbeats 800000 in
/-- **Proposition 2.6(1)** for `k(Γ_A)`, second sequence, exactness on
homogeneous families: if `∑_a c_{y,a} (σa) V_a` lies in the mesh ideal, then
`V_a ≡ a U` for one `U`. -/
theorem contra_homog (d : ℕ) {W : S.ARVertex} (y : S.nonprojectiveVertices)
    (V : ∀ a : Σ X : S.ARVertex, X ⟶ y.1, LinearPaths.obj (k := k) a.1 ⟶ LinearPaths.obj W)
    (hV : ∀ a, V a ∈ LinearPaths.degreePart (k := k) d a.1 W)
    (hsum : ∑ a, ((S.arCoefficients b y a.1 a.2 : kˣ) : k) •
      (LinearPaths.arrow (S.arTranslationQuiver.mate y a.1 a.2) ≫ V a) ∈ (S.meshIdeal b).hom _ _) :
    ∃ U : LinearPaths.obj (k := k) y.1 ⟶ LinearPaths.obj W,
      ∀ a, V a - LinearPaths.arrow a.2 ≫ U ∈ (S.meshIdeal b).hom _ _ := by
  have hdeg : ∑ a, ((S.arCoefficients b y a.1 a.2 : kˣ) : k) •
      (LinearPaths.arrow (S.arTranslationQuiver.mate y a.1 a.2) ≫ V a) ∈
        LinearPaths.degreePart (k := k) (d + 1) _ W := by
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ ?_
    have := LinearPaths.comp_mem_degreePart (LinearPaths.arrow_mem_degreePart (k := k)
      (S.arTranslationQuiver.mate y a.1 a.2)) (hV a)
    rwa [add_comm] at this
  have hreal := S.realize_mem_of_mem_ideal b hdeg hsum
  let R : ∀ i, S.label (S.vertex (S.midLabel (S.index y.1) i)) ⟶ S.label W := fun i ↦
    S.realize b _ _ (V ⟨S.vertex (S.midLabel (S.index y.1) i), S.occArrow y.1 i⟩)
  have hR : ∀ i, R i ∈ S.radPow d _ _ := fun i ↦
    S.realize_mem b (hV ⟨S.vertex (S.midLabel (S.index y.1) i), S.occArrow y.1 i⟩)
  have hreal' : ∑ i, ((S.arCoefficients b y _ (S.occArrow y.1 i) : kˣ) : k) •
      (S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)) ≫ R i) ∈
        S.radPow (d + 2) _ _ := by
    have e : S.realize b _ _ (∑ a, ((S.arCoefficients b y a.1 a.2 : kˣ) : k) •
        (LinearPaths.arrow (S.arTranslationQuiver.mate y a.1 a.2) ≫ V a)) =
        ∑ i, ((S.arCoefficients b y _ (S.occArrow y.1 i) : kˣ) : k) •
          (S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)) ≫ R i) := by
      rw [map_sum, S.sum_lastArrow_eq (W := W)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, S.realize_comp, realize_arrow]
    rw [← e]
    exact hreal
  -- the family `v'_i = v_i R_i` in `mod A`
  let v' : ∀ i, S.fg (S.midLabel (S.index y.1) i) ⟶ S.fg (S.index W) := fun i ↦
    S.toFG.map (S.vCoeff b y.1 i • R i)
  have hv' : ∀ i, v' i ∈ (StrictLayers.Ipow d : HomIdeal (ModCat A)).hom _ _ := fun i ↦
    (S.mem_radPow_iff d _).1 (Submodule.smul_mem _ _ (hR i))
  have hT : ∑ i, S.alphaI y i ≫ (S.vCoeff b y.1 i • R i) ∈ S.radPow (d + 2) _ _ := by
    have e : ∑ i, S.alphaI y i ≫ (S.vCoeff b y.1 i • R i) =
        ∑ i, (S.alphaI y i - S.uCoeff b y i •
            S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i))) ≫
          (S.vCoeff b y.1 i • R i) +
        ∑ i, ((S.arCoefficients b y _ (S.occArrow y.1 i) : kˣ) : k) •
          (S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)) ≫ R i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [S.arCoefficients_occArrow]
      have e1 : (S.uCoeff b y i • S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i))) ≫
          (S.vCoeff b y.1 i • R i) = (S.uCoeff b y i * S.vCoeff b y.1 i) •
            (S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)) ≫ R i) := by
        rw [Linear.smul_comp, Linear.comp_smul, smul_smul]
      rw [Preadditive.sub_comp, e1, sub_add_cancel]
    rw [e]
    refine add_mem (Submodule.sum_mem _ fun i _ ↦ ?_) hreal'
    have := S.comp_mem_radPow (S.alphaI_sub_mem b y i) (Submodule.smul_mem _ (S.vCoeff b y.1 i) (hR i))
    rwa [add_comm] at this
  have hsumα : ∑ i, ((S.rightMesh (S.index y.1)).f ≫ S.midProj (S.index y.1) i) ≫ v' i ∈
      (StrictLayers.Ipow (d + 2) : HomIdeal (ModCat A)).hom _ _ := by
    have h1 := (S.mem_radPow_iff (d + 2) _).1 hT
    rw [Functor.map_sum] at h1
    have h2 := (StrictLayers.Ipow (d + 2) : HomIdeal (ModCat A)).precomp
      (S.tau.tauPlusIso (S.vendorNonprojective y)).hom h1
    have e : (S.tau.tauPlusIso (S.vendorNonprojective y)).hom ≫
        ∑ i, S.toFG.map (S.alphaI y i ≫ (S.vCoeff b y.1 i • R i)) =
        ∑ i, ((S.rightMesh (S.index y.1)).f ≫ S.midProj (S.index y.1) i) ≫ v' i := by
      rw [Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Functor.map_comp, S.alphaI_map]
      simp only [v', Category.assoc, Iso.hom_inv_id_assoc]
    rw [e] at h2
    exact h2
  cases d with
  | zero =>
      refine ⟨0, fun a ↦ ?_⟩
      obtain ⟨i, rfl⟩ := S.exists_occ a
      rw [Limits.comp_zero, sub_zero]
      apply S.mem_meshIdeal_of_realize_mem b 0 (hV _)
      have := S.colayer_exact_zero y v' hsumα i
      exact S.mem_of_smul_mem (S.vCoeff_ne_zero b y.1 i) ((S.mem_radPow_iff 1 _).2 this)
  | succ n =>
      obtain ⟨u, hu, huv⟩ := S.colayer_exact y v' hv' hsumα
      let uInd : S.label y.1 ⟶ S.label W := (S.homEquivFG (S.label y.1) (S.label W)).symm u
      have huMap : S.toFG.map uInd = u := S.map_homEquivFG_symm _
      have huMem : uInd ∈ S.radPow n _ _ := by rw [S.mem_radPow_iff, huMap]; exact hu
      obtain ⟨U, hU, hUdiff⟩ := S.exists_realize_sub_mem b n uInd huMem
      refine ⟨U, fun a ↦ ?_⟩
      obtain ⟨i, rfl⟩ := S.exists_occ a
      have hAU : LinearPaths.arrow (k := k) (S.occArrow y.1 i) ≫ U ∈
          LinearPaths.degreePart (k := k) (n + 1) _ W := by
        have := LinearPaths.comp_mem_degreePart (LinearPaths.arrow_mem_degreePart (k := k)
          (S.occArrow y.1 i)) hU
        rwa [add_comm] at this
      apply S.mem_meshIdeal_of_realize_mem b (n + 1) (sub_mem (hV _) hAU)
      rw [map_sub, S.realize_comp, realize_arrow]
      apply S.mem_of_smul_mem (S.vCoeff_ne_zero b y.1 i)
      set v := S.vCoeff b y.1 i
      have e : v • (R i - S.rep b (S.occArrow y.1 i) ≫ S.realize b _ _ U) =
          (v • R i - S.betaI y.1 i ≫ uInd) +
            (S.betaI y.1 i - v • S.rep b (S.occArrow y.1 i)) ≫ uInd +
            v • (S.rep b (S.occArrow y.1 i) ≫ (uInd - S.realize b _ _ U)) := by
        rw [smul_sub, Preadditive.sub_comp, Linear.smul_comp, Preadditive.comp_sub, smul_sub]
        abel
      rw [e]
      refine add_mem (add_mem ?_ ?_) (Submodule.smul_mem _ _ ?_)
      · rw [S.mem_radPow_iff, Functor.map_sub, Functor.map_comp, huMap, betaI,
          map_homEquivFG_symm]
        exact huv i
      · have := S.comp_mem_radPow (S.betaI_sub_mem b y.1 i) huMem
        rwa [add_comm] at this
      · have := S.comp_mem_radPow (S.rep_mem b (S.occArrow y.1 i)) hUdiff
        rwa [show 1 + (n + 1) = n + 1 + 1 by omega] at this

end MultiplicativeBasisDeformations.IndSkeleton
