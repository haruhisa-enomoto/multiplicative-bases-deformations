import MultiplicativeBasisDeformations.Foundations.LiftedEvaluation
import MultiplicativeBasisDeformations.Foundations.WeightTwist
import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd

/-!
# The modules `V_X̃` over finite subcategories of `L`

Lemma 4.8 and the first step of Lemma 4.13 (`scalar-normalization.tex:
327–390, 566–583`). `L` is the graded covering category on the lifted
projective vertices (`grading0`). For a lifted object `X̃ = (X, h)` and a finite
set `T` of lifted projective vertices, `V_X̃` restricted to `T` is a module over
the covering algebra `cov T` (`VM`): its value at `z = (p, g)` is the degree
`g⁻¹h` part of `C(P_p, X)`, and `L` acts by composition. When `T` contains the
support of `V_X̃` it is finite-dimensional and indecomposable: "Height gives
`End(V_X̃) = k`, so the modules are indecomposable" (`VM_isFiniteIndecomposable`,
via Lemma 4.8).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G] [DecidableEq G]

/-! ### Restricting a grading to a subfamily -/

namespace HomGrading

/-- The restriction of a grading to a subfamily. -/
def comp (Dg : HomGrading (k := k) F G) {κ : Type} [Fintype κ] [DecidableEq κ] (σ : κ → ι) :
    HomGrading (k := k) (F ∘ σ) G where
  proj g x y := Dg.proj g (σ x) (σ y)
  proj_proj g h x y f := Dg.proj_proj g h _ _ f
  sum x y f := Dg.sum _ _ f
  proj_comp g a b x y z f f' := Dg.proj_comp g a b _ _ _ f f'
  proj_id g x := Dg.proj_id g (σ x)

end HomGrading

/-- The restriction of height data to a subfamily with distinct labels. -/
def HeightData.comp {Dg : HomGrading (k := k) F G} (H : HeightData Dg) {κ : Type} [Fintype κ]
    [DecidableEq κ] (σ : κ → ι) (hσ : Function.Injective σ) : HeightData (Dg.comp σ) where
  hgt := H.hgt
  hgt_mul := H.hgt_mul
  nonneg g x y f hf hf0 := H.nonneg g _ _ f hf hf0
  scalar g x y f hf hf0 hg := by
    obtain ⟨h, h1, c, hc⟩ := H.scalar g _ _ f hf hf0 hg
    have := hσ h
    subst this
    exact ⟨rfl, h1, c, by simpa using hc⟩

namespace MeshData

variable {L : LocalFamily (k := k) F} (D : MeshData F L) (Dg : HomGrading (k := k) F G)

/-- **The grading of `L`**: the deck grading on the projective labels. -/
abbrev grading0 : HomGrading (k := k) D.F0 G := Dg.comp Subtype.val

variable (T : Finset (D.PV × G)) (X : ι × G)

/-- The finite set `T` as objects of `L`. -/
abbrev sT : T → D.PV × G := fun q ↦ q.1

/-- The covering algebra of `T`. -/
abbrev covT := cov (grading0 D Dg) (sT D T)

/-- **`V_X̃` on `T`**: at `z = (p, g)` the degree `g⁻¹h` part of `C(P_p, X)`. -/
abbrev VX : Type u := ∀ q : T, Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1

/-- Elements of the covering algebra as matrices. -/
def ρ : (covT D Dg T)ᵐᵒᵖ →+* Alg (D.F0 ∘ lab (sT D T)) where
  toFun b := ((b.unop : covT D Dg T) : (Alg (D.F0 ∘ lab (sT D T)))ᵐᵒᵖ).unop
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {D Dg T X}

theorem ρ_mem (b : (covT D Dg T)ᵐᵒᵖ) (p q : T) :
    Dg.IsHom ((p.1.2)⁻¹ * q.1.2) (ρ D Dg T b p q) := b.unop.2 p q

/-- The underlying morphisms. -/
def ιV : VX D Dg T X →+ Rep (D.F0 ∘ lab (sT D T)) (F X.1) where
  toFun m q := (m q).1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ιV_injective : Function.Injective (ιV (D := D) (Dg := Dg) (T := T) (X := X)) :=
  fun m n h ↦ funext fun q ↦ Subtype.ext (congrFun h q)

theorem smul_mem (b : (covT D Dg T)ᵐᵒᵖ) (m : VX D Dg T X) (p : T) :
    (ρ D Dg T b • ιV m) p ∈ Dg.part ((p.1.2)⁻¹ * X.2) p.1.1.1 X.1 := by
  rw [Rep.smul_apply, HomGrading.mem_part_iff]
  refine Dg.isHom_sum _ fun q _ ↦ ?_
  have := Dg.isHom_comp (ρ_mem b p q) ((HomGrading.mem_part_iff (D := Dg)).1 (m q).2)
  rwa [show (p.1.2)⁻¹ * q.1.2 * ((q.1.2)⁻¹ * X.2) = (p.1.2)⁻¹ * X.2 by group] at this

instance : SMul (covT D Dg T)ᵐᵒᵖ (VX D Dg T X) :=
  ⟨fun b m p ↦ ⟨(ρ D Dg T b • ιV m) p, smul_mem b m p⟩⟩

theorem ιV_smul (b : (covT D Dg T)ᵐᵒᵖ) (m : VX D Dg T X) : ιV (b • m) = ρ D Dg T b • ιV m := rfl

instance : Module (covT D Dg T)ᵐᵒᵖ (VX D Dg T X) :=
  letI : Module (covT D Dg T)ᵐᵒᵖ (Rep (D.F0 ∘ lab (sT D T)) (F X.1)) :=
    Module.compHom _ (ρ D Dg T)
  Function.Injective.module _ ιV ιV_injective ιV_smul

variable (D Dg T X) in
/-- **The module `V_X̃|_T` over the covering algebra.** -/
def VM : RightModuleCat (covT D Dg T) := ModuleCat.of _ (VX D Dg T X)

theorem algebraMap_smul_VX (c : k) (m : VX D Dg T X) :
    (algebraMap k (covT D Dg T)ᵐᵒᵖ c) • m = c • m := by
  apply ιV_injective
  rw [ιV_smul]
  have : ρ D Dg T (algebraMap k (covT D Dg T)ᵐᵒᵖ c) =
      algebraMap k (Alg (D.F0 ∘ lab (sT D T))) c := rfl
  rw [this, algebraMap_smul]
  rfl

/-- The identity from the native `k`-structure. -/
def VMK : VX D Dg T X →ₗ[k] VM D Dg T X where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := (algebraMap_smul_VX c m).symm

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

instance VM_finite : Module.Finite k (VM D Dg T X) :=
  Module.Finite.of_surjective VMK fun m ↦ ⟨m, rfl⟩

/-! ### Matrix units and components -/

variable (T) in
/-- The matrix unit of a morphism `u : q' → q` of `L` between objects of `T`. -/
def unitE (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1) (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u) :
    covT D Dg T :=
  ⟨MulOpposite.op (fun p r ↦ idTo (F := D.F0 ∘ lab (sT D T)) p q' ≫ u ≫
      idTo (F := D.F0 ∘ lab (sT D T)) q r), fun p r ↦ by
    change Dg.IsHom _ (idTo (F := D.F0 ∘ lab (sT D T)) p q' ≫ u ≫
      idTo (F := D.F0 ∘ lab (sT D T)) q r)
    by_cases hp : p = q'
    · subst hp
      by_cases hr : r = q
      · subst hr
        have e : idTo (F := D.F0 ∘ lab (sT D T)) p p ≫ u ≫
            idTo (F := D.F0 ∘ lab (sT D T)) r r = u := by
          rw [idTo_self, idTo_self]; exact (Category.id_comp _).trans (Category.comp_id _)
        rw [e]; exact hu
      · rw [idTo_ne (Ne.symm hr), Limits.comp_zero, Limits.comp_zero]; exact Dg.isHom_zero _
    · rw [idTo_ne hp, Limits.zero_comp]; exact Dg.isHom_zero _⟩

theorem ρ_unitE (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1)
    (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u) (p r : T) :
    ρ D Dg T (MulOpposite.op (unitE T q' q u hu)) p r =
      idTo (F := D.F0 ∘ lab (sT D T)) p q' ≫ u ≫ idTo (F := D.F0 ∘ lab (sT D T)) q r :=
  rfl

theorem VX_sum_apply {κ : Type} (s : Finset κ) (g : κ → VX D Dg T X) (p : T) :
    (∑ i ∈ s, g i) p = ∑ i ∈ s, g i p :=
  Finset.sum_apply p s g

/-- A component concentrated at one object of `T`. -/
def singleV (q : T) : Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1 →ₗ[k] VX D Dg T X :=
  LinearMap.single k (fun q : T ↦ Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) q

theorem singleV_same (q : T) (m : Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) : (singleV (D := D) (Dg := Dg) (X := X) q m : VX D Dg T X) q = m :=
  Pi.single_eq_same (M := fun q : T ↦ Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) q m

theorem singleV_ne {q p : T} (h : p ≠ q) (m : Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) :
    (singleV (D := D) (Dg := Dg) (X := X) q m : VX D Dg T X) p = 0 :=
  Pi.single_eq_of_ne (M := fun q : T ↦ Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) h m

theorem unitE_smul_apply (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1)
    (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u) (y : VX D Dg T X) (p : T) :
    ((MulOpposite.op (unitE T q' q u hu) • y : VX D Dg T X) p).1 =
      idTo (F := D.F0 ∘ lab (sT D T)) p q' ≫ u ≫ (y q).1 := by
  change (ρ D Dg T _ • ιV y) p = _
  rw [Rep.smul_apply]
  simp_rw [ρ_unitE, Category.assoc]
  rw [← Preadditive.comp_sum, ← Preadditive.comp_sum]
  congr 2
  exact sum_idTo_comp (F := D.F0 ∘ lab (sT D T)) q (ιV y)

theorem unitE_smul_single (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1)
    (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u)
    (m : Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1)
    (hum : u ≫ m.1 ∈ Dg.part ((q'.1.2)⁻¹ * X.2) q'.1.1.1 X.1) :
    MulOpposite.op (unitE T q' q u hu) • singleV q m = singleV (X := X) q' ⟨u ≫ m.1, hum⟩ := by
  funext p
  apply Subtype.ext
  rw [unitE_smul_apply, singleV_same]
  by_cases hp : p = q'
  · subst hp; rw [idTo_self, Category.id_comp, singleV_same]
  · rw [idTo_ne hp, Limits.zero_comp, singleV_ne hp]; rfl

/-- Maps `V_X̃ → V_Ỹ` that scale the action of matrix units by `d`. -/
def IsScaled (d : D.PV × G → D.PV × G → k) {Y : ι × G} (f : VX D Dg T X →ₗ[k] VX D Dg T Y) :
    Prop :=
  ∀ (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1)
    (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u) (y : VX D Dg T X),
    f (MulOpposite.op (unitE T q' q u hu) • y) = d q'.1 q.1 • (MulOpposite.op (unitE T q' q u hu) • f y)

variable {d : D.PV × G → D.PV × G → k} {Y : ι × G} {f : VX D Dg T X →ₗ[k] VX D Dg T Y}

theorem IsScaled.concentrated (hf : IsScaled d f) (q : T)
    (m : Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) {p : T} (hp : p ≠ q) :
    f (singleV q m) p = 0 := by
  have hm := unitE_smul_single (X := X) q q (𝟙 _) (by rw [inv_mul_cancel]; exact Dg.isHom_id _) m
    (by rw [Category.id_comp]; exact m.2)
  have e : (⟨𝟙 _ ≫ m.1, by rw [Category.id_comp]; exact m.2⟩ :
      Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1) = m := Subtype.ext (Category.id_comp _)
  rw [e] at hm
  rw [← hm, hf]
  apply Subtype.ext
  change d q.1 q.1 • ((MulOpposite.op (unitE T q q (𝟙 _) _) • f (singleV q m) : VX D Dg T Y) p).1 = 0
  rw [unitE_smul_apply, idTo_ne hp, Limits.zero_comp, smul_zero]

theorem IsScaled.apply (hf : IsScaled d f) (y : VX D Dg T X) (p : T) :
    f y p = f (singleV p (y p)) p := by
  have hy : y = ∑ q, singleV q (y q) := by
    funext p'
    rw [VX_sum_apply, Finset.sum_eq_single p' (fun q _ hq ↦ singleV_ne (Ne.symm hq) _) (by simp), singleV_same]
  conv_lhs => rw [hy]
  rw [map_sum, VX_sum_apply, Finset.sum_eq_single p (fun q _ hq ↦ hf.concentrated q _ (Ne.symm hq))
    (by simp)]

theorem IsScaled.nat (hf : IsScaled d f) (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1)
    (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u) (m : Dg.part ((q.1.2)⁻¹ * X.2) q.1.1.1 X.1)
    (hum : u ≫ m.1 ∈ Dg.part ((q'.1.2)⁻¹ * X.2) q'.1.1.1 X.1) :
    (f (singleV q' ⟨u ≫ m.1, hum⟩) q').1 = d q'.1 q.1 • (u ≫ (f (singleV q m) q).1) := by
  rw [← unitE_smul_single q' q u hu m hum, hf]
  change d q'.1 q.1 • ((MulOpposite.op (unitE T q' q u hu) • f (singleV q m) : VX D Dg T Y) q').1 = _
  rw [unitE_smul_apply, idTo_self, Category.id_comp]

/-! ### Natural families from module maps -/

variable (Dg T X) in
/-- `T` contains the support of `V_X̃`. -/
def Supp : Prop := ∀ z : D.PV × G, z ∉ T → Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 = ⊥

/-- A family of maps `C̃(P_z, X̃) → C̃(P_z, Ỹ)` scaled by `d` along `L`. -/
structure ScFam (d : D.PV × G → D.PV × G → k) (X Y : ι × G) where
  φ : ∀ z : D.PV × G, (F z.1.1 ⟶ F X.1) →ₗ[k] (F z.1.1 ⟶ F Y.1)
  mem : ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
    φ z m ∈ Dg.part (z.2⁻¹ * Y.2) z.1.1 Y.1
  nat : ∀ (z z' : D.PV × G) (u : F z'.1.1 ⟶ F z.1.1) (m : F z.1.1 ⟶ F X.1),
    u ∈ Dg.part (z'.2⁻¹ * z.2) z'.1.1 z.1.1 → m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
    φ z' (u ≫ m) = d z' z • (u ≫ φ z m)

/-- An unscaled family is natural. -/
def ScFam.toNatFam (N : ScFam (D := D) (Dg := Dg) (fun _ _ ↦ 1) X Y) : NatFam D Dg X Y where
  φ := N.φ
  mem := N.mem
  nat z z' u m hu hm := by rw [N.nat z z' u m hu hm, one_smul]

variable (T) in
/-- The components of a map `V_X̃|_T → V_Ỹ|_T`, extended by zero. -/
def famOf (f : VX D Dg T X →ₗ[k] VX D Dg T Y) (z : D.PV × G) :
    (F z.1.1 ⟶ F X.1) →ₗ[k] (F z.1.1 ⟶ F Y.1) :=
  if hz : z ∈ T then
    (Dg.part ((z.2)⁻¹ * Y.2) z.1.1 Y.1).subtype ∘ₗ
      (LinearMap.proj (R := k) (φ := fun q : T ↦ Dg.part ((q.1.2)⁻¹ * Y.2) q.1.1.1 Y.1)
        (⟨z, hz⟩ : T)) ∘ₗ f ∘ₗ singleV (T := T) ⟨z, hz⟩ ∘ₗ
      LinearMap.codRestrict (Dg.part ((z.2)⁻¹ * X.2) z.1.1 X.1) (Dg.proj _ z.1.1 X.1)
        (fun m ↦ LinearMap.mem_range_self _ m)
  else 0

theorem famOf_apply (f : VX D Dg T X →ₗ[k] VX D Dg T Y) {z : D.PV × G} (hz : z ∈ T)
    {m : F z.1.1 ⟶ F X.1} (hm : m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1) :
    famOf T f z m = (f (singleV (T := T) ⟨z, hz⟩ ⟨m, hm⟩) ⟨z, hz⟩).1 := by
  have hc : (LinearMap.codRestrict (Dg.part ((z.2)⁻¹ * X.2) z.1.1 X.1) (Dg.proj _ z.1.1 X.1)
      (fun m ↦ LinearMap.mem_range_self _ m)) m = ⟨m, hm⟩ :=
    Subtype.ext ((HomGrading.mem_part_iff (D := Dg)).1 hm)
  rw [famOf, dif_pos hz]
  simp only [LinearMap.coe_comp, Function.comp_apply, hc]
  rfl

theorem famOf_mem (f : VX D Dg T X →ₗ[k] VX D Dg T Y) (z : D.PV × G) (m : F z.1.1 ⟶ F X.1) :
    famOf T f z m ∈ Dg.part (z.2⁻¹ * Y.2) z.1.1 Y.1 := by
  rw [famOf]
  split_ifs with hz
  · exact Submodule.coe_mem _
  · exact Submodule.zero_mem _

theorem eq_zero_of_supp (hX : Supp Dg T X) {z : D.PV × G} (hz : z ∉ T) {m : F z.1.1 ⟶ F X.1}
    (hm : m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1) : m = 0 := by
  rw [hX z hz, Submodule.mem_bot] at hm; exact hm

/-- **A scaled module map gives a scaled family.** -/
def scFamOf (hX : Supp Dg T X) (hY : Supp Dg T Y) (hf : IsScaled d f) : ScFam (D := D) (Dg := Dg) d X Y where
  φ := famOf T f
  mem z m _ := famOf_mem f z m
  nat z z' u m hu hm := by
    have hum : u ≫ m ∈ Dg.part (z'.2⁻¹ * X.2) z'.1.1 X.1 := by
      rw [HomGrading.mem_part_iff] at hu hm ⊢
      have := Dg.isHom_comp hu hm
      rwa [show z'.2⁻¹ * z.2 * (z.2⁻¹ * X.2) = z'.2⁻¹ * X.2 by group] at this
    by_cases hz' : z' ∈ T
    · by_cases hz : z ∈ T
      · rw [famOf_apply f hz' hum, famOf_apply f hz hm]
        exact hf.nat ⟨z', hz'⟩ ⟨z, hz⟩ u ((HomGrading.mem_part_iff (D := Dg)).1 hu) ⟨m, hm⟩ hum
      · rw [eq_zero_of_supp hX hz hm, Limits.comp_zero, map_zero, map_zero, Limits.comp_zero,
          smul_zero]
    · have h1 : u ≫ famOf T f z m = 0 := by
        apply eq_zero_of_supp hY hz'
        rw [HomGrading.mem_part_iff] at hu ⊢
        have := Dg.isHom_comp hu ((HomGrading.mem_part_iff (D := Dg)).1 (famOf_mem f z m))
        rwa [show z'.2⁻¹ * z.2 * (z.2⁻¹ * Y.2) = z'.2⁻¹ * Y.2 by group] at this
      rw [h1, smul_zero, famOf, dif_neg hz']
      rfl

/-! ### Indecomposability -/

/-- A module map as a `k`-linear map for the native structures. -/
def homK (θ : VM D Dg T X ⟶ VM D Dg T Y) : VX D Dg T X →ₗ[k] VX D Dg T Y where
  toFun := θ.hom
  map_add' := map_add _
  map_smul' c y := by
    rw [RingHom.id_apply, ← algebraMap_smul_VX]
    exact (map_smul θ.hom _ y).trans (algebraMap_smul_VX c _)

theorem homK_isScaled (θ : VM D Dg T X ⟶ VM D Dg T Y) : IsScaled (fun _ _ ↦ 1) (homK θ) := by
  intro q' q u hu y
  rw [one_smul]
  exact map_smul θ.hom _ y

include hfd in
/-- **Endomorphisms of `V_X̃` are scalars** ("Height gives `End(V_X̃) = k`"). -/
theorem end_eq_smul (H : HeightData Dg) (hX : Supp Dg T X) (θ : VM D Dg T X ⟶ VM D Dg T X) :
    ∃ c : k, ∀ y : VX D Dg T X, θ.hom y = c • y := by
  let N := (scFamOf hX hX (homK_isScaled θ)).toNatFam
  obtain ⟨g, hg, hφ⟩ := N.exists_hom
  rw [inv_mul_cancel] at hg
  obtain ⟨c, rfl⟩ := H.scalar_one hg
  refine ⟨c, fun y ↦ funext fun p ↦ Subtype.ext ?_⟩
  change (homK θ y p).1 = c • (y p).1
  rw [(homK_isScaled θ).apply y p, ← famOf_apply (homK θ) p.2 (y p).2]
  change N.φ p.1 (y p).1 = _
  rw [hφ p.1 _ (y p).2, Linear.comp_smul, Category.comp_id]

include hfd in
theorem exists_ne_zero (hX : Supp Dg T X) (h1 : 𝟙 (F X.1) ≠ 0) : ∃ y : VX D Dg T X, y ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h1
  refine eq_zero_of_lifted (D := D) (Dg := Dg) (𝟙 (F X.1)) fun z m hm ↦ ?_
  rw [Category.comp_id]
  by_cases hz : z ∈ T
  · have := congrFun (hall (singleV (T := T) ⟨z, hz⟩ ⟨m, hm⟩)) ⟨z, hz⟩
    rw [singleV_same] at this
    exact congrArg Subtype.val this
  · exact eq_zero_of_supp hX hz hm

include hfd in
/-- **`V_X̃|_T` is finite-dimensional and indecomposable.** -/
theorem VM_isFiniteIndecomposable (H : HeightData Dg) (hX : Supp Dg T X) (h1 : 𝟙 (F X.1) ≠ 0) :
    IsFiniteIndecomposable k (covT D Dg T) (VM D Dg T X) := by
  obtain ⟨y₀, hy₀⟩ := exists_ne_zero hX h1
  have hsm : ∀ (c : k) (y : VX D Dg T X), ((c • 𝟙 (VM D Dg T X)) : VM D Dg T X ⟶ _).hom y = c • y :=
    fun c y ↦ algebraMap_smul_VX c y
  have hloc : IsLocalRing (End (VM D Dg T X)) := by
    haveI : Nontrivial (End (VM D Dg T X)) := ⟨⟨1, 0, fun h ↦ hy₀ (by
      have := congrArg (fun θ : End (VM D Dg T X) ↦ θ.hom y₀) h
      exact this)⟩⟩
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro θ
    obtain ⟨c, hc⟩ := end_eq_smul H hX θ
    by_cases h0 : c = 0
    · right
      have : θ = 0 := ModuleCat.hom_ext (LinearMap.ext fun y ↦
        (hc y).trans (by
          rw [h0]
          have h00 : ∀ z : VX D Dg T X, (0 : k) • z = 0 := fun z ↦ zero_smul k z
          exact (h00 y).trans rfl))
      rw [this, sub_zero]
      exact isUnit_one
    · left
      refine ⟨⟨θ, c⁻¹ • 𝟙 _, ?_, ?_⟩, rfl⟩
      · refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
        change θ.hom ((c⁻¹ • 𝟙 (VM D Dg T X)).hom y) = y
        have hss : ∀ z : VX D Dg T X, c • c⁻¹ • z = z := fun z ↦ by
          rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
        exact (congrArg θ.hom (hsm c⁻¹ y)).trans ((hc _).trans (hss y))
      · refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
        change (c⁻¹ • 𝟙 (VM D Dg T X)).hom (θ.hom y) = y
        have hss : ∀ z : VX D Dg T X, c⁻¹ • c • z = z := fun z ↦ by
          rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
        exact (hsm c⁻¹ _).trans ((congrArg (fun z : VX D Dg T X ↦ c⁻¹ • z) (hc y)).trans (hss y))
  exact ⟨VM_finite, @MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _ _ _ _ _ hloc⟩

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
