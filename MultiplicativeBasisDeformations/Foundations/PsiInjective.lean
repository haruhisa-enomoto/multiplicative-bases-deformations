module

public import MultiplicativeBasisDeformations.Foundations.HochschildMesh

/-!
# Injectivity of `Ψ` (Proposition 7.6)

`weights-and-parameters.tex`: "If `Ψ[μ] = 0`, change the arrows to remove
the errors. They give a functor from `C ⊗ k[ε]/(ε²)` to the Hom category of the
lifted modules reducing to the identity. […] On the actual projective corner it
trivializes the algebra deformation with leading identity, so `[μ] = 0`."

A functor `C ⊗ k[ε] → (lifted modules)` reducing to the identity is recorded by
its `ε`-part: a derivation `δ` of `C` into the `k`-linear maps between evaluated
modules with `(rs φ, δ φ)` a lifted map for every `φ`. We build `δ` on paths
(`δp`), extend it linearly to the path category (`δL`), show that it kills the mesh
ideal once the mesh errors vanish (`δL_ideal`), and descend it to `C` (`δC`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
  (Ld : LiftData D hfin q μ)

/-! ### The derivation on paths -/

/-- The `ε`-part of the lifted path: `δ(p a) = a δ(p) + g_a p`. -/
def δp : ∀ {Y X : V}, Quiver.Path Y X →
    (Rep D.F0 (meshFam Q c Y) →ₗ[k] Rep D.F0 (meshFam Q c X))
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p a => fA D a ∘ₗ δp p + Ld.g a ∘ₗ rs D (pathMor c p)

theorem rs_zero {Y X : V} : rs D (0 : obj c Y ⟶ obj c X) = 0 := by
  ext m y; simp

theorem rs_id (Y : V) : rs D (𝟙 (obj c Y)) = LinearMap.id := by
  ext m y; simp

theorem isLiftHom_id (Y : V) : IsLiftHom (Ld.L Y) (Ld.L Y) LinearMap.id 0 :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ by simp⟩

theorem rs_pathMor_cons {Y X Z : V} (p : Quiver.Path Y X) (a : X ⟶ Z) :
    rs D (pathMor c (p.cons a)) = fA D a ∘ₗ rs D (pathMor c p) := by
  rw [← Quiver.Path.comp_toPath_eq_cons, pathMor_comp, ← rs_comp, pathMor_toPath]
  rfl

theorem δp_lift {Y X : V} (p : Quiver.Path Y X) :
    IsLiftHom (Ld.L Y) (Ld.L X) (rs D (pathMor c p)) (δp Ld p) := by
  induction p with
  | nil => rw [pathMor_nil, rs_id, δp]; exact isLiftHom_id Ld Y
  | cons p a ih =>
    rw [rs_pathMor_cons, δp]
    exact (Ld.lift a).comp ih

theorem δp_comp {Y X : V} (p : Quiver.Path Y X) : ∀ {Z : V} (p' : Quiver.Path X Z),
    δp Ld (p.comp p') = rs D (pathMor c p') ∘ₗ δp Ld p + δp Ld p' ∘ₗ rs D (pathMor c p) := by
  intro Z p'
  induction p' with
  | nil => simp [δp, pathMor_nil, rs_id]
  | cons p' a ih =>
    rw [Quiver.Path.comp_cons, δp, ih, δp, rs_pathMor_cons, pathMor_comp, ← rs_comp]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc]
    abel

/-! ### Linear extension to the path category -/

/-- The linear extension of `δp` to the morphisms of `kQ`. -/
def δL {Y X : V} : (LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) →ₗ[k]
    (Rep D.F0 (meshFam Q c Y) →ₗ[k] Rep D.F0 (meshFam Q c X)) :=
  (Finsupp.linearCombination k (fun p : Quiver.Path Y X ↦ δp Ld p)).comp
    (LinearPaths.finsuppEquiv (k := k) Y X).toLinearMap

theorem δL_path {Y X : V} (p : Quiver.Path Y X) : δL Ld (LinearPaths.path (k := k) p) = δp Ld p := by
  simp [δL, LinearPaths.finsuppEquiv]

/-- The image of a morphism of `kQ` in `C`. -/
abbrev img {Y X : V} (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    obj c Y ⟶ obj c X :=
  (RelationCategory.functor k (meshRelations c)).map F

theorem img_zero {Y X : V} :
    img (c := c) (0 : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) = 0 :=
  Functor.map_zero _ _ _

theorem img_path {Y X : V} (p : Quiver.Path Y X) : img (c := c) (LinearPaths.path p) = pathMor c p :=
  rfl

theorem kQ_induction {Y X : V} {P : (LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) → Prop}
    (h0 : P 0) (hadd : ∀ F G, P F → P G → P (F + G)) (hsmul : ∀ (t : k) F, P F → P (t • F))
    (hpath : ∀ p, P (LinearPaths.path p)) (F) : P F := by
  have : F = LinearPaths.ofFinsupp (LinearPaths.toFinsupp F) := rfl
  rw [this]
  induction LinearPaths.toFinsupp F using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg => exact hadd _ _ hf hg
  | single p t =>
    have : LinearPaths.ofFinsupp (Finsupp.single p t) = t • LinearPaths.path (k := k) p := by
      change Finsupp.single p t = t • Finsupp.single p 1
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact hsmul _ _ (hpath p)

theorem rs_img_add {Y X : V} (F G : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    rs D (img (c := c) (F + G)) = rs D (img (c := c) F) + rs D (img (c := c) G) := by
  rw [img, Functor.map_add, rs_add]

theorem rs_img_smul {Y X : V} (t : k) (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    rs D (img (c := c) (t • F)) = t • rs D (img (c := c) F) := by
  rw [img, Functor.map_smul, rs_smul]

theorem δL_lift {Y X : V} (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    IsLiftHom (Ld.L Y) (Ld.L X) (rs D (img (c := c) F)) (δL Ld F) := by
  induction F using kQ_induction with
  | h0 => rw [img_zero, rs_zero, map_zero]; exact isLiftHom_zero
  | hadd F G hF hG => rw [rs_img_add, map_add]; exact hF.add hG
  | hsmul t F hF => rw [rs_img_smul, map_smul]; exact hF.smul t
  | hpath p => rw [img_path, δL_path]; exact δp_lift Ld p

theorem δL_comp {Y X Z : V} (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X)
    (G : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj (k := k) Z) :
    δL Ld (F ≫ G) = rs D (img (c := c) G) ∘ₗ δL Ld F + δL Ld G ∘ₗ rs D (img (c := c) F) := by
  induction F using kQ_induction with
  | h0 => rw [Limits.zero_comp, map_zero, map_zero, img_zero, rs_zero, LinearMap.comp_zero,
      LinearMap.comp_zero, add_zero]
  | hadd F F' hF hF' =>
    rw [Preadditive.add_comp, map_add, hF, hF', map_add, rs_img_add]
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    abel
  | hsmul t F hF =>
    rw [Linear.smul_comp, map_smul, hF, map_smul, rs_img_smul]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, smul_add]
  | hpath p =>
    induction G using kQ_induction with
    | h0 => rw [Limits.comp_zero, map_zero, map_zero, img_zero, rs_zero, LinearMap.zero_comp,
        LinearMap.zero_comp, add_zero]
    | hadd G G' hG hG' =>
      rw [Preadditive.comp_add, map_add, hG, hG', map_add, rs_img_add]
      simp only [LinearMap.comp_add, LinearMap.add_comp]
      abel
    | hsmul t G hG =>
      rw [Linear.comp_smul, map_smul, hG, map_smul, rs_img_smul]
      simp only [LinearMap.comp_smul, LinearMap.smul_comp, smul_add]
    | hpath p' =>
      rw [LinearPaths.path_comp_path, δL_path, δL_path, δL_path, img_path, img_path, δp_comp]

/-! ### The mesh ideal and descent to `C` -/

theorem δp_toPath {Y X : V} (a : Y ⟶ X) : δp Ld a.toPath = Ld.g a := by
  change δp Ld (Quiver.Path.cons Quiver.Path.nil a) = _
  rw [δp, δp, pathMor_nil, rs_id]
  simp

/-- **The `ε`-part of a mesh relation is the mesh error.** -/
theorem δL_meshRelation (x : Q.nonprojective) : δL Ld (meshRelation c x) = zE Ld x := by
  rw [meshRelation, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, δL_path, δp_comp, δp_toPath, δp_toPath, pathMor_toPath, pathMor_toPath]
  rfl

theorem img_add' {Y X : V} (F G : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    img (c := c) (F + G) = img (c := c) F + img (c := c) G := Functor.map_add _

theorem img_sub {Y X : V} (F G : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    img (c := c) (F - G) = img (c := c) F - img (c := c) G := Functor.map_sub _

theorem img_smul' {Y X : V} (t : k) (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    img (c := c) (t • F) = t • img (c := c) F := Functor.map_smul _ _ _

theorem img_comp {Y X Z : V} (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X)
    (G : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj (k := k) Z) :
    img (c := c) (F ≫ G) = img (c := c) F ≫ img (c := c) G := Functor.map_comp _ _ _

theorem img_meshRelation (x : Q.nonprojective) : img (c := c) (meshRelation c x) = 0 := by
  rw [img, RelationCategory.functor_map_eq_zero_iff]
  refine CategoricalIdeal.HomIdeal.relation_mem_linearSpan _ ⟨x, rfl, rfl, ?_⟩
  simp

variable {Ld}

theorem δL_sandwich (hz : ∀ x, zE Ld x = 0) {Y X : V} (x : Q.nonprojective)
    (a : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) (Q.tau x).1)
    (b : LinearPaths.obj (k := k) x.1 ⟶ LinearPaths.obj (k := k) X) :
    δL Ld (a ≫ meshRelation c x ≫ b) = 0 := by
  rw [δL_comp, δL_comp, δL_meshRelation, hz, img_comp, img_meshRelation, Limits.zero_comp]
  simp only [rs_zero, LinearMap.comp_zero, LinearMap.zero_comp, zero_add]

/-- **When the mesh errors vanish, the derivation kills the mesh ideal.** -/
theorem δL_ideal (hz : ∀ x, zE Ld x = 0) {Y X : V}
    {F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X}
    (hF : F ∈ (CategoricalIdeal.HomIdeal.linearSpan k (meshRelations c)).hom
      (LinearPaths.obj Y) (LinearPaths.obj X)) : δL Ld F = 0 := by
  rw [CategoricalIdeal.HomIdeal.linearSpan_hom] at hF
  change F ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule k (meshRelations c) _ _ at hF
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, B, r, hr, a, b, rfl⟩ := hf
    obtain ⟨x, hA, hB, rfl⟩ := hr
    change A = LinearPaths.obj (k := k) (Q.tau x).1 at hA
    change B = LinearPaths.obj (k := k) x.1 at hB
    subst hA hB
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact δL_sandwich hz x a b
  | zero => exact map_zero _
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul t f _ hf => rw [map_smul, hf, smul_zero]

theorem δL_eq_of_img (hz : ∀ x, zE Ld x = 0) {Y X : V}
    {F G : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X}
    (h : img (c := c) F = img (c := c) G) : δL Ld F = δL Ld G := by
  have : img (c := c) (F - G) = 0 := by rw [img_sub]; exact sub_eq_zero.2 h
  rw [img, RelationCategory.functor_map_eq_zero_iff] at this
  have h0 := δL_ideal hz this
  rwa [map_sub, sub_eq_zero] at h0

/-- A preimage in `kQ` of a morphism of `C`. -/
def pre {Y X : V} (φ : obj c Y ⟶ obj c X) : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X :=
  Classical.choose (RelationCategory.functor_map_surjective (meshRelations c) φ)

theorem img_pre {Y X : V} (φ : obj c Y ⟶ obj c X) : img (c := c) (pre φ) = φ :=
  Classical.choose_spec (RelationCategory.functor_map_surjective (meshRelations c) φ)

variable (hz : ∀ x, zE Ld x = 0)

/-- **The derivation on `C`**: the `ε`-part of the functor `C ⊗ k[ε] → (lifted modules)`. -/
def δC {Y X : V} : (obj c Y ⟶ obj c X) →ₗ[k]
    (Rep D.F0 (meshFam Q c Y) →ₗ[k] Rep D.F0 (meshFam Q c X)) where
  toFun φ := δL Ld (pre φ)
  map_add' φ ψ := by
    rw [← map_add]
    exact δL_eq_of_img hz (by rw [img_pre, img_add', img_pre, img_pre])
  map_smul' t φ := by
    rw [← map_smul]
    exact δL_eq_of_img hz (by rw [img_pre, img_smul', img_pre]; rfl)

theorem δC_img {Y X : V} (F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X) :
    δC hz (img (c := c) F) = δL Ld F :=
  δL_eq_of_img hz (img_pre _)

theorem δC_lift {Y X : V} (φ : obj c Y ⟶ obj c X) :
    IsLiftHom (Ld.L Y) (Ld.L X) (rs D φ) (δC hz φ) := by
  have := δL_lift Ld (pre φ)
  rwa [img_pre] at this

theorem δC_comp {Y X Z : V} (φ : obj c Y ⟶ obj c X) (ψ : obj c X ⟶ obj c Z) :
    δC hz (φ ≫ ψ) = rs D ψ ∘ₗ δC hz φ + δC hz ψ ∘ₗ rs D φ := by
  have : φ ≫ ψ = img (c := c) (pre φ ≫ pre ψ) := by rw [img_comp, img_pre, img_pre]
  rw [this, δC_img, δL_comp, img_pre, img_pre]
  rfl

theorem δC_pathMor {Y X : V} (p : Quiver.Path Y X) : δC hz (pathMor c p) = δp Ld p := by
  rw [← img_path, δC_img, δL_path]

theorem δC_id (Y : V) : δC hz (𝟙 (obj c Y)) = 0 := by
  rw [← pathMor_nil, δC_pathMor, δp]

/-! ### The projective corner

`Δ_X(m) = ∑_s δ(m_s)(e_s)` on an evaluated module; every `δφ` is the commutator of
`Δ` with `φ`. On the projective corner, `Δ` becomes a linear map of `A₀` satisfying the
hypothesis of `GExt.eq_hcobdry_of_derivation`. -/

/-- `Δ_X(m) = ∑_s δ(m_s)(e_s)`. -/
def Δm (X : V) : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X) where
  toFun m := ∑ s : D.PV, δC hz (Y := s.1) (X := X) (m s) (unit (F := D.F0) s)
  map_add' m n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    change δC hz (m s + n s) _ = _
    rw [map_add, LinearMap.add_apply]
  map_smul' t m := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    change δC hz (t • m s) _ = _
    rw [map_smul, LinearMap.smul_apply]

theorem Δm_apply (X : V) (m : Rep D.F0 (meshFam Q c X)) :
    Δm hz X m = ∑ s : D.PV, δC hz (Y := s.1) (X := X) (m s) (unit (F := D.F0) s) := rfl

theorem rep_eq_sum {X : V} (n : Rep D.F0 (meshFam Q c X)) :
    ∑ s : D.PV, rs D (X := s.1) (n s) (unit (F := D.F0) s) = n := by
  ext y
  rw [Rep.sum_apply]
  exact sum_idTo_comp (F := D.F0) y n

theorem rs_act {Y X : V} (f : obj c Y ⟶ obj c X) (m : Rep D.F0 (meshFam Q c Y))
    (b : (Alg D.F0)ᵐᵒᵖ) :
    rs D f ((gmodEv D hfin Y).act m b) = (gmodEv D hfin X).act (rs D f m) b :=
  (repMap (F := D.F0) f).map_smul b.unop m

/-- **`δφ` is the commutator of `Δ` with `φ`.** -/
theorem δC_comm {Y X : V} (φ : obj c Y ⟶ obj c X) (n : Rep D.F0 (meshFam Q c Y)) :
    δC hz φ n = Δm hz X (rs D φ n) - rs D φ (Δm hz Y n) := by
  rw [eq_sub_iff_add_eq, Δm_apply, Δm_apply, map_sum]
  have e := congrArg (δC hz φ) (rep_eq_sum (D := D) n)
  rw [← e, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  change _ = δC hz (n s ≫ φ) _
  rw [δC_comp]
  rw [add_comm]
  rfl

/-! #### Transport to `A₀` -/

variable (D hfin) in
/-- The coordinate `ψ_p : M_p → A₀` of an evaluated projective. -/
abbrev ψP (p : D.PV) : Rep D.F0 (meshFam Q c p.1) →ₗ[k] (Alg D.F0)ᵐᵒᵖ := (cycProj D hfin p).ψ

variable (D) in
/-- The idempotent `e_p` of `A₀`. -/
abbrev eP (p : D.PV) : (Alg D.F0)ᵐᵒᵖ := MulOpposite.op (idem (F := D.F0) p)

variable (D hfin) in
/-- `b ↦ e_p·b ∈ M_p`. -/
abbrev gA (p : D.PV) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c p.1) :=
  (gmodEv D hfin p.1).act (unit (F := D.F0) p)

theorem ψP_unit (p : D.PV) : ψP D hfin p (unit (F := D.F0) p) = eP D p := rfl

theorem ψP_act (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1)) (b : (Alg D.F0)ᵐᵒᵖ) :
    ψP D hfin p ((gmodEv D hfin p.1).act m b) = ψP D hfin p m * b :=
  (cycProj D hfin p).ψ_act m b

theorem act_ψP (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1)) : gA D hfin p (ψP D hfin p m) = m :=
  (cycProj D hfin p).act_ψ m

theorem ψP_gA (p : D.PV) (b : (Alg D.F0)ᵐᵒᵖ) : ψP D hfin p (gA D hfin p b) = eP D p * b := by
  rw [gA, ψP_act, ψP_unit]

theorem eP_mul_ψP (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1)) :
    eP D p * ψP D hfin p m = ψP D hfin p m := by
  conv_rhs => rw [← act_ψP (hfin := hfin) p m]
  rw [ψP_gA]

theorem eP_idem (p : D.PV) : eP D p * eP D p = eP D p := by
  rw [eP, ← MulOpposite.op_mul, idem_mul_idem]

theorem sum_eP : ∑ p, eP D p = 1 := by
  rw [← Finset.op_sum, ← MulOpposite.op_one]
  congr 1
  ext y z
  rw [CatAlg.sum_apply, CatAlg.one_apply]
  simp only [idem, colAlg, unit]
  exact sum_idTo_comp y (fun x ↦ idTo (F := D.F0) x z)

theorem gA_one (p : D.PV) : gA D hfin p 1 = unit (F := D.F0) p :=
  (gmodEv D hfin p.1).act_one _

theorem ψP_rs {r p : D.PV} (f : obj c r.1 ⟶ obj c p.1) (n : Rep D.F0 (meshFam Q c r.1)) :
    ψP D hfin p (rs D f n) = ψP D hfin p (rs D f (unit (F := D.F0) r)) * ψP D hfin r n := by
  conv_lhs => rw [← act_ψP (hfin := hfin) r n]
  rw [gA, rs_act, ψP_act]

theorem gA_apply (p : D.PV) (x : (Alg D.F0)ᵐᵒᵖ) (r : D.PV) : gA D hfin p x r = x.unop r p :=
  sum_comp_idTo_alg x.unop r p

theorem sum_ψP_rs (x : (Alg D.F0)ᵐᵒᵖ) (r : D.PV) :
    ∑ p, ψP D hfin p (rs D (X := r.1) (Y := p.1) (gA D hfin p x r) (unit (F := D.F0) r)) =
      x * eP D r := by
  apply MulOpposite.unop_injective
  ext y z
  rw [Finset.unop_sum, CatAlg.sum_apply, MulOpposite.unop_mul, CatAlg.mul_apply]
  have e1 : ∀ p : D.PV, (ψP D hfin p (rs D (X := r.1) (Y := p.1) (gA D hfin p x r)
      (unit (F := D.F0) r))).unop y z = (idTo (F := D.F0) y r ≫ x.unop r p) ≫ idTo p z := by
    intro p
    rw [← gA_apply (hfin := hfin) p x r]
    rfl
  simp only [e1]
  rw [sum_comp_idTo (F := D.F0) z (fun p ↦ idTo (F := D.F0) y r ≫ x.unop r p)]
  simp only [eP, MulOpposite.unop_op, idem, colAlg, unit, Category.assoc]
  rw [← Preadditive.comp_sum, sum_idTo_comp_alg]

theorem sum_sum_ψP_rs (x : (Alg D.F0)ᵐᵒᵖ) (n : ∀ r : D.PV, Rep D.F0 (meshFam Q c r.1)) :
    ∑ p, ∑ r, ψP D hfin p (rs D (X := r.1) (Y := p.1) (gA D hfin p x r) (n r)) =
      x * ∑ r, ψP D hfin r (n r) := by
  simp_rw [ψP_rs (D := D) (hfin := hfin) _ (n _)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_ψP_rs, mul_assoc, eP_mul_ψP, Finset.mul_sum]

theorem sum_rs_gA (p : D.PV) (x b : (Alg D.F0)ᵐᵒᵖ) :
    ∑ r, rs D (X := r.1) (Y := p.1) (gA D hfin p x r) (gA D hfin r b) = gA D hfin p (x * b) := by
  simp only [gA, rs_act]
  rw [← LinearMap.sum_apply, ← map_sum, rep_eq_sum, (gmodEv D hfin p.1).act_mul]

variable (D hfin) in
/-- **The derivation on `A₀`**: `Δ̂(b) = ∑_p ψ_p(Δ_p(e_p b))`. -/
def Dfull : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
  ∑ p : D.PV, ψP D hfin p ∘ₗ Δm hz p.1 ∘ₗ gA D hfin p

theorem Dfull_apply (b : (Alg D.F0)ᵐᵒᵖ) :
    Dfull D hfin hz b = ∑ p, ψP D hfin p (Δm hz p.1 (gA D hfin p b)) := by
  simp [Dfull, LinearMap.sum_apply]

variable (hreg : ∀ (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1)) (b : (Alg D.F0)ᵐᵒᵖ),
  (Ld.L p.1).act m b = gA D hfin p (μ (ψP D hfin p m) b))

include hreg in
/-- **The derivation identity on `A₀`.** -/
theorem Dfull_eq (x b : (Alg D.F0)ᵐᵒᵖ) :
    Dfull D hfin hz (x * b) - x * Dfull D hfin hz b -
        (Dfull D hfin hz x - x * Dfull D hfin hz 1) * b =
      ∑ p, eP D p * μ (eP D p * x) b - x * ∑ p, eP D p * μ (eP D p) b := by
  have key : ∀ p r : D.PV,
      ψP D hfin p (Δm hz p.1 (rs D (gA D hfin p x r) (gA D hfin r b))) -
          ψP D hfin p (rs D (gA D hfin p x r) (Δm hz r.1 (gA D hfin r b))) -
          (ψP D hfin p (Δm hz p.1 (rs D (gA D hfin p x r) (unit (F := D.F0) r))) * b -
            ψP D hfin p (rs D (gA D hfin p x r) (Δm hz r.1 (unit (F := D.F0) r))) * b) =
        eP D p * μ (ψP D hfin p (rs D (gA D hfin p x r) (unit (F := D.F0) r))) b -
          ψP D hfin p (rs D (gA D hfin p x r) (gA D hfin r (μ (eP D r) b))) := by
    intro p r
    have hL := (δC_lift hz (X := p.1) (Y := r.1) (gA D hfin p x r)).2 (unit (F := D.F0) r) b
    rw [δC_comm, δC_comm, hreg, hreg, ψP_unit] at hL
    have h2 := congrArg (ψP D hfin p) hL
    simp only [map_sub, LinearMap.sub_apply, ψP_act, ψP_unit] at h2
    exact h2
  have P1 : Dfull D hfin hz (x * b) =
      ∑ p, ∑ r, ψP D hfin p (Δm hz p.1 (rs D (gA D hfin p x r) (gA D hfin r b))) := by
    rw [Dfull_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← sum_rs_gA, map_sum, map_sum]
  have P2 : Dfull D hfin hz x =
      ∑ p, ∑ r, ψP D hfin p (Δm hz p.1 (rs D (gA D hfin p x r) (unit (F := D.F0) r))) := by
    rw [Dfull_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← map_sum, ← map_sum, rep_eq_sum]
  have P3 : x * Dfull D hfin hz b =
      ∑ p, ∑ r, ψP D hfin p (rs D (gA D hfin p x r) (Δm hz r.1 (gA D hfin r b))) := by
    rw [sum_sum_ψP_rs, Dfull_apply]
  have P4 : x * Dfull D hfin hz 1 =
      ∑ p, ∑ r, ψP D hfin p (rs D (gA D hfin p x r) (Δm hz r.1 (unit (F := D.F0) r))) := by
    rw [sum_sum_ψP_rs, Dfull_apply]
    simp only [gA_one]
  have P5 : ∑ p, eP D p * μ (eP D p * x) b =
      ∑ p, ∑ r, eP D p * μ (ψP D hfin p (rs D (gA D hfin p x r) (unit (F := D.F0) r))) b := by
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum, rep_eq_sum, ψP_gA]
  have P6 : x * ∑ p, eP D p * μ (eP D p) b =
      ∑ p, ∑ r, ψP D hfin p (rs D (gA D hfin p x r) (gA D hfin r (μ (eP D r) b))) := by
    rw [sum_sum_ψP_rs]
    simp only [ψP_gA]
  rw [P1, P2, P3, P4, P5, P6, sub_mul, Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun r _ ↦ key p r

/-! ### Removing the mesh errors

"If `Ψ[μ] = 0`, change the arrows to remove the errors." -/

theorem rs_deg {X Y : V} {s : ℕ} {f : obj c X ⟶ obj c Y} (hf : f ∈ degreePart c s X Y) {p : ℤ}
    {m : Rep D.F0 (meshFam Q c X)} (hm : (zgrEv D hfin X).IsHom p m) :
    (zgrEv D hfin Y).IsHom (p + s) (rs D f m) :=
  repMap_isHom (D := D) hfin hf hm

theorem isLiftHom_rs {Y X : V} (L₁ : ActLift μ (q : ℤ) (gmodEv D hfin Y))
    (L₂ : ActLift μ (q : ℤ) (gmodEv D hfin X)) (f : obj c Y ⟶ obj c X) :
    IsLiftHom L₁ L₂ 0 (rs D f) :=
  (isLiftHom_zero_iff _ _ _).2 fun m b ↦ rs_act f m b

/-- **Changing the arrows by a family `f` of degree `q + 1`.** -/
def LiftData.shift (Ld : LiftData D hfin q μ) (f : ArrowFamily c) (hf : f ∈ familiesDeg c (q + 1)) :
    LiftData D hfin q μ where
  L := Ld.L
  g a := Ld.g a - rs D (f ⟨_, _, a⟩)
  lift a := by
    have := (Ld.lift a).add ((isLiftHom_rs (Ld.L _) (Ld.L _) (f ⟨_, _, a⟩)).smul (-1))
    simpa [sub_eq_add_neg] using this
  deg a p m hm := by
    have h1 := Ld.deg a p m hm
    have h2 := rs_deg (hfin := hfin) (hf ⟨_, _, a⟩) hm
    rw [show p + ((q + 1 : ℕ) : ℤ) = p + (1 + (q : ℤ)) by push_cast; ring] at h2
    rw [LinearMap.sub_apply, sub_eq_add_neg]
    exact ZGr.isHom_add _ h1 (ZGr.isHom_neg _ h2)

theorem zE_shift (Ld : LiftData D hfin q μ) (f : ArrowFamily c) (hf : f ∈ familiesDeg c (q + 1))
    (x : Q.nonprojective) :
    zE (Ld.shift f hf) x = zE Ld x - rs D (meshDerivative c f x) := by
  rw [meshDerivative, rs_sum, zE, zE, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [rs_smul, ← smul_sub, rs_add, ← rs_comp, ← rs_comp]
  simp only [LiftData.shift, LinearMap.comp_sub, LinearMap.sub_comp]
  congr 1
  change _ = _ - (fA D a.2 ∘ₗ _ + _ ∘ₗ fA D _)
  abel

/-- **If `Ψ[μ] = 0`, the arrows can be changed to remove the mesh errors.** -/
theorem exists_zE_zero (Ld : LiftData D hfin q μ) (h : Ψc Ld = 0) :
    ∃ Ld' : LiftData D hfin q μ, Ld'.L = Ld.L ∧ ∀ x, zE Ld' x = 0 := by
  unfold Ψc at h
  rw [Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨f, hf, hfd⟩ := h
  refine ⟨Ld.shift f hf, rfl, fun x ↦ ?_⟩
  rw [zE_shift, show meshDerivative c f x = zhat Ld x from congrFun hfd x, zhat_spec', sub_self]

/-! ### Degrees -/

theorem δp_deg {Y X : V} (p : Quiver.Path Y X) {e : ℤ} {m : Rep D.F0 (meshFam Q c Y)}
    (hm : (zgrEv D hfin Y).IsHom e m) :
    (zgrEv D hfin X).IsHom (e + ((p.length : ℤ) + q)) (δp Ld p m) := by
  induction p with
  | nil => rw [δp]; exact ZGr.isHom_zero _ _
  | cons p a ih =>
    rw [δp, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have h1 := fA_deg D hfin a ih
    have h2 := Ld.deg a _ _ (rs_deg (hfin := hfin) (pathMor_mem_degreePart (c := c) p) hm)
    rw [Quiver.Path.length_cons]
    have e1 : e + ((p.length : ℤ) + q) + 1 = e + (((p.length + 1 : ℕ) : ℤ) + q) := by
      push_cast; ring
    have e2 : e + (p.length : ℤ) + (1 + q) = e + (((p.length + 1 : ℕ) : ℤ) + q) := by
      push_cast; ring
    rw [e1] at h1
    rw [e2] at h2
    exact ZGr.isHom_add _ h1 h2

theorem δL_deg {Y X : V} {d : ℕ} {F : LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (k := k) X}
    (hF : F ∈ LinearPaths.degreePart d Y X) {e : ℤ} {m : Rep D.F0 (meshFam Q c Y)}
    (hm : (zgrEv D hfin Y).IsHom e m) :
    (zgrEv D hfin X).IsHom (e + ((d : ℤ) + q)) (δL Ld F m) := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨p, hp, rfl⟩ := hf
    rw [δL_path, ← hp]
    exact δp_deg p hm
  | zero => rw [map_zero, LinearMap.zero_apply]; exact ZGr.isHom_zero _ _
  | add f g _ _ hf hg => rw [map_add, LinearMap.add_apply]; exact ZGr.isHom_add _ hf hg
  | smul t f _ hf => rw [map_smul, LinearMap.smul_apply]; exact ZGr.isHom_smul _ t hf

theorem δC_deg {Y X : V} {d : ℕ} {φ : obj c Y ⟶ obj c X} (hφ : φ ∈ degreePart c d Y X) {e : ℤ}
    {m : Rep D.F0 (meshFam Q c Y)} (hm : (zgrEv D hfin Y).IsHom e m) :
    (zgrEv D hfin X).IsHom (e + ((d : ℤ) + q)) (δC hz φ m) := by
  obtain ⟨F, hF, rfl⟩ := hφ
  change (zgrEv D hfin X).IsHom _ (δC hz (img (c := c) F) m)
  rw [δC_img]
  exact δL_deg hF hm

theorem unit_isHom (s : D.PV) : (zgrEv D hfin s.1).IsHom 0 (unit (F := D.F0) s) :=
  (cycProj D hfin s).hg

theorem Δm_deg (X : V) {d : ℤ} {m : Rep D.F0 (meshFam Q c X)} (hm : (zgrEv D hfin X).IsHom d m) :
    (zgrEv D hfin X).IsHom (d + q) (Δm hz X m) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [(zgrEv_isHom_neg D hfin X hd m).1 hm, map_zero]; exact ZGr.isHom_zero _ _
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  rw [zgrEv_isHom] at hm
  rw [Δm_apply]
  refine ZGr.isHom_sum _ _ _ fun s _ ↦ ?_
  have := δC_deg hz (hm s) (unit_isHom (hfin := hfin) s)
  rwa [zero_add] at this

theorem eP_isHom (p : D.PV) : (galgA0 D hfin).gr.IsHom 0 (eP D p) := by
  have := (cycProj D hfin p).ψ_deg 0 _ (unit_isHom (hfin := hfin) p)
  rwa [show (cycProj D hfin p).b = 0 from rfl, sub_self] at this

theorem Dfull_deg {d : ℤ} {b : (Alg D.F0)ᵐᵒᵖ} (hb : (galgA0 D hfin).gr.IsHom d b) :
    (galgA0 D hfin).gr.IsHom (d + q) (Dfull D hfin hz b) := by
  rw [Dfull_apply]
  refine ZGr.isHom_sum _ _ _ fun p _ ↦ ?_
  have h1 := (gmodEv D hfin p.1).act_hom _ _ _ _ (unit_isHom (hfin := hfin) p) hb
  rw [zero_add] at h1
  have h2 := (cycProj D hfin p).ψ_deg _ _ (Δm_deg hz p.1 h1)
  rwa [show (cycProj D hfin p).b = 0 from rfl, sub_zero] at h2

/-! ### Injectivity of `Ψ` -/

theorem stdL_act (J : D.InjData) (h1 : DegOne D) (hμ : IsHCocycle μ)
    (hμdeg : HDeg (galgA0 D hfin) μ (q : ℤ)) (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1))
    (b : (Alg D.F0)ᵐᵒᵖ) :
    (stdL J h1 hμ hμdeg p.1).act m b = gA D hfin p (μ (ψP D hfin p m) b) := by
  rw [stdL, dif_pos p.2]
  exact CycProj.actLift_act hμdeg hμ _ m b

/-- **Proposition 7.6, injectivity** (`weights-and-parameters.tex`): if `Ψ[μ] = 0`,
then `μ` is the coboundary of a map of degree `q`. -/
theorem eq_hcobdry_of_Ψc_eq_zero (J : D.InjData) (h1 : DegOne D) (hμ : IsHCocycle μ)
    (hμdeg : HDeg (galgA0 D hfin) μ (q : ℤ)) (Ld : LiftData D hfin q μ) (h : Ψc Ld = 0) :
    ∃ H : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
      (∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + q) (H a)) ∧
      μ = hcobdry H := by
  obtain ⟨Ld₀, hL₀⟩ := exists_liftData J h1 hμ hμdeg
  have h0 : Ψc Ld₀ = 0 := (Ψc_indep J h1 Ld Ld₀).trans h
  obtain ⟨Ld₁, hL₁, hz⟩ := exists_zE_zero Ld₀ h0
  have hreg : ∀ (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1)) (b : (Alg D.F0)ᵐᵒᵖ),
      (Ld₁.L p.1).act m b = gA D hfin p (μ (ψP D hfin p m) b) := by
    intro p m b
    rw [hL₁, hL₀]
    exact stdL_act J h1 hμ hμdeg p m b
  refine ⟨_, ?_, eq_hcobdry_of_derivation (eP D) eP_idem sum_eP hμ (Dfull D hfin hz)
    (Dfull_eq hz hreg)⟩
  intro p a ha
  have G1 := (galgA0 D hfin).one_hom
  have hw : (galgA0 D hfin).gr.IsHom (q : ℤ)
      (μ 1 1 + ∑ i, μ (eP D i) (eP D i) + Dfull D hfin hz 1) := by
    refine ZGr.isHom_add _ (ZGr.isHom_add _ ?_ (ZGr.isHom_sum _ _ _ fun i _ ↦ ?_)) ?_
    · have := hμdeg 0 0 1 1 G1 G1; rwa [zero_add, zero_add] at this
    · have := hμdeg 0 0 _ _ (eP_isHom (hfin := hfin) i) (eP_isHom (hfin := hfin) i)
      rwa [zero_add, zero_add] at this
    · have := Dfull_deg hz G1; rwa [zero_add] at this
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  refine ZGr.isHom_add _ (ZGr.isHom_add _ ?_ (ZGr.isHom_neg _ (ZGr.isHom_sum _ _ _ fun i _ ↦ ?_)))
    (ZGr.isHom_neg _ (Dfull_deg hz ha))
  · have := (galgA0 D hfin).mul_hom _ _ _ _ hw ha; rwa [add_comm] at this
  · have := hμdeg _ _ _ _ (eP_isHom (hfin := hfin) i)
      ((galgA0 D hfin).mul_hom _ _ _ _ (eP_isHom (hfin := hfin) i) ha)
    rwa [zero_add, zero_add] at this

end MeshWalk

end MultiplicativeBasisDeformations
