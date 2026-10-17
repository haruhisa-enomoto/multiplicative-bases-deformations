import MultiplicativeBasisDeformations.Foundations.MGrading
import MultiplicativeBasisDeformations.Foundations.MeshWeights
import MultiplicativeBasisDeformations.Foundations.HochschildMesh
import MultiplicativeBasisDeformations.Foundations.BinaryNormalization

/-!
# Mesh-weight gradings of `A₀` and of its evaluated modules

`weights-and-parameters.tex:248–262`: "a mesh weight `w` grades `V_{m+1}(C)` by giving a
path at row `v` the weight `w(path) − ν_v`, and grades `U_m(C)` …", and
`weights-and-parameters.tex:396–400`: "Lift a basis of the integer ray weights to mesh
weights using Lemma 7.4. These give simultaneous gradings on the lifted modules."

A mesh weight `W` with values in an abelian group `M` is a path weight for which all
meshes are homogeneous (`MeshWt.homog`), so it grades every Hom space of `C` (`wπ`),
compatibly with composition and with the length grading (`wπ_degProj`). It grades `A₀`
(`grA0`, `latA0`) and each evaluated module `M_X` (`grEv`); the action of a homogeneous
element of `A₀`, the arrow maps and all evaluated morphisms shift weights
(`act_shift`, `fA_shift`, `rs_shift`), and an evaluated morphism shifting by `γ` comes
from the weight-`γ` part of `C` (`mem_wP_of_shift`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

section PW

variable {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V} {M : Type} [AddCommGroup M]

theorem MeshWt.pw_comp (W : MeshWt Q M) {x y : V} (p : Quiver.Path x y) :
    ∀ {z : V} (q : Quiver.Path y z), W.pw (p.comp q) = W.pw p + W.pw q
  | _, Quiver.Path.nil => by simp [MeshWt.pw]
  | _, Quiver.Path.cons q a => by
      rw [Quiver.Path.comp_cons, MeshWt.pw, MeshWt.pw, W.pw_comp p q, add_assoc]

theorem MeshWt.pw_toPath (W : MeshWt Q M) {x y : V} (a : x ⟶ y) : W.pw a.toPath = W.w a := by
  simp [Quiver.Hom.toPath, MeshWt.pw]

/-- The path weight of a mesh weight, with values in `Multiplicative M`. -/
def MeshWt.toPW (W : MeshWt Q M) : PathWeight V (Multiplicative M) where
  deg p := Multiplicative.ofAdd (W.pw p)
  deg_nil _ := by simp [MeshWt.pw]
  deg_comp p q := by rw [W.pw_comp, ofAdd_add]

theorem MeshWt.toPW_deg (W : MeshWt Q M) {x y : V} (p : Quiver.Path x y) :
    W.toPW.deg p = Multiplicative.ofAdd (W.pw p) := rfl

variable [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- **Meshes are homogeneous** for a mesh weight. -/
theorem MeshWt.homog (W : MeshWt Q M) : MeshHomogeneous (Q := Q) W.toPW := by
  intro x a b
  rw [W.toPW_deg, W.toPW_deg, W.pw_comp, W.pw_comp, W.pw_toPath, W.pw_toPath, W.pw_toPath,
    W.pw_toPath, W.mesh x a, W.mesh x b]

end PW

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)

/-! ### Weight parts of the Hom spaces of `C` -/

variable (c) in
/-- The weight-`g` part of `C(x, y)`. -/
abbrev wP (g : M) (x y : V) : Submodule k (obj c x ⟶ obj c y) :=
  wPart c W.toPW (Multiplicative.ofAdd g) x y

variable (c) in
/-- The weight-`g` projection of `C(x, y)`. -/
abbrev wπ (g : M) (x y : V) : (obj c x ⟶ obj c y) →ₗ[k] (obj c x ⟶ obj c y) :=
  wProj c W.toPW W.homog (Multiplicative.ofAdd g) x y

theorem wπ_mem (g : M) {x y : V} (f : obj c x ⟶ obj c y) : wπ c W g x y f ∈ wP c W g x y :=
  wProj_mem W.homog _ f

theorem wπ_of_mem {g h : M} {x y : V} {f : obj c x ⟶ obj c y} (hf : f ∈ wP c W h x y) :
    wπ c W g x y f = if h = g then f else 0 := by
  rw [wProj_of_mem W.homog hf]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem comp_mem_wP {g h : M} {x y z : V} {f : obj c x ⟶ obj c y} {f' : obj c y ⟶ obj c z}
    (hf : f ∈ wP c W g x y) (hf' : f' ∈ wP c W h y z) : f ≫ f' ∈ wP c W (g + h) x z := by
  exact comp_mem_wPart hf hf'

theorem pathMor_mem_wP {x y : V} (p : Quiver.Path x y) : pathMor c p ∈ wP c W (W.pw p) x y :=
  pathMor_mem_wPart p

theorem arrowMor_mem_wP {x y : V} (a : x ⟶ y) : arrowMor c a ∈ wP c W (W.w a) x y := by
  rw [← pathMor_toPath, ← W.pw_toPath]; exact pathMor_mem_wP W _

/-- The weight and length projections commute. -/
theorem wπ_degProj (g : M) (d : ℕ) {x y : V} (f : obj c x ⟶ obj c y) :
    wπ c W g x y (degProj c d x y f) = degProj c d x y (wπ c W g x y f) := by
  obtain ⟨F, rfl⟩ := quotL_surjective c x y f
  change wπ c W g x y (degProj c d x y ((RelationCategory.functor k (meshRelations c)).map F)) =
    degProj c d x y (wπ c W g x y ((RelationCategory.functor k (meshRelations c)).map F))
  rw [degProj_apply, wProj_apply, wProj_apply, degProj_apply]
  congr 1
  show (Finsupp.filter _ (Finsupp.filter _ (LinearPaths.toFinsupp F)) : Quiver.Path x y →₀ k) =
    Finsupp.filter _ (Finsupp.filter _ (LinearPaths.toFinsupp F))
  ext p
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl

theorem wπ_mem_degreePart (g : M) {d : ℕ} {x y : V} {f : obj c x ⟶ obj c y}
    (hf : f ∈ degreePart c d x y) : wπ c W g x y f ∈ degreePart c d x y := by
  rw [← (degProj_of_mem c hf).trans (if_pos rfl), wπ_degProj]; exact degProj_mem c d _

variable (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

include hfin in
theorem finite_wP (x y : V) : Set.Finite {g : M | wP c W g x y ≠ ⊥} := by
  have := (iSupIndep_wPart (c := c) W.homog x y).fintypeNeBotOfFiniteDimensional
  have hfin' : Set.Finite {g : Multiplicative M | wPart c W.toPW g x y ≠ ⊥} :=
    @Finite.of_fintype _ this
  have := hfin'.preimage (f := Multiplicative.ofAdd) (Multiplicative.ofAdd.injective.injOn)
  exact this

/-- A finite set of weights containing all weights with nonzero parts. -/
def wSupp : Finset M :=
  Finset.univ.biUnion fun x : V ↦ Finset.univ.biUnion fun y : V ↦ (finite_wP W hfin x y).toFinset

theorem wP_eq_bot {g : M} (hg : g ∉ wSupp W hfin) (x y : V) : wP c W g x y = ⊥ := by
  by_contra h
  apply hg
  simp only [wSupp, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
  exact ⟨x, y, h⟩

theorem wπ_out {g : M} (hg : g ∉ wSupp W hfin) (x y : V) : wπ c W g x y = 0 := by
  ext f
  have := wπ_mem W g f
  rw [wP_eq_bot W hfin hg, Submodule.mem_bot] at this
  rw [this]; rfl

theorem eq_sum_wπ {x y : V} (f : obj c x ⟶ obj c y) : f = ∑ g ∈ wSupp W hfin, wπ c W g x y f := by
  set e := f - ∑ g ∈ wSupp W hfin, wπ c W g x y f
  have he : ∀ g : M, wπ c W g x y e = 0 := by
    intro g
    rw [map_sub, map_sum]
    simp only [wπ_of_mem W (wπ_mem W _ f)]
    rw [Finset.sum_ite_eq']
    split_ifs with hg
    · exact sub_self _
    · rw [wπ_out W hfin hg]; simp
  obtain ⟨s, hs⟩ := eq_sum_wProj W.homog e
  have : e = 0 := by
    rw [hs]; exact Finset.sum_eq_zero fun h _ ↦ he (Multiplicative.toAdd h)
  exact sub_eq_zero.1 this

include hfin in
/-- Composition with a homogeneous morphism on the left. -/
theorem wπ_comp_left {β : M} {x y z : V} {u : obj c x ⟶ obj c y} (hu : u ∈ wP c W β x y)
    (γ : M) (f : obj c y ⟶ obj c z) : wπ c W (β + γ) x z (u ≫ f) = u ≫ wπ c W γ y z f := by
  conv_lhs => rw [eq_sum_wπ W hfin f, Preadditive.comp_sum, map_sum]
  simp only [wπ_of_mem W (comp_mem_wP W hu (wπ_mem W _ f)), add_right_inj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [wπ_out W hfin h, LinearMap.zero_apply, Limits.comp_zero]

include hfin in
/-- Composition with a homogeneous morphism on the right. -/
theorem wπ_comp_right {β : M} {x y z : V} {u : obj c y ⟶ obj c z} (hu : u ∈ wP c W β y z)
    (γ : M) (f : obj c x ⟶ obj c y) : wπ c W (γ + β) x z (f ≫ u) = wπ c W γ x y f ≫ u := by
  conv_lhs => rw [eq_sum_wπ W hfin f, Preadditive.sum_comp, map_sum]
  simp only [wπ_of_mem W (comp_mem_wP W (wπ_mem W _ f) hu), add_left_inj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [wπ_out W hfin h, LinearMap.zero_apply, Limits.zero_comp]

/-! ### The grading of the evaluated modules -/

variable {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)

/-- The weight projection of an evaluated module. -/
def evProj (g : M) (X : V) : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X) :=
  LinearMap.pi fun y ↦ wπ c W g y.1 X ∘ₗ LinearMap.proj (R := k)
    (φ := fun y : D.PV ↦ D.F0 y ⟶ meshFam Q c X) y

theorem evProj_apply (g : M) (X : V) (m : Rep D.F0 (meshFam Q c X)) (y : D.PV) :
    evProj W D g X m y = wπ c W g y.1 X (m y) := rfl

/-- **The mesh-weight grading of `M_X`.** -/
def grEv (X : V) : MGr k M (Rep D.F0 (meshFam Q c X)) where
  proj g := evProj W D g X
  supp := wSupp W hfin
  proj_proj g h m := by
    funext y
    simp only [evProj_apply]
    rw [wπ_of_mem W (wπ_mem W h _)]
    split_ifs <;> rfl
  proj_out g hg := by
    ext m y
    simp only [evProj_apply, wπ_out W hfin hg, LinearMap.zero_apply]
    rfl
  sum m := by
    funext y
    rw [Rep.sum_apply]
    exact eq_sum_wπ W hfin (m y)

theorem grEv_isHom {g : M} {X : V} {m : Rep D.F0 (meshFam Q c X)} :
    (grEv W hfin D X).IsHom g m ↔ ∀ y, m y ∈ wP c W g y.1 X := by
  constructor
  · intro h y
    rw [← congrFun h y]
    exact wπ_mem W g _
  · intro h
    funext y
    change wπ c W g y.1 X (m y) = m y
    rw [wπ_of_mem W (h y), if_pos rfl]

/-! ### The grading of `A₀` -/

/-- The weight projection of `A₀`. -/
def a0Proj (g : M) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ where
  toFun a := MulOpposite.op (fun p q ↦ wπ c W g p.1 q.1 (a.unop p q))
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    exact map_add _ _ _
  map_smul' t a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    change wπ c W g p.1 q.1 (t • a.unop p q) = t • wπ c W g p.1 q.1 (a.unop p q)
    exact map_smul _ _ _

theorem a0Proj_apply (g : M) (a : (Alg D.F0)ᵐᵒᵖ) (p q : D.PV) :
    (a0Proj W D g a).unop p q = wπ c W g p.1 q.1 (a.unop p q) := rfl

/-- **The mesh-weight grading of `A₀`** as a module grading. -/
def grA0 : MGr k M (Alg D.F0)ᵐᵒᵖ where
  proj := a0Proj W D
  supp := wSupp W hfin
  proj_proj g h a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [a0Proj_apply, a0Proj_apply, wπ_of_mem W (wπ_mem W h _)]
    split_ifs <;> rfl
  proj_out g hg := by
    ext a
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [a0Proj_apply, wπ_out W hfin hg]
    rfl
  sum a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [Finset.unop_sum, CatAlg.sum_apply]
    exact eq_sum_wπ W hfin _

theorem grA0_isHom {g : M} {a : (Alg D.F0)ᵐᵒᵖ} :
    (grA0 W hfin D).IsHom g a ↔ ∀ p q, a.unop p q ∈ wP c W g p.1 q.1 := by
  constructor
  · intro h p q
    rw [← h]
    exact wπ_mem W g _
  · intro h
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    change wπ c W g p.1 q.1 (a.unop p q) = a.unop p q
    rw [wπ_of_mem W (h p q), if_pos rfl]

theorem grA0_mul {g h : M} {a b : (Alg D.F0)ᵐᵒᵖ} (ha : (grA0 W hfin D).IsHom g a)
    (hb : (grA0 W hfin D).IsHom h b) : (grA0 W hfin D).IsHom (g + h) (a * b) := by
  rw [grA0_isHom] at ha hb ⊢
  intro p q
  rw [MulOpposite.unop_mul, mul_apply]
  refine Submodule.sum_mem _ fun r _ ↦ ?_
  rw [add_comm]
  exact comp_mem_wP W (hb p r) (ha r q)

/-- **The mesh-weight grading of `A₀`** as an algebra grading. -/
def latA0 : LatGrading k (Alg D.F0)ᵐᵒᵖ M where
  proj := a0Proj W D
  supp := wSupp W hfin
  proj_proj := (grA0 W hfin D).proj_proj
  proj_out := (grA0 W hfin D).proj_out
  sum := (grA0 W hfin D).sum
  mul_hom g h a b := grA0_mul W hfin D ((grA0 W hfin D).isHom_proj g a)
    ((grA0 W hfin D).isHom_proj h b)

theorem latA0_isHom {g : M} {a : (Alg D.F0)ᵐᵒᵖ} :
    (latA0 W hfin D).IsHom g a ↔ (grA0 W hfin D).IsHom g a := Iff.rfl

/-! ### Shifting maps -/

/-- The action of a homogeneous element of `A₀` shifts weights. -/
theorem act_shift {α : M} {a : (Alg D.F0)ᵐᵒᵖ} (ha : (grA0 W hfin D).IsHom α a) (X : V) :
    MGr.Shift (grEv W hfin D X) (grEv W hfin D X) α ((evAct D X).flip a) := by
  intro β m hm
  rw [grEv_isHom] at hm ⊢
  rw [grA0_isHom] at ha
  intro y
  change (a.unop • m) y ∈ _
  rw [Rep.smul_apply]
  refine Submodule.sum_mem _ fun z _ ↦ ?_
  rw [add_comm]
  exact comp_mem_wP W (ha y z) (hm z)

/-- An evaluated homogeneous morphism shifts weights. -/
theorem rs_shift {γ : M} {X Y : V} {f : obj c X ⟶ obj c Y} (hf : f ∈ wP c W γ X Y) :
    MGr.Shift (grEv W hfin D X) (grEv W hfin D Y) γ (rs D f) := by
  intro β m hm
  rw [grEv_isHom] at hm ⊢
  intro y
  exact comp_mem_wP W (hm y) hf

theorem fA_shift {X Y : V} (a : X ⟶ Y) :
    MGr.Shift (grEv W hfin D X) (grEv W hfin D Y) (W.w a) (fA D a) :=
  rs_shift W hfin D (arrowMor_mem_wP W a)

/-- The weight part of an evaluated morphism. -/
theorem pr_rs (γ : M) {X Y : V} (f : obj c X ⟶ obj c Y) :
    MGr.pr (grEv W hfin D X) (grEv W hfin D Y) γ (rs D f) = rs D (wπ c W γ X Y f) := by
  refine (grEv W hfin D X).ext_of_hom fun β m hm ↦ ?_
  rw [MGr.pr_apply_hom _ _ hm]
  funext y
  change wπ c W (β + γ) y.1 Y (m y ≫ f) = m y ≫ wπ c W γ X Y f
  exact wπ_comp_left W hfin ((grEv_isHom W hfin D).1 hm y) γ f

variable [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- **An evaluated morphism shifting by `γ` comes from the weight-`γ` part.** -/
theorem mem_wP_of_shift {γ : M} {X Y : V} {f : obj c X ⟶ obj c Y}
    (h : MGr.Shift (grEv W hfin D X) (grEv W hfin D Y) γ (rs D f)) : f ∈ wP c W γ X Y := by
  have h1 := pr_rs W hfin D γ f
  rw [MGr.pr_of_shift h] at h1
  have : f - wπ c W γ X Y f = 0 := D.repMap_eq_zero X Y _ fun m ↦ by
    have := LinearMap.congr_fun h1 m
    simp only [LinearMap.coe_restrictScalars] at this
    rw [show repMap (F := D.F0) (f - wπ c W γ X Y f) m =
      repMap (F := D.F0) f m - repMap (F := D.F0) (wπ c W γ X Y f) m from by
        ext y; simp [Preadditive.comp_sub]]
    rw [this, sub_self]
  rw [sub_eq_zero] at this
  rw [this]
  exact wπ_mem W γ f

/-! ### Compatibility with the length grading -/

theorem evProj_zgr {g : M} {X : V} {p : ℤ} {m : Rep D.F0 (meshFam Q c X)}
    (hm : (zgrEv D hfin X).IsHom p m) : (zgrEv D hfin X).IsHom p (evProj W D g X m) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [(zgrEv_isHom_neg D hfin X hp m).1 hm, map_zero]
    exact GExt.ZGr.isHom_zero _ _
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [zgrEv_isHom] at hm ⊢
  intro y
  exact wπ_mem_degreePart W g (hm y)

theorem a0Proj_zgr {g : M} {p : ℤ} {a : (Alg D.F0)ᵐᵒᵖ} (ha : (galgA0 D hfin).gr.IsHom p a) :
    (galgA0 D hfin).gr.IsHom p (a0Proj W D g a) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [(galgA0_isHom_neg D hfin hp a).1 ha, map_zero]
    exact GExt.ZGr.isHom_zero _ _
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [galgA0_isHom] at ha ⊢
  intro y z
  exact wπ_mem_degreePart W g (ha y z)

end MeshWalk

end MultiplicativeBasisDeformations
