import MultiplicativeBasisDeformations.Foundations.NormalFormAlgebra
import MultiplicativeBasisDeformations.Foundations.OrbitDim
import MultiplicativeBasisDeformations.Foundations.RepFinite

/-!
# Lemma 8.8 for bound quiver algebras

`lem:dimension-infinity` (`local-ray-geometry.tex`): "Let `kQ/(ρ_1, …, ρ_t)` be a
finite-dimensional bound quiver algebra, with each relation between radical paths with specified
endpoints. For a nonzero dimension vector `d`, put `D = Σ_v d_v²`, `N = Σ_{a : v → w} d_v d_w`,
`F = Σ_i d_{source(ρ_i)} d_{target(ρ_i)}`. If `N − F ≥ D`, the algebra is representation-infinite."

The algebra `kQ/(ρ)` is the category algebra of the relation category `kQ/(ρ)` (path-order
product). A point `x` of the representation space (matrices on the arrows) gives the arrow maps
of a representation; the relations evaluate to the matrices `relMat x i`, whose entries are
`F` polynomials in the coordinates (`relP`), vanishing at `0` (the relations have no
length-zero part) and stable under `∏ GL_{d v}` (`relMat_act`). A point of their zero set gives a
functor `kQ/(ρ) → Mod k` (`Φ`), hence a right module of dimension `Σ d_v` (`repObj`), and
isomorphic modules come from conjugate points (`conj_of_iso`). Finite representation type would
give finitely many orbits, contradicting `OrbitDim.orbits_not_finite`
(`not_isRepresentationFinite_bound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

namespace BoundQuiver

universe u

open GeneralNormalForm OrbitDim MvPolynomial

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)] (d : V → ℕ)

variable (V) in
/-- The arrows. -/
abbrev Arr := Σ (u v : V), u ⟶ v

/-- The source of an arrow. -/
abbrev src (a : Arr V) : V := a.1

/-- The target of an arrow. -/
abbrev tgt (a : Arr V) : V := a.2.1

variable (k) in
/-- The points of the representation space. -/
abbrev Pt := Coord d (src (V := V)) tgt → k

/-! ### Path matrices -/

/-- The matrix of a path at a point (path order: `M_{p a} = M_a M_p`). -/
def pathMat (x : Pt k d) : ∀ {u v : V}, Quiver.Path u v → Matrix (Fin (d v)) (Fin (d u)) k
  | _, _, .nil => 1
  | _, _, .cons p e => mat x ⟨_, _, e⟩ * pathMat x p

theorem pathMat_nil (x : Pt k d) (u : V) : pathMat d x (Quiver.Path.nil : Quiver.Path u u) = 1 := by
  simp only [pathMat]

theorem pathMat_cons (x : Pt k d) {u v w : V} (p : Quiver.Path u v) (e : v ⟶ w) :
    pathMat d x (p.cons e) = mat x ⟨_, _, e⟩ * pathMat d x p := by
  simp only [pathMat]

variable (k) in
/-- The generic matrix of an arrow. -/
def matP (a : Arr V) :
    Matrix (Fin (d (tgt a))) (Fin (d (src a))) (MvPolynomial (Coord d (src (V := V)) tgt) k) :=
  Matrix.of fun i j ↦ X ⟨a, i, j⟩

variable (k) in
/-- The polynomial matrix of a path. -/
def pathMatP : ∀ {u v : V}, Quiver.Path u v →
    Matrix (Fin (d v)) (Fin (d u)) (MvPolynomial (Coord d (src (V := V)) tgt) k)
  | _, _, .nil => 1
  | _, _, .cons p e => matP k d ⟨_, _, e⟩ * pathMatP p

theorem map_pathMatP (x : Pt k d) {u v : V} (p : Quiver.Path u v) :
    (pathMatP (k := k) d p).map (eval x) = pathMat d x p := by
  induction p with
  | nil => simp [pathMatP, pathMat]
  | cons p e ih =>
      simp only [pathMatP, pathMat]
      rw [Matrix.map_mul, ih]
      congr 1
      ext i j
      simp [mat, matP]

theorem pathMat_act (g : ∀ v, GL (Fin (d v)) k) (x : Pt k d) {u v : V} (p : Quiver.Path u v) :
    pathMat d (act g x) p = (g v).val * pathMat d x p * ((g u)⁻¹).val := by
  induction p with
  | nil =>
      rw [pathMat_nil, pathMat_nil, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  | cons p e ih =>
      rw [pathMat_cons, pathMat_cons, ih, mat_act]
      simp only [Matrix.mul_assoc]
      congr 2
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem pathMat_zero {u v : V} (p : Quiver.Path u v) (hp : p.length ≠ 0) :
    pathMat (k := k) d 0 p = 0 := by
  cases p with
  | nil => exact absurd rfl hp
  | cons p e =>
      rw [pathMat_cons]
      have : mat (0 : Pt k d) ⟨_, _, e⟩ = 0 := by ext i j; rfl
      rw [this, Matrix.zero_mul]

/-! ### The relations -/

section Relations

variable {ι : Type} [Fintype ι] (s t : ι → V)
  (r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i))

/-- The matrix of a relation at a point. -/
def relMat (x : Pt k d) (i : ι) : Matrix (Fin (d (t i))) (Fin (d (s i))) k :=
  (LinearPaths.toFinsupp (r i)).sum fun p c ↦ c • pathMat d x p

/-- The polynomial matrix of a relation. -/
def relP (i : ι) : Matrix (Fin (d (t i))) (Fin (d (s i))) (MvPolynomial (Coord d (src (V := V)) tgt) k) :=
  (LinearPaths.toFinsupp (r i)).sum fun p c ↦ c • pathMatP k d p

theorem eval_relP (x : Pt k d) (i : ι) (a : Fin (d (t i))) (b : Fin (d (s i))) :
    eval x (relP d s t r i a b) = relMat d s t r x i a b := by
  simp only [relP, relMat, Finsupp.sum, Matrix.sum_apply, map_sum, Matrix.smul_apply,
    smul_eval, ← map_pathMatP d x, Matrix.map_apply, smul_eq_mul]

theorem relMat_act (g : ∀ v, GL (Fin (d v)) k) (x : Pt k d) (i : ι) :
    relMat d s t r (act g x) i = (g (t i)).val * relMat d s t r x i * ((g (s i))⁻¹).val := by
  simp only [relMat, Finsupp.sum, pathMat_act, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]

theorem relMat_zero (hrad : ∀ i, LinearPaths.proj (k := k) 0 (s i) (t i) (r i) = 0) (i : ι) :
    relMat d s t r 0 i = 0 := by
  classical
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hlen : p.length ≠ 0 := by
    intro h0
    have := congrArg (fun F ↦ LinearPaths.toFinsupp F p) (hrad i)
    change (Finsupp.filter (fun q : Quiver.Path (s i) (t i) ↦ q.length = 0)
      (LinearPaths.toFinsupp (r i))) p = 0 at this
    rw [Finsupp.filter_apply, if_pos h0] at this
    exact (Finsupp.mem_support_iff.1 hp) this
  show _ • pathMat d 0 p = 0
  rw [pathMat_zero d p hlen, smul_zero]

/-! ### Realization in `Mod k` -/

variable (k) in
/-- The space `k^{d v}`. -/
abbrev Sp (v : V) : ModuleCat.{u} k := ModuleCat.of k (Fin (d v) → k)

/-- The arrow maps of a point. -/
def Lx (x : Pt k d) {u v : V} (e : u ⟶ v) : Sp k d u ⟶ Sp k d v :=
  ModuleCat.ofHom (Matrix.toLin' (mat x ⟨u, v, e⟩))

theorem pathMap_Lx (x : Pt k d) {u v : V} (p : Quiver.Path u v) :
    pathMap (O := Sp k d) (Lx d x) p = ModuleCat.ofHom (Matrix.toLin' (pathMat d x p)) := by
  induction p with
  | nil =>
      rw [pathMap_nil, pathMat_nil, Matrix.toLin'_one]; rfl
  | cons p e ih =>
      rw [pathMap_cons, ih, pathMat_cons, Matrix.toLin'_mul]; rfl

theorem realize_Lx (x : Pt k d) {u v : V}
    (P : LinearPaths.obj (k := k) u ⟶ LinearPaths.obj (k := k) v) :
    realize (O := Sp k d) (Lx d x) u v P =
      ModuleCat.ofHom (Matrix.toLin' ((LinearPaths.toFinsupp P).sum fun p c ↦ c • pathMat d x p)) := by
  change Finsupp.linearCombination k (pathMap (Lx d x)) (LinearPaths.toFinsupp P) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, pathMap_Lx, map_sum, map_smul]
  ext w
  simp [ModuleCat.ofHom, ModuleCat.hom_sum, ModuleCat.hom_smul]

end Relations

/-! ### The functor and the module of a point -/

section Module

open CatAlg

variable {ι : Type} [Fintype ι] {s t : ι → V}
  {r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i)}
  (x : Pt k d) (hx : ∀ i, relMat d s t r x i = 0)

include hx in
theorem realize_eq_zero_of_mem {u v : V} {G : LinearPaths.obj (k := k) u ⟶ LinearPaths.obj v}
    (hG : G ∈ (CategoricalIdeal.HomIdeal.linearSpan k (Rel s t r)).hom _ _) :
    realize (O := Sp k d) (Lx d x) u v G = 0 := by
  change G ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule k _ _ _ at hG
  induction hG using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨X, Y, rr, hrr, a, a', rfl⟩ := hg
      obtain ⟨i, hX, hY, rfl⟩ := hrr
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [realize_comp, realize_comp]
      have h0 : realize (O := Sp k d) (Lx d x) (s i) (t i) (r i) = 0 := by
        rw [realize_Lx]
        change ModuleCat.ofHom (Matrix.toLin' (relMat d s t r x i)) = 0
        rw [hx i, map_zero]; rfl
      rw [h0, Limits.zero_comp, Limits.comp_zero]
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, ha, hc, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **The functor `kQ/(ρ) → Mod k` of a point of the zero set.** -/
def Φ : RelationCategory k (Rel s t r) ⥤ ModuleCat.{u} k :=
  CategoryTheory.Quotient.lift _ (pathFunctor (O := Sp k d) (Lx d x)) fun _ _ f₁ f₂ h ↦ by
    have h0 := realize_eq_zero_of_mem d x hx h
    rw [map_sub, sub_eq_zero] at h0
    exact h0

theorem Φ_map_cl {u v : V} (P : LinearPaths.obj (k := k) u ⟶ LinearPaths.obj v) :
    (Φ d x hx).map ((cl s t r).map P) = realize (O := Sp k d) (Lx d x) u v P := rfl

theorem Φ_map_add {u v : V} (c c' : clObj s t r u ⟶ clObj s t r v) :
    (Φ d x hx).map (c + c') = (Φ d x hx).map c + (Φ d x hx).map c' := by
  obtain ⟨P, rfl⟩ := (cl s t r).map_surjective (X := LinearPaths.obj u) (Y := LinearPaths.obj v) c
  obtain ⟨P', rfl⟩ := (cl s t r).map_surjective (X := LinearPaths.obj u) (Y := LinearPaths.obj v) c'
  rw [← Functor.map_add, Φ_map_cl, Φ_map_cl, Φ_map_cl, map_add]
  rfl

theorem Φ_map_smul {u v : V} (a : k) (c : clObj s t r u ⟶ clObj s t r v) :
    (Φ d x hx).map (a • c) = a • (Φ d x hx).map c := by
  obtain ⟨P, rfl⟩ := (cl s t r).map_surjective (X := LinearPaths.obj u) (Y := LinearPaths.obj v) c
  rw [← Functor.map_smul, Φ_map_cl, Φ_map_cl, map_smul]
  rfl

theorem Φ_map_zero {u v : V} : (Φ d x hx).map (0 : clObj s t r u ⟶ clObj s t r v) = 0 := by
  have := Φ_map_smul d x hx (0 : k) (0 : clObj s t r u ⟶ clObj s t r v)
  rwa [zero_smul, zero_smul] at this

theorem Φ_map_sum {u v : V} {κ : Type*} (F : Finset κ) (c : κ → (clObj s t r u ⟶ clObj s t r v)) :
    (Φ d x hx).map (∑ j ∈ F, c j) = ∑ j ∈ F, (Φ d x hx).map (c j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [Φ_map_zero]
  | insert j F hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Φ_map_add, ih]

/-- The linear map of a morphism of `kQ/(ρ)`. -/
def Φl {u v : V} (c : clObj s t r u ⟶ clObj s t r v) : (Fin (d u) → k) →ₗ[k] (Fin (d v) → k) :=
  ((Φ d x hx).map c).hom

theorem Φl_add {u v : V} (c c' : clObj s t r u ⟶ clObj s t r v) :
    Φl d x hx (c + c') = Φl d x hx c + Φl d x hx c' := by
  simp only [Φl, Φ_map_add]; rfl

theorem Φl_smul {u v : V} (a : k) (c : clObj s t r u ⟶ clObj s t r v) :
    Φl d x hx (a • c) = a • Φl d x hx c := by
  simp only [Φl, Φ_map_smul]; rfl

theorem Φl_zero {u v : V} : Φl d x hx (0 : clObj s t r u ⟶ clObj s t r v) = 0 := by
  simp only [Φl, Φ_map_zero]; rfl

theorem Φl_sum {u v : V} {κ : Type*} (F : Finset κ) (c : κ → (clObj s t r u ⟶ clObj s t r v)) :
    Φl d x hx (∑ j ∈ F, c j) = ∑ j ∈ F, Φl d x hx (c j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [Φl_zero]
  | insert j F hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Φl_add, ih]

theorem Φl_comp {u v w : V} (c : clObj s t r u ⟶ clObj s t r v) (c' : clObj s t r v ⟶ clObj s t r w) :
    Φl d x hx (c ≫ c') = Φl d x hx c' ∘ₗ Φl d x hx c := by
  simp only [Φl, Functor.map_comp]; rfl

theorem Φl_id (u : V) : Φl d x hx (𝟙 (clObj s t r u)) = LinearMap.id := by
  rw [show 𝟙 (clObj s t r u) = (cl s t r).map (𝟙 _) from ((cl s t r).map_id _).symm]
  unfold Φl
  rw [Φ_map_cl, realize_id]
  rfl

theorem Φl_idTo_ne {u v : V} (h : u ≠ v) : Φl d x hx (idTo (F := clObj s t r) u v) = 0 := by
  rw [idTo_ne h, Φl_zero]

/-- The action of the bound quiver algebra on `⊕_v k^{d v}`. -/
def act (a : Alg (clObj s t r)) (w : ∀ v, Fin (d v) → k) : ∀ v, Fin (d v) → k :=
  fun y ↦ ∑ u : V, Φl d x hx (a u y) (w u)

theorem act_mul (a b : Alg (clObj s t r)) (w : ∀ v, Fin (d v) → k) :
    act d x hx (b * a) w = act d x hx a (act d x hx b w) := by
  funext z
  simp only [act, CatAlg.mul_apply, Φl_sum, LinearMap.sum_apply, Φl_comp, LinearMap.comp_apply,
    map_sum]
  exact Finset.sum_comm

theorem act_one (w : ∀ v, Fin (d v) → k) : act d x hx 1 w = w := by
  funext y
  simp only [act, CatAlg.one_apply]
  rw [Finset.sum_eq_single y]
  · rw [idTo_self, Φl_id, LinearMap.id_apply]
  · intro u _ hu; rw [Φl_idTo_ne d x hx hu, LinearMap.zero_apply]
  · simp

theorem act_algebraMap (c : k) (w : ∀ v, Fin (d v) → k) :
    act d x hx (algebraMap k (Alg (clObj s t r)) c) w = c • w := by
  funext y
  simp only [act, Algebra.algebraMap_eq_smul_one, CatAlg.smul_apply, CatAlg.one_apply, Φl_smul,
    LinearMap.smul_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single y]
  · rw [idTo_self, Φl_id, LinearMap.id_apply]
  · intro u _ hu; rw [Φl_idTo_ne d x hx hu, LinearMap.zero_apply, smul_zero]
  · simp

/-- The carrier. -/
abbrev Car (_x : Pt k d) : Type u := ∀ v, Fin (d v) → k

/-- The right module structure. -/
def repModule : Module (Alg (clObj s t r))ᵐᵒᵖ (Car d x) where
  smul a w := act d x hx a.unop w
  one_smul w := act_one d x hx w
  mul_smul a b w := act_mul d x hx a.unop b.unop w
  smul_zero a := by
    change act d x hx a.unop 0 = 0
    funext y; simp [act]
  smul_add a v w := by
    change act d x hx a.unop (v + w) = act d x hx a.unop v + act d x hx a.unop w
    funext y
    simp only [act, Pi.add_apply, ← Finset.sum_add_distrib, map_add]
  add_smul a b w := by
    change act d x hx (a + b).unop w = act d x hx a.unop w + act d x hx b.unop w
    funext y
    change ∑ u, Φl d x hx (a.unop u y + b.unop u y) (w u) =
      ∑ u, Φl d x hx (a.unop u y) (w u) + ∑ u, Φl d x hx (b.unop u y) (w u)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    erw [Φl_add]; rfl
  zero_smul w := by
    change act d x hx (0 : (Alg (clObj s t r))ᵐᵒᵖ).unop w = 0
    funext y; simp [act, CatAlg.zero_apply, Φl_zero]

/-- **The module of a point.** -/
def repObj : RightModuleCat (Alg (clObj s t r)) :=
  @ModuleCat.of _ _ (Car d x) _ (repModule d x hx)

/-- The identification with `∏ k^{d v}` is `k`-linear. -/
def toPi : repObj d x hx →ₗ[k] (∀ v, Fin (d v) → k) where
  toFun w := w
  map_add' _ _ := rfl
  map_smul' c w := act_algebraMap d x hx c w

theorem repObj_finite : Module.Finite k (repObj d x hx) :=
  Module.Finite.of_injective (toPi d x hx) fun _ _ h ↦ h

theorem finrank_repObj_le : Module.finrank k (repObj d x hx) ≤ ∑ v, d v := by
  have := LinearMap.finrank_le_finrank_of_injective (f := toPi d x hx) fun _ _ h ↦ h
  refine this.trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype]
  simp

end Module

/-! ### Isomorphisms are conjugations -/

section Iso

open CatAlg

variable {ι : Type} [Fintype ι] {s t : ι → V}
  {r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i)}

theorem act_sgl (x : Pt k d) (hx : ∀ i, relMat d s t r x i = 0) (p q : V)
    (c : clObj s t r p ⟶ clObj s t r q) (w : ∀ v, Fin (d v) → k) :
    act d x hx (sgl p q c) w = Pi.single q (Φl d x hx c (w p)) := by
  funext z
  simp only [act, sgl, Φl_comp, LinearMap.comp_apply]
  by_cases hz : z = q
  · subst hz
    rw [Pi.single_eq_same, Finset.sum_eq_single p]
    · rw [idTo_self, idTo_self, Φl_id, Φl_id, LinearMap.id_apply, LinearMap.id_apply]
    · intro u _ hu; rw [Φl_idTo_ne d x hx hu, LinearMap.zero_apply, map_zero, map_zero]
    · simp
  · rw [Pi.single_eq_of_ne hz]
    exact Finset.sum_eq_zero fun u _ ↦ by
      rw [Φl_idTo_ne d x hx (Ne.symm hz), LinearMap.zero_apply]

theorem Φl_arrow (x : Pt k d) (hx : ∀ i, relMat d s t r x i = 0) {p q : V} (e : p ⟶ q) :
    Φl d x hx ((cl s t r).map (LinearPaths.arrow e)) = Matrix.toLin' (mat x ⟨p, q, e⟩) := by
  unfold Φl
  rw [Φ_map_cl, LinearPaths.arrow, realize_path, pathMap_Lx]
  change Matrix.toLin' (pathMat d x e.toPath) = _
  rw [Quiver.Hom.toPath, pathMat_cons, pathMat_nil, Matrix.mul_one]

variable {x y : Pt k d} {hx : ∀ i, relMat d s t r x i = 0} {hy : ∀ i, relMat d s t r y i = 0}
  (f : (∀ v, Fin (d v) → k) → (∀ v, Fin (d v) → k))
  (hf : ∀ a w, f (act d x hx a w) = act d y hy a (f w))
  (hfa : ∀ w w', f (w + w') = f w + f w')

/-- The component maps of an isomorphism. -/
def comp (v : V) (w : Fin (d v) → k) : Fin (d v) → k := f (Pi.single v w) v

include hf in
theorem f_single (v : V) (w : Fin (d v) → k) :
    f (Pi.single v w) = Pi.single v (comp d f v w) := by
  have h1 := hf (sgl v v (𝟙 _)) (Pi.single v w)
  rw [act_sgl, act_sgl, Φl_id, Φl_id, LinearMap.id_apply, LinearMap.id_apply,
    Pi.single_eq_same] at h1
  rw [h1]; rfl

include hf in
theorem f_smul (c : k) (w : ∀ v, Fin (d v) → k) : f (c • w) = c • f w := by
  have := hf (algebraMap k _ c) w
  rwa [act_algebraMap, act_algebraMap] at this

include hf in
/-- The component maps as linear maps. -/
def compL (v : V) : (Fin (d v) → k) →ₗ[k] (Fin (d v) → k) where
  toFun := comp d f v
  map_add' u u' := by simp only [comp, Pi.single_add, hfa, Pi.add_apply]
  map_smul' c u := by
    simp only [comp, RingHom.id_apply]
    have hs : (Pi.single v (c • u) : ∀ v, Fin (d v) → k) = c • Pi.single v u := by
      funext v' i
      by_cases h : v' = v
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hs, f_smul d f hf]
    rfl

include hf in
/-- **The arrow relation** `g_q M_e = M'_e g_p`. -/
theorem comp_arrow {p q : V} (e : p ⟶ q) (u : Fin (d p) → k) :
    compL d f hf hfa q (Matrix.toLin' (mat x ⟨p, q, e⟩) u) =
      Matrix.toLin' (mat y ⟨p, q, e⟩) (compL d f hf hfa p u) := by
  have h1 := hf (sgl p q ((cl s t r).map (LinearPaths.arrow e))) (Pi.single p u)
  simp only [act_sgl, Pi.single_eq_same, Φl_arrow, f_single d f hf] at h1
  exact Pi.single_injective q h1

variable (g : (∀ v, Fin (d v) → k) → (∀ v, Fin (d v) → k))
  (hg : ∀ a w, g (act d y hy a w) = act d x hx a (g w))
  (hga : ∀ w w', g (w + w') = g w + g w') (hgf : ∀ w, g (f w) = w)

include hf hg hgf in
theorem comp_left_inv (v : V) (u : Fin (d v) → k) :
    compL d g hg hga v (compL d f hf hfa v u) = u := by
  change g (Pi.single v (comp d f v u)) v = u
  rw [← f_single d f hf, hgf, Pi.single_eq_same]

end Iso

section Points

open CatAlg

variable {ι : Type} [Fintype ι] {s t : ι → V}
  {r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i)}

/-- **Isomorphic modules are conjugate points.** -/
theorem conj_of_iso (x y : Pt k d) (hx : ∀ i, relMat d s t r x i = 0)
    (hy : ∀ i, relMat d s t r y i = 0)
    (L : repObj d x hx ≃ₗ[(Alg (clObj s t r))ᵐᵒᵖ] repObj d y hy) :
    ∃ g : ∀ v, GL (Fin (d v)) k, y = OrbitDim.act g x := by
  set f : (∀ v, Fin (d v) → k) → (∀ v, Fin (d v) → k) := fun w ↦ L w
  set g : (∀ v, Fin (d v) → k) → (∀ v, Fin (d v) → k) := fun w ↦ L.symm w
  have hf : ∀ a w, f (act d x hx a w) = act d y hy a (f w) :=
    fun a w ↦ L.map_smul (MulOpposite.op a) w
  have hfa : ∀ w w', f (w + w') = f w + f w' := fun w w' ↦ L.map_add w w'
  have hg : ∀ a w, g (act d y hy a w) = act d x hx a (g w) :=
    fun a w ↦ L.symm.map_smul (MulOpposite.op a) w
  have hga : ∀ w w', g (w + w') = g w + g w' := fun w w' ↦ L.symm.map_add w w'
  have hgf : ∀ w, g (f w) = w := fun w ↦ L.symm_apply_apply w
  have hfg : ∀ w, f (g w) = w := fun w ↦ L.apply_symm_apply w
  set gL := compL d f hf hfa
  set hL := compL d g hg hga
  have h1 : ∀ v u, hL v (gL v u) = u := comp_left_inv d f hf hfa g hg hga hgf
  have h2 : ∀ v u, gL v (hL v u) = u := comp_left_inv d g hg hga f hf hfa hfg
  let G : ∀ v, GL (Fin (d v)) k := fun v ↦
    ⟨LinearMap.toMatrix' (gL v), LinearMap.toMatrix' (hL v), by
      rw [← LinearMap.toMatrix'_comp,
        show gL v ∘ₗ hL v = LinearMap.id from LinearMap.ext fun u ↦ h2 v u,
        LinearMap.toMatrix'_id], by
      rw [← LinearMap.toMatrix'_comp,
        show hL v ∘ₗ gL v = LinearMap.id from LinearMap.ext fun u ↦ h1 v u,
        LinearMap.toMatrix'_id]⟩
  refine ⟨G, ?_⟩
  funext co
  obtain ⟨⟨p, q, e⟩, i, j⟩ := co
  have harr := comp_arrow d f hf hfa e
  have hMy : Matrix.toLin' (mat y ⟨p, q, e⟩) = gL q ∘ₗ Matrix.toLin' (mat x ⟨p, q, e⟩) ∘ₗ hL p := by
    refine LinearMap.ext fun u ↦ ?_
    simp only [LinearMap.comp_apply]
    rw [harr, h2]
  have hmat : mat y ⟨p, q, e⟩ =
      LinearMap.toMatrix' (gL q) * mat x ⟨p, q, e⟩ * LinearMap.toMatrix' (hL p) := by
    have := congrArg LinearMap.toMatrix' hMy
    simp only [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp] at this
    rw [this, Matrix.mul_assoc]
  change y ⟨⟨p, q, e⟩, i, j⟩ = (LinearMap.toMatrix' (gL q) * mat x ⟨p, q, e⟩ *
    LinearMap.toMatrix' (hL p)) i j
  rw [← hmat]; rfl

end Points

/-! ### Lemma 8.8 -/

section Main

open CatAlg

variable {ι : Type} [Fintype ι] (s t : ι → V)
  (r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i))

/-- The labelled biproducts. -/
def Obj {N : ℕ} (X : Fin N → RightModuleCat (Alg (clObj s t r))) (B : ℕ)
    (τ : Σ m : Fin (B + 1), (Fin m → Fin N)) : RightModuleCat (Alg (clObj s t r)) :=
  ⨁ fun j : Fin τ.1 ↦ X (τ.2 j)

/-- **Lemma 8.8** (`lem:dimension-infinity`): let `kQ/(ρ₁, …, ρ_t)` be a finite-dimensional
bound quiver algebra (the category algebra of the relation category, path-order product), each
relation `ρ_i : s_i → t_i` a combination of paths of positive length. For a nonzero dimension
vector `d` with `N − F ≥ D`, i.e. `Σ_v d_v² + Σ_i d_{s_i} d_{t_i} ≤ Σ_{a : v → w} d_v d_w`, the
algebra is representation-infinite. -/
theorem not_isRepresentationFinite_bound [IsAlgClosed k] [FiniteDimensional k (Alg (clObj s t r))]
    (hrad : ∀ i, LinearPaths.proj (k := k) 0 (s i) (t i) (r i) = 0) (hd : ∃ v, 0 < d v)
    (hNF : ∑ v, d v ^ 2 + ∑ i, d (s i) * d (t i) ≤ ∑ a : Arr V, d (src a) * d (tgt a)) :
    ¬ IsRepresentationFinite k (Alg (clObj s t r)) := by
  classical
  intro hA
  obtain ⟨N, X, -, hX⟩ := exists_labels_iso hA
  -- the relation polynomials
  set Ix := Σ i : ι, Fin (d (t i)) × Fin (d (s i))
  set eI := Fintype.equivFin Ix
  let f : Fin (Fintype.card Ix) → MvPolynomial (Coord d (src (V := V)) tgt) k := fun n ↦
    relP d s t r (eI.symm n).1 (eI.symm n).2.1 (eI.symm n).2.2
  have hzero : ∀ y : Pt k d, (∀ n, eval y (f n) = 0) ↔ ∀ i, relMat d s t r y i = 0 := by
    intro y
    constructor
    · intro h i
      ext a b
      have := h (eI ⟨i, a, b⟩)
      change eval y (relP d s t r (eI.symm (eI ⟨i, a, b⟩)).1 (eI.symm (eI ⟨i, a, b⟩)).2.1
        (eI.symm (eI ⟨i, a, b⟩)).2.2) = 0 at this
      rw [Equiv.symm_apply_apply, eval_relP] at this
      exact this
    · intro h n
      simp only [f, eval_relP, h, Matrix.zero_apply]
  -- the modules of the points of the zero set
  set Z := {y : Pt k d // ∀ i, relMat d s t r y i = 0}
  set B := ∑ v, d v
  choose n l hn hiso using fun y : Z ↦ hX _ (repObj_finite d y.1 y.2)
  have hnB : ∀ y, n y < B + 1 := fun y ↦
    Nat.lt_succ_of_le ((hn y).trans (finrank_repObj_le d y.1 y.2))
  let lab : Z → Σ m : Fin (B + 1), (Fin m → Fin N) := fun y ↦ ⟨⟨n y, hnB y⟩, l y⟩
  have hM : ∀ y : Z, Nonempty (repObj d y.1 y.2 ≅ Obj s t r X B (lab y)) := fun y ↦ hiso y
  let rep : (Σ m : Fin (B + 1), (Fin m → Fin N)) → Pt k d :=
    fun τ ↦ if h : ∃ y, lab y = τ then (Classical.choose h).1 else 0
  refine OrbitDim.orbits_not_finite (k := k) _ f (fun n ↦ ?_) (fun g y hy n ↦ ?_) hd ?_
    (Finset.univ.image rep) fun y hy ↦ ?_
  · simp only [f, eval_relP, relMat_zero d s t r hrad, Matrix.zero_apply]
  · have hy' := (hzero y).1 hy
    simp only [f, eval_relP, relMat_act, hy', Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
  · simp only [OrbitDim.Coord, OrbitDim.GC, Ix, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin]
    have h1 : ∑ v, d v * d v = ∑ v, d v ^ 2 := by simp [sq]
    have h2 : ∑ i, d (t i) * d (s i) = ∑ i, d (s i) * d (t i) := by simp [mul_comm]
    have h3 : ∑ a : Arr V, d (tgt a) * d (src a) = ∑ a : Arr V, d (src a) * d (tgt a) := by
      simp [mul_comm]
    rw [h1, h2, h3]
    exact hNF
  · have hy' := (hzero y).1 hy
    set y' : Z := ⟨y, hy'⟩
    have hex' : ∃ z, lab z = lab y' := ⟨y', rfl⟩
    have hrep : rep (lab y') = (Classical.choose hex').1 := dif_pos hex'
    have hlab : lab (Classical.choose hex') = lab y' := Classical.choose_spec hex'
    refine ⟨rep (lab y'), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    set z := Classical.choose hex'
    have e : repObj d z.1 z.2 ≅ repObj d y'.1 y'.2 :=
      (hM z).some ≪≫ eqToIso (congrArg (Obj s t r X B) hlab) ≪≫ (hM y').some.symm
    rw [hrep]
    exact conj_of_iso d z.1 y'.1 z.2 y'.2 e.toLinearEquiv

end Main

end BoundQuiver

end MultiplicativeBasisDeformations
