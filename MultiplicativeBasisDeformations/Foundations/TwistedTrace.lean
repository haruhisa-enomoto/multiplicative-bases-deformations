import MultiplicativeBasisDeformations.Foundations.RowRotation
import MultiplicativeBasisDeformations.Foundations.CoveringMesh

/-!
# Lifted paths and row classes (Lemma A.2)

`lem:twisted-trace-surjection` (`periodic-mesh-calculations.tex:322–343`).
Let `π : ℤΔ → Q` be a covering commuting with translation, with signed mesh
coefficients. A path `p` of the doubled tree `Δ̄` starting at `v` lifts to `ℤΔ`
from `τ X` for any `X = (v, t)` (`liftZ`); the class of the image of the lift in
`coker D_m` is `phiD X p`. Since contextual relations of `Π(Δ)` lift term by term
with the same endpoints and heights, the linear extension `phiL X` of `phiD X`
kills the ideal of `Π(Δ)` (`phiL_eq_zero_of_mem`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v v' w

theorem Prefunctor.mapPath_cast {U W : Type*} [Quiver U] [Quiver W] (φ : U ⥤q W) {a b a' b' : U}
    (ha : a = a') (hb : b = b') (p : Quiver.Path a b) :
    φ.mapPath (p.cast ha hb) = (φ.mapPath p).cast (congrArg φ.obj ha) (congrArg φ.obj hb) := by
  subst ha hb; rfl

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D)

theorem par_path {a : T.Dbl} : ∀ {b : T.Dbl} (p : Quiver.Path a b),
    T.par (b : D) = T.par (a : D) + p.length
  | _, Quiver.Path.nil => by simp
  | _, Quiver.Path.cons p e => by
      rw [Quiver.Path.length_cons, T.par_adj e.down, par_path p]
      push_cast; ring

/-- The vertex of `ℤΔ` at the end of the lift of a path of `Δ̄` from `Y`. -/
def liftEnd (Y : T.ZVert) {b : T.Dbl} (p : Quiver.Path (T.toDbl Y.v) b) : T.ZVert :=
  ⟨b, Y.t + p.length, by push_cast; rw [Y.ht, T.par_path p]; rfl⟩

theorem liftEnd_nil (Y : T.ZVert) : Y = T.liftEnd Y Quiver.Path.nil := by
  ext <;> simp [liftEnd, toDbl]

theorem liftEnd_congr (Y : T.ZVert) {b : T.Dbl} {p q : Quiver.Path (T.toDbl Y.v) b}
    (h : p.length = q.length) : T.liftEnd Y p = T.liftEnd Y q := by
  ext <;> simp [liftEnd, h]

/-- **The lift of a path of `Δ̄` to `ℤΔ`** from `Y`: heights increase by one along
each arrow. -/
def liftZ (Y : T.ZVert) : ∀ {b : T.Dbl} (p : Quiver.Path (T.toDbl Y.v) b),
    Quiver.Path Y (T.liftEnd Y p)
  | _, Quiver.Path.nil => Quiver.Path.nil.cast rfl (T.liftEnd_nil Y)
  | _, Quiver.Path.cons p e =>
      (liftZ Y p).cons ⟨⟨e.down, by simp [liftEnd]; ring⟩⟩

theorem forget_mapPath_liftZ (Y : T.ZVert) : ∀ {b : T.Dbl} (p : Quiver.Path (T.toDbl Y.v) b),
    T.forget.mapPath (T.liftZ Y p) = p
  | _, Quiver.Path.nil => by
      rw [liftZ, Prefunctor.mapPath_cast]
      rfl
  | _, Quiver.Path.cons p e => by
      rw [liftZ, Prefunctor.mapPath_cons, forget_mapPath_liftZ Y p]
      rfl

theorem length_liftZ (Y : T.ZVert) {b : T.Dbl} (p : Quiver.Path (T.toDbl Y.v) b) :
    (T.liftZ Y p).length = p.length := by
  rw [← LinearPaths.length_mapPath T.forget, forget_mapPath_liftZ]

/-- Two paths of `ℤΔ` from the same vertex with the same image in `Δ̄` are equal. -/
theorem pathStar_eq_of_forget [Fintype D] [DecidableEq D] {Y E E' : T.ZVert} (P : Quiver.Path Y E) (P' : Quiver.Path Y E')
    (h : (⟨T.forget.obj E, T.forget.mapPath P⟩ : Quiver.PathStar (T.forget.obj Y)) =
      ⟨T.forget.obj E', T.forget.mapPath P'⟩) :
    (⟨E, P⟩ : Quiver.PathStar Y) = ⟨E', P'⟩ :=
  (T.forget_isCovering.pathStar_bijective Y).1 h

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]

open ScalarMeshCategory

/-- The row class of the image of a path of `ℤΔ`. -/
def rowZ (m : ℕ) {X Y : T.ZVert} (P : Quiver.Path X Y) : Coker c m :=
  rowQ c hQ m (π.mapPath P)

theorem rowZ_cast (m : ℕ) {X Y X' Y' : T.ZVert} (hX : X = X') (hY : Y = Y')
    (P : Quiver.Path X Y) : T.rowZ hQ π c m (P.cast hX hY) = T.rowZ hQ π c m P := by
  subst hX hY; rfl

theorem rowZ_eq_of_pathStar {m : ℕ} {X Y Y' : T.ZVert} {P : Quiver.Path X Y}
    {P' : Quiver.Path X Y'} (h : (⟨Y, P⟩ : Quiver.PathStar X) = ⟨Y', P'⟩) :
    T.rowZ hQ π c m P = T.rowZ hQ π c m P' := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  rw [eq_of_heq h]

/-- The linear extension of `rowZ`. -/
def rowZL (m : ℕ) (X Y : T.ZVert) :
    (LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y) →ₗ[k] Coker c m :=
  LinearPaths.extend (T.rowZ hQ π c m)

theorem pathMor_cast {x y x' y' : V} (hx : x = x') (hy : y = y') (w : Quiver.Path x y) :
    pathMor c (w.cast hx hy) = eqToHom (by rw [hx]) ≫ pathMor c w ≫ eqToHom (by rw [hy]) := by
  subst hx hy; simp

variable [Fintype D] [DecidableEq D] [DecidableRel T.orient]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))

include hπ hτ in
/-- **Mesh relations of `ℤΔ` give zero row classes**: the linear extension of
`rowZ` kills the mesh ideal. -/
theorem rowZL_eq_zero_of_mem (m : ℕ) {X Y : T.ZVert}
    {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ (RelSystem.mesh (T.pullCoeff hQ π c)).ideal _ _) : T.rowZL hQ π c m X Y f = 0 := by
  by_cases h : π.obj X = hQ.tauE (π.obj Y)
  · have key : ∀ g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y,
        T.rowZL hQ π c m X Y g = Submodule.Quotient.mk
          (Pi.single (M := fun x : Q.nonprojective ↦
              ScalarMeshCategory.obj c (Q.tau x).1 ⟶ ScalarMeshCategory.obj c x.1)
            (⟨π.obj Y, hQ.mem_nonprojective _⟩ : Q.nonprojective)
            (eqToHom (congrArg (ScalarMeshCategory.obj c) h.symm) ≫
              (RelationCategory.functor k (meshRelations c)).map
                (LinearPaths.mapPaths π X Y g))) := by
      intro g
      induction g using LinearPaths.induction_on with
      | h0 => simp
      | hadd f g hf hg =>
          rw [map_add, hf, hg, map_add, Functor.map_add, Preadditive.comp_add, Pi.single_add,
            Submodule.Quotient.mk_add]
      | hsingle P a =>
          rw [map_smul, map_smul, Functor.map_smul, Linear.comp_smul, Pi.single_smul,
            Submodule.Quotient.mk_smul]
          congr 1
          rw [rowZL, LinearPaths.extend_path, rowZ, ← rowQ_cast c hQ m h rfl, rowQ_eq_mk,
            pathMor_cast, LinearPaths.mapPaths_path]
          simp [pathMor]
    have h0 := (RelationCategory.functor_map_eq_zero_iff (k := k) (meshRelations c)
      (LinearPaths.mapPaths π X Y f)).2 (T.mapPaths_mem_mesh hQ π hπ hτ c hf)
    rw [key]
    simp only [h0, Limits.comp_zero, Pi.single_zero, Submodule.Quotient.mk_zero]
  · have key : ∀ g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y,
        T.rowZL hQ π c m X Y g = 0 := by
      intro g
      induction g using LinearPaths.induction_on with
      | h0 => simp
      | hadd f g hf hg => rw [map_add, hf, hg, add_zero]
      | hsingle P a =>
          rw [map_smul, rowZL, LinearPaths.extend_path, rowZ, rowQ, dif_neg h, smul_zero]
    exact key f

/-- **The row class of the lift of a path of `Δ̄` from `τ X`.** -/
def phiD (m : ℕ) (X : T.ZVert) {b : T.Dbl} (p : Quiver.Path (T.toDbl X.v) b) : Coker c m :=
  T.rowZ hQ π c m (T.liftZ (T.ztau X) p)

/-- The linear extension of `phiD`. -/
def phiL (m : ℕ) (X : T.ZVert) (b : T.Dbl) :
    (LinearPaths.obj (k := k) (T.toDbl X.v) ⟶ LinearPaths.obj b) →ₗ[k] Coker c m :=
  LinearPaths.extend (T.phiD hQ π c m X)

omit [DecidableRel T.orient] in
/-- Lifting combinations of paths of a fixed length, which share their end. -/
def liftN (Y : T.ZVert) {b : T.Dbl} (p₀ : Quiver.Path (T.toDbl Y.v) b) :
    (LinearPaths.obj (k := k) (T.toDbl Y.v) ⟶ LinearPaths.obj b) →ₗ[k]
      (LinearPaths.obj (k := k) Y ⟶ LinearPaths.obj (T.liftEnd Y p₀)) :=
  LinearPaths.extend fun p ↦ if h : p.length = p₀.length then
    LinearPaths.path ((T.liftZ Y p).cast rfl (T.liftEnd_congr Y h)) else 0

omit [DecidableRel T.orient] in
theorem liftN_induction {Y : T.ZVert} {b : T.Dbl} (p₀ : Quiver.Path (T.toDbl Y.v) b)
    {P : (LinearPaths.obj (k := k) (T.toDbl Y.v) ⟶ LinearPaths.obj b) → Prop}
    (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (a : k) f, P f → P (a • f))
    (hp : ∀ p : Quiver.Path (T.toDbl Y.v) b, p.length = p₀.length → P (LinearPaths.path p))
    {f : LinearPaths.obj (k := k) (T.toDbl Y.v) ⟶ LinearPaths.obj b}
    (hf : f ∈ LinearPaths.degreePart (k := k) p₀.length _ _) : P f := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨p, hp', rfl⟩ := hf; exact hp p hp'
  | zero => exact h0
  | add f g _ _ hf hg => exact hadd f g hf hg
  | smul a f _ hf => exact hsmul a f hf

omit [DecidableRel T.orient] in
theorem forget_liftN (Y : T.ZVert) {b : T.Dbl} (p₀ : Quiver.Path (T.toDbl Y.v) b)
    {f : LinearPaths.obj (k := k) (T.toDbl Y.v) ⟶ LinearPaths.obj b}
    (hf : f ∈ LinearPaths.degreePart (k := k) p₀.length _ _) :
    LinearPaths.mapPaths T.forget _ _ (T.liftN Y p₀ f) = f := by
  refine liftN_induction T p₀ (P := fun f ↦ LinearPaths.mapPaths T.forget _ _ (T.liftN Y p₀ f) = f)
    (by simp) (fun f g hf hg ↦ by rw [map_add, map_add, hf, hg])
    (fun a f hf ↦ by rw [map_smul, map_smul, hf]) (fun p hp ↦ ?_) hf
  rw [liftN, LinearPaths.extend_path, dif_pos hp, LinearPaths.mapPaths_path,
    Prefunctor.mapPath_cast]
  congr 1
  rw [Quiver.Path.cast_eq_cast, forget_mapPath_liftZ]
  exact cast_eq _ _

theorem rowZL_liftN (m : ℕ) (X : T.ZVert) {b : T.Dbl} (p₀ : Quiver.Path (T.toDbl X.v) b)
    {f : LinearPaths.obj (k := k) (T.toDbl X.v) ⟶ LinearPaths.obj b}
    (hf : f ∈ LinearPaths.degreePart (k := k) p₀.length _ _) :
    T.rowZL hQ π c m _ _ (T.liftN (T.ztau X) p₀ f) = T.phiL hQ π c m X b f := by
  refine liftN_induction T (Y := T.ztau X) p₀
    (P := fun f ↦ T.rowZL hQ π c m _ _ (T.liftN (T.ztau X) p₀ f) = T.phiL hQ π c m X b f)
    (by simp) (fun f g hf hg ↦ by rw [map_add, map_add, hf, hg, map_add])
    (fun a f hf ↦ by rw [map_smul, map_smul, hf, map_smul]) (fun p hp ↦ ?_) hf
  have e1 : T.liftN (k := k) (T.ztau X) p₀ (LinearPaths.path p) =
      LinearPaths.path ((T.liftZ (T.ztau X) p).cast rfl (T.liftEnd_congr _ hp)) := by
    unfold liftN
    rw [LinearPaths.extend_path, dif_pos hp]
  rw [e1]
  unfold rowZL phiL
  rw [LinearPaths.extend_path, LinearPaths.extend_path, rowZ_cast]
  rfl

omit [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)] in
theorem preprojRel_mem_degreePart (i : T.Dbl) :
    T.preprojRel k i ∈ LinearPaths.degreePart (k := k) 2 i i := by
  unfold preprojRel
  refine Submodule.sum_mem _ fun e _ ↦ Submodule.smul_mem _ _ ?_
  have := LinearPaths.path_mem_degreePart (k := k)
    (e.2.toPath.comp (Quiver.Hom.toPath (show e.1 ⟶ i from ⟨e.2.down.symm⟩)))
  rwa [Quiver.Path.length_comp, Quiver.Path.length_toPath, Quiver.Path.length_toPath] at this

include hπ hτ in
/-- **Relations of `Π(Δ)` give zero row classes** (proof of Lemma A.2:
"contextual mesh relations lift term by term with the same endpoints and
heights"). -/
theorem phiL_eq_zero_of_mem (hsig : T.pullCoeff hQ π c = T.zSigned k) (m : ℕ) (X : T.ZVert)
    {b : T.Dbl} {f : LinearPaths.obj (k := k) (T.toDbl X.v) ⟶ LinearPaths.obj b}
    (hf : f ∈ (T.preproj k).ideal _ _) : T.phiL hQ π c m X b f = 0 := by
  refine (T.preproj k).ideal_induction (P := fun f ↦ T.phiL hQ π c m X b f = 0) (by simp)
    (fun f g hf hg ↦ by rw [map_add, hf, hg, add_zero])
    (fun a f hf ↦ by rw [map_smul, hf, smul_zero]) (fun i p p' ↦ ?_) hf
  rcases isEmpty_or_nonempty (Σ y : T.Dbl, ((T.preproj k).s i : T.Dbl) ⟶ y) with hE | ⟨⟨y, e⟩⟩
  · have : (T.preproj k).rel i = 0 := by
      change T.preprojRel k i = 0
      unfold preprojRel
      exact Finset.sum_eq_zero fun e _ ↦ (hE.false e).elim
    rw [this, Limits.zero_comp, Limits.comp_zero, map_zero]
  · set p₀ := (p.comp (e.toPath.comp (Quiver.Hom.toPath (show y ⟶ (T.preproj k).t i from
      ⟨e.down.symm⟩)))).comp p'
    have hdeg : LinearPaths.path p ≫ (T.preproj k).rel i ≫ LinearPaths.path p' ∈
        LinearPaths.degreePart (k := k) p₀.length _ _ := by
      have h := LinearPaths.comp_mem_degreePart (LinearPaths.path_mem_degreePart (k := k) p)
        (LinearPaths.comp_mem_degreePart (T.preprojRel_mem_degreePart (k := k) i)
          (LinearPaths.path_mem_degreePart (k := k) p'))
      convert h using 2
      · simp only [p₀, Quiver.Path.length_comp, Quiver.Path.length_toPath]
        omega
      · rfl
    rw [← T.rowZL_liftN hQ π c m X p₀ hdeg]
    apply T.rowZL_eq_zero_of_mem hQ π c hπ hτ
    rw [hsig]
    apply T.mem_mesh_of_forget k
    rw [T.forget_liftN (T.ztau X) p₀ hdeg]
    exact (T.preproj k).comp_rel_comp_mem i _ _

/-! ### Rotation -/

omit [Fintype D] [DecidableEq D] [DecidableRel T.orient] in
theorem rowQ_rotate' (hc : OppositeOnMates c hQ) {m : ℕ} {u w₁ y x : V}
    (hu : u = hQ.tauE y) (hw : w₁ = hQ.tauE x) (b : u ⟶ w₁) (a : y ⟶ x) (q : Quiver.Path w₁ y)
    (hq : q.length = m) : rowQ c hQ m (b.toPath.comp q) = rowQ c hQ m (q.cons a) := by
  subst hu hw
  exact rowQ_rotate c hQ hc a b q hq

omit [Fintype D] [DecidableEq D] [DecidableRel T.orient] in
/-- Rotation of a lifted row: the first arrow moves to the end. -/
theorem rowZ_rotate (hc : OppositeOnMates c hQ) {m : ℕ} {Z Y₁ E E' : T.ZVert} (a₁ : Z ⟶ Y₁)
    (B : Quiver.Path Y₁ E) (a₂ : E ⟶ E') (hZ : π.obj Z = hQ.tauE (π.obj E))
    (hY : π.obj Y₁ = hQ.tauE (π.obj E')) (hB : B.length = m) :
    T.rowZ hQ π c m (a₁.toPath.comp B) = T.rowZ hQ π c m (B.cons a₂) := by
  rw [rowZ, rowZ, Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath, Prefunctor.mapPath_cons]
  exact rowQ_rotate' hQ c hc hZ hY _ _ _ (by rw [LinearPaths.length_mapPath, hB])

/-- `X` raised by one along an arrow of `Δ̄`. -/
def raise (X : T.ZVert) {y : T.Dbl} (e : T.toDbl X.v ⟶ y) : T.ZVert :=
  ⟨y, X.t + 1, by push_cast; rw [X.ht]; exact (T.par_adj e.down).symm⟩

section Deck

variable (σ : D ≃ D) (hσ : ∀ a b, T.G.Adj (σ a) (σ b) ↔ T.G.Adj a b) (s : ℤ)
  (hσp : ∀ v, T.par (σ v) = T.par v + s)

/-- An automorphism of `ℤΔ` of height form `(v, t) ↦ (σ v, t + s)`. -/
def zAct : T.ZVert ⥤q T.ZVert where
  obj X := ⟨σ X.v, X.t + s, by push_cast; rw [hσp, X.ht]⟩
  map a := ⟨⟨(hσ _ _).2 a.down.1, by simp only [a.down.2]; ring⟩⟩

/-- The corresponding automorphism of `Δ̄`. -/
def dAct : T.Dbl ⥤q T.Dbl where
  obj v := σ v
  map e := ⟨(hσ _ _).2 e.down⟩

omit [Fintype D] [DecidableEq D] [DecidableRel T.orient] in
theorem forget_zAct_mapPath {X Y : T.ZVert} (P : Quiver.Path X Y) :
    T.forget.mapPath ((T.zAct σ hσ s hσp).mapPath P) =
      (T.dAct σ hσ).mapPath (T.forget.mapPath P) := by
  induction P with
  | nil => rfl
  | cons P a ih => rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, ih]; rfl

omit [Fintype D] [DecidableEq D] [DecidableRel T.orient] in
theorem mapPath_zAct (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {X Y : T.ZVert}
    (P : Quiver.Path X Y) :
    π.mapPath ((T.zAct σ hσ s hσp).mapPath P) = (π.mapPath P).cast (hdeck X).symm (hdeck Y).symm := by
  induction P with
  | nil => exact (Quiver.Path.cast_nil _).symm
  | cons P a ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, ih,
        Quiver.Path.cast_cons]
      congr 1
      · exact hdeck _
      · exact (Quiver.Path.cast_heq _ _ _).trans (Quiver.Path.cast_heq _ _ _).symm
      · exact (heq_of_eq (Subsingleton.elim _
          (Quiver.Hom.cast (hdeck _).symm (hdeck _).symm (π.map a)))).trans
          ((Quiver.Hom.cast_heq _ _ _).trans (Quiver.Hom.cast_heq _ _ _).symm)

omit [Fintype D] [DecidableEq D] [DecidableRel T.orient] in
/-- Row classes are invariant under deck transformations. -/
theorem rowZ_zAct (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {m : ℕ}
    {X Y : T.ZVert} (P : Quiver.Path X Y) :
    T.rowZ hQ π c m ((T.zAct σ hσ s hσp).mapPath P) = T.rowZ hQ π c m P := by
  rw [rowZ, mapPath_zAct T π σ hσ s hσp hdeck, rowQ_cast]; rfl

omit [DecidableRel T.orient] in
theorem phiD_zAct (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {m : ℕ}
    (X : T.ZVert) {b : T.Dbl} (p : Quiver.Path (T.toDbl X.v) b) :
    T.phiD hQ π c m ((T.zAct σ hσ s hσp).obj X) ((T.dAct σ hσ).mapPath p) =
      T.phiD hQ π c m X p := by
  have h0 : (T.zAct σ hσ s hσp).obj (T.ztau X) = T.ztau ((T.zAct σ hσ s hσp).obj X) := by
    ext
    · rfl
    · simp only [zAct, ztau]; ring
  rw [phiD, phiD, ← T.rowZ_zAct hQ π c σ hσ s hσp hdeck (T.liftZ (T.ztau X) p),
    ← T.rowZ_cast hQ π c m h0 rfl]
  apply rowZ_eq_of_pathStar
  apply pathStar_eq_of_forget
  refine Sigma.ext rfl ?_
  rw [Prefunctor.mapPath_cast, forget_zAct_mapPath, forget_mapPath_liftZ, forget_mapPath_liftZ]
  dsimp only
  exact (Quiver.Path.cast_heq _ _ _).symm

end Deck

omit [DecidableRel T.orient] in
theorem liftZ_comp_pathStar (Y : T.ZVert) {b b' : T.Dbl} (p : Quiver.Path (T.toDbl Y.v) b)
    (q : Quiver.Path b b') :
    (⟨_, T.liftZ Y (p.comp q)⟩ : Quiver.PathStar Y) =
      ⟨_, (T.liftZ Y p).comp (T.liftZ (T.liftEnd Y p) q)⟩ := by
  apply pathStar_eq_of_forget
  refine Sigma.ext rfl (heq_of_eq ?_)
  rw [Prefunctor.mapPath_comp, forget_mapPath_liftZ, forget_mapPath_liftZ, forget_mapPath_liftZ]

theorem phiD_congr {m : ℕ} {X X' : T.ZVert} (h : X = X') {b : T.Dbl}
    (p : Quiver.Path (T.toDbl X.v) b) :
    T.phiD hQ π c m X p = T.phiD hQ π c m X' (p.cast (by rw [h]) rfl) := by
  subst h; rfl

section Rotate

variable (σ : D ≃ D) (hσ : ∀ a b, T.G.Adj (σ a) (σ b) ↔ T.G.Adj a b) (s : ℤ)
  (hσp : ∀ v, T.par (σ v) = T.par v + s)

include hτ in
/-- **Twisted rotation of one arrow** (proof of Lemma A.2): for a row path
`e q` from `v` to `σ v` of length `2 + s`, cutting after the initial arrow `e`
and correcting its mesh mate gives `[e q] = [q σ(e)]`, the latter lifted from
one level higher. -/
theorem phiD_rotate (hc : OppositeOnMates c hQ)
    (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {m : ℕ} (X : T.ZVert) {y : T.Dbl}
    (e : T.toDbl X.v ⟶ y) (q : Quiver.Path y ((T.dAct σ hσ).obj (T.toDbl X.v)))
    (hq : q.length = m) (hs : (m : ℤ) + 1 = 2 + s) :
    T.phiD hQ π c m X (e.toPath.comp q) =
      T.phiD hQ π c m (T.raise X e) (q.comp ((T.dAct σ hσ).map e).toPath) := by
  set R := T.raise X e
  let a₁ : T.ztau X ⟶ T.ztau R := ⟨⟨e.down, by simp only [ztau, R, raise]; ring⟩⟩
  have hE : T.liftEnd (T.ztau R) q = (T.zAct σ hσ s hσp).obj X := by
    ext
    · rfl
    · simp only [liftEnd, ztau, R, raise, zAct, hq]; omega
  let a₂ : T.liftEnd (T.ztau R) q ⟶ (T.zAct σ hσ s hσp).obj R :=
    ⟨⟨((T.dAct σ hσ).map e).down, by
      simp only [liftEnd, ztau, R, raise, zAct, hq]; omega⟩⟩
  have h1 : T.phiD hQ π c m X (e.toPath.comp q) =
      T.rowZ hQ π c m (a₁.toPath.comp (T.liftZ (T.ztau R) q)) := by
    apply rowZ_eq_of_pathStar
    apply pathStar_eq_of_forget
    refine Sigma.ext rfl (heq_of_eq ?_)
    rw [Prefunctor.mapPath_comp, forget_mapPath_liftZ, forget_mapPath_liftZ,
      Prefunctor.mapPath_toPath]
    rfl
  have h2 : T.phiD hQ π c m R (q.comp ((T.dAct σ hσ).map e).toPath) =
      T.rowZ hQ π c m ((T.liftZ (T.ztau R) q).cons a₂) := by
    apply rowZ_eq_of_pathStar
    apply pathStar_eq_of_forget
    refine Sigma.ext rfl (heq_of_eq ?_)
    rw [Prefunctor.mapPath_cons, forget_mapPath_liftZ, forget_mapPath_liftZ]
    rfl
  rw [h1, h2]
  refine T.rowZ_rotate hQ π c hc a₁ _ a₂ ?_ ?_ (by rw [length_liftZ, hq])
  · rw [hE, hdeck, hτ]
  · rw [hdeck, hτ]

include hτ in
/-- **Twisted rotation of an initial segment**: `[U W] = [W σ(U)]`. -/
theorem phiD_rotate_path (hc : OppositeOnMates c hQ)
    (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {m : ℕ} (hs : (m : ℤ) + 1 = 2 + s)
    (X : T.ZVert) {z : T.Dbl} (U : Quiver.Path (T.toDbl X.v) z) :
    ∀ (W : Quiver.Path z ((T.dAct σ hσ).obj (T.toDbl X.v))), U.length + W.length = m + 1 →
      T.phiD hQ π c m X (U.comp W) =
        T.phiD hQ π c m (T.liftEnd X U) (W.comp ((T.dAct σ hσ).mapPath U)) := by
  induction U with
  | nil =>
      intro W _
      rw [Quiver.Path.nil_comp, Prefunctor.mapPath_nil, Quiver.Path.comp_nil,
        T.phiD_congr hQ π c (T.liftEnd_nil X) W]
      congr 1
  | cons U' e ih =>
      intro W hW
      rw [Quiver.Path.length_cons] at hW
      have h1 : (U'.cons e).comp W = U'.comp (e.toPath.comp W) := by
        rw [← Quiver.Path.comp_assoc]; rfl
      rw [h1, ih (e.toPath.comp W) (by rw [Quiver.Path.length_comp, Quiver.Path.length_toPath]; omega),
        Quiver.Path.comp_assoc]
      rw [T.phiD_rotate hQ π c hτ σ hσ s hσp hc hdeck (T.liftEnd X U') e
        (W.comp ((T.dAct σ hσ).mapPath U'))
        (by rw [Quiver.Path.length_comp, LinearPaths.length_mapPath]; omega) hs]
      have h2 : T.raise (T.liftEnd X U') e = T.liftEnd X (U'.cons e) := by
        ext
        · rfl
        · simp [raise, liftEnd]; ring
      rw [T.phiD_congr hQ π c h2, Prefunctor.mapPath_cons, Quiver.Path.comp_assoc]
      congr 1

include hτ in
/-- **The row class is independent of the repetition coordinate** (proof of
Lemma A.2: "applying this rotation `d` times identifies the row with its
translate by `τ`"). -/
theorem phiD_ztauInv (hc : OppositeOnMates c hQ)
    (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {m : ℕ} (hs : (m : ℤ) + 1 = 2 + s)
    (X : T.ZVert) (p : Quiver.Path (T.toDbl X.v) ((T.dAct σ hσ).obj (T.toDbl X.v)))
    (hp : p.length = m + 1) :
    T.phiD hQ π c m X p = T.phiD hQ π c m (T.ztauInv X) p := by
  have h := T.phiD_rotate_path hQ π c hτ σ hσ s hσp hc hdeck hs X p Quiver.Path.nil
    (by rw [Quiver.Path.length_nil, hp])
  rw [Quiver.Path.comp_nil, Quiver.Path.nil_comp] at h
  have h2 : T.liftEnd X p = (T.zAct σ hσ s hσp).obj (T.ztauInv X) := by
    ext
    · rfl
    · simp only [liftEnd, zAct, ztauInv, hp]; push_cast; omega
  rw [h, T.phiD_congr hQ π c h2]
  rw [← T.phiD_zAct hQ π c σ hσ s hσp hdeck (T.ztauInv X) p]
  congr 1

include hτ in
theorem phiD_height (hc : OppositeOnMates c hQ)
    (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z) {m : ℕ} (hs : (m : ℤ) + 1 = 2 + s)
    (X : T.ZVert) (p : Quiver.Path (T.toDbl X.v) ((T.dAct σ hσ).obj (T.toDbl X.v)))
    (hp : p.length = m + 1) (t' : ℤ) (ht' : (t' : ZMod 2) = T.par X.v) :
    T.phiD hQ π c m X p = T.phiD hQ π c m ⟨X.v, t', ht'⟩ p := by
  have up : ∀ n : ℕ, ∀ Y : T.ZVert, ∀ (hv : Y.v = X.v) (hY : ((Y.t + 2 * n : ℤ) : ZMod 2) = T.par X.v),
      T.phiD hQ π c m Y (p.cast (by rw [hv]) rfl) = T.phiD hQ π c m ⟨X.v, Y.t + 2 * n, hY⟩ p := by
    intro n
    induction n with
    | zero =>
        intro Y hv hY
        rw [T.phiD_congr hQ π c (show Y = ⟨X.v, Y.t + 2 * ((0 : ℕ) : ℤ), hY⟩ by ext <;> simp [hv])]
        congr 1
        rw [Quiver.Path.cast_cast, Quiver.Path.cast_eq_cast]
        exact cast_eq _ _
    | succ n ih =>
        intro Y hv hY
        have hY' : ((Y.t + 2 * n : ℤ) : ZMod 2) = T.par X.v := by
          have : ((Y.t + 2 * n : ℤ) : ZMod 2) = ((Y.t + 2 * ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod 2) := by
            push_cast
            rw [show (2 : ZMod 2) = 0 from rfl]; ring
          rw [this, hY]
        rw [ih Y hv hY', T.phiD_ztauInv hQ π c hτ σ hσ s hσp hc hdeck hs
          (⟨X.v, Y.t + 2 * n, hY'⟩ : T.ZVert) p hp]
        congr 1
        ext
        · rfl
        · simp only [ztauInv]; push_cast; ring
  have hpar : ((t' - X.t : ℤ) : ZMod 2) = 0 := by push_cast; rw [ht', X.ht, sub_self]
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 hpar
  rcases le_or_gt 0 j with h0 | h0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    obtain rfl : t' = X.t + 2 * n := by omega
    have := up n X rfl ht'
    rw [Quiver.Path.cast_eq_cast, cast_eq] at this
    exact this
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -j := ⟨(-j).toNat, Int.toNat_of_nonneg (by omega)⟩
    rcases X with ⟨xv, xt, xh⟩
    obtain rfl : xt = t' + 2 * n := by simp only at hj; omega
    have := up n ⟨xv, t', ht'⟩ rfl xh
    rw [Quiver.Path.cast_eq_cast, cast_eq] at this
    exact this.symm

end Rotate

end OrientedTree

end MultiplicativeBasisDeformations
