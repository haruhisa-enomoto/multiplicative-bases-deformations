module

public import MultiplicativeBasisDeformations.Foundations.CoveringIdeals
public import MultiplicativeBasisDeformations.Foundations.StableTranslation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The repetition `ℤΔ` of a tree and the signed preprojective category `Π(Δ)`

`scalar-normalization.tex` and `periodic-mesh-calculations.tex`.

We use the height coordinates of Proposition 4.1(2)
(`periodic-mesh-calculations.tex`). Fix a finite graph `Δ` with a proper
two-colouring `par`. A vertex of `ℤΔ` is a pair `(v, t)` with `t ≡ par v`
(mod 2), its height being `t`; there is an arrow `(u, t) → (v, t + 1)` for every
edge `u — v`. Translation is `(v, t) ↦ (v, t - 2)`. For an orientation of `Δ`
with `d_v - d_u = 1` along every arrow `u → v`, this is the repetition quiver
of Subsection 4.1 under `v_j ↦ (v, 2j + d_v)`.

`Π(Δ)` is the path category of the doubled quiver modulo the vertex relations
`∑_{a : x → y} a a* - ∑_{a : y → x} a* a`, i.e.
`ρ_x = ∑_{y — x} ε(x, y) (x → y → x)` with `ε(x, y) = 1` if the edge is
oriented `x → y` and `-1` otherwise. The signed mesh coefficients of `ℤΔ` are
`c_{(x,t), (y,t-1)} = ε(x, y)`, so forgetting heights sends the mesh relation at
`(x, t)` to `ρ_x`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

/-- A finite graph with a proper two-colouring and an orientation of its
edges. -/
structure OrientedTree (D : Type v) where
  G : SimpleGraph D
  par : D → ZMod 2
  par_adj : ∀ {u w : D}, G.Adj u w → par w = par u + 1
  orient : D → D → Prop
  orient_adj : ∀ {u w : D}, orient u w → G.Adj u w
  orient_or : ∀ {u w : D}, G.Adj u w → (orient u w ↔ ¬ orient w u)

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D)

/-- A vertex of the repetition `ℤΔ`, in height coordinates. -/
@[ext]
structure ZVert where
  v : D
  t : ℤ
  ht : (t : ZMod 2) = T.par v

instance : Quiver T.ZVert where
  Hom X Y := PLift (T.G.Adj X.v Y.v ∧ Y.t = X.t + 1)

instance (X Y : T.ZVert) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- Translation on `ℤΔ`. -/
def ztau (X : T.ZVert) : T.ZVert where
  v := X.v
  t := X.t - 2
  ht := by
    rw [← X.ht]; push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, sub_zero]

/-- Inverse translation on `ℤΔ`. -/
def ztauInv (X : T.ZVert) : T.ZVert where
  v := X.v
  t := X.t + 2
  ht := by
    rw [← X.ht]; push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, add_zero]

/-- `ℤΔ` as a stable translation quiver. -/
def zQuiver : TranslationQuiver T.ZVert where
  nonprojective := Set.univ
  noninjective := Set.univ
  tau :=
    { toFun := fun X ↦ ⟨T.ztau X.1, trivial⟩
      invFun := fun X ↦ ⟨T.ztauInv X.1, trivial⟩
      left_inv := fun X ↦ by ext <;> simp [ztau, ztauInv]
      right_inv := fun X ↦ by ext <;> simp [ztau, ztauInv] }
  mate x y :=
    { toFun := fun a ↦ ⟨⟨a.down.1.symm, by
          have := a.down.2; change y.t = (x.1.t - 2) + 1; omega⟩⟩
      invFun := fun b ↦ ⟨⟨b.down.1.symm, by
          have := b.down.2; change y.t = (x.1.t - 2) + 1 at this; omega⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

theorem zQuiver_isStable : T.zQuiver.IsStable := ⟨rfl, rfl⟩

@[simp] theorem zQuiver_tau_v (X : T.zQuiver.nonprojective) : (T.zQuiver.tau X).1.v = X.1.v := rfl

@[simp] theorem zQuiver_tau_t (X : T.zQuiver.nonprojective) : (T.zQuiver.tau X).1.t = X.1.t - 2 :=
  rfl

variable [Fintype D] [DecidableEq D]

noncomputable instance instFintypeCostar (X : T.ZVert) : Fintype (Σ Y : T.ZVert, Y ⟶ X) :=
  Fintype.ofInjective (fun e : Σ Y : T.ZVert, Y ⟶ X ↦ e.1.v) (by
    rintro ⟨Y, a⟩ ⟨Y', a'⟩ h
    have ht : Y.t = Y'.t := by have := a.down.2; have := a'.down.2; omega
    have : Y = Y' := ZVert.ext h ht
    subst this
    exact congrArg _ (Subsingleton.elim a a'))

/-- The sign `ε(u, w)` of an edge: `1` if it is oriented `u → w`, else `-1`. -/
def sgn (k : Type u) [CommRing k] [DecidableRel T.orient] (u w : D) : kˣ :=
  if T.orient u w then 1 else -1

theorem sgn_swap (k : Type u) [CommRing k] [DecidableRel T.orient] {u w : D} (h : T.G.Adj u w) :
    T.sgn k w u = - T.sgn k u w := by
  unfold sgn
  by_cases huw : T.orient u w
  · rw [if_pos huw, if_neg ((T.orient_or h).1 huw)]
  · rw [if_neg huw, if_pos (by by_contra h'; exact huw ((T.orient_or h).2 h')), neg_neg]

/-- The signed preprojective mesh coefficients on `ℤΔ`. -/
def zSigned (k : Type u) [CommRing k] [DecidableRel T.orient] : MeshCoefficients k T.zQuiver :=
  fun X Y _ ↦ T.sgn k X.1.v Y.v

/-- The doubled quiver of `Δ`: an arrow each way along every edge. -/
def Dbl (_T : OrientedTree D) : Type v := D

instance : Quiver T.Dbl where
  Hom u w := PLift (T.G.Adj (u : D) (w : D))

instance (u w : T.Dbl) : Subsingleton (u ⟶ w) := inferInstanceAs (Subsingleton (PLift _))

instance : Fintype T.Dbl := inferInstanceAs (Fintype D)

instance : DecidableEq T.Dbl := inferInstanceAs (DecidableEq D)

noncomputable instance instFintypeDblStar (x : T.Dbl) : Fintype (Σ y : T.Dbl, x ⟶ y) :=
  Fintype.ofInjective (fun e : Σ y : T.Dbl, x ⟶ y ↦ (e.1 : D)) (by
    rintro ⟨y, a⟩ ⟨y', a'⟩ h
    change y = y' at h
    subst h
    exact congrArg _ (Subsingleton.elim a a'))

/-- The relation `ρ_x = ∑_{y — x} ε(x, y) (x → y → x)` of `Π(Δ)`. -/
def preprojRel (k : Type u) [CommRing k] [DecidableRel T.orient] (x : T.Dbl) :
    LinearPaths.obj (k := k) x ⟶ LinearPaths.obj x :=
  ∑ e : Σ y : T.Dbl, x ⟶ y, ((T.sgn k (x : D) (e.1 : D) : kˣ) : k) •
    LinearPaths.path (e.2.toPath.comp (Quiver.Hom.toPath (show e.1 ⟶ x from ⟨e.2.down.symm⟩)))

/-- The relations of `Π(Δ)`. -/
def preproj (k : Type u) [CommRing k] [DecidableRel T.orient] : RelSystem k T.Dbl where
  I := D
  s x := x
  t x := x
  rel x := T.preprojRel k x

/-- Forgetting heights, `ℤΔ → Δ̄`. -/
def forget : T.ZVert ⥤q T.Dbl where
  obj X := X.v
  map a := ⟨a.down.1⟩

theorem forget_isCovering : T.forget.IsCovering := by
  refine ⟨fun X ↦ ⟨?_, ?_⟩, fun X ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨Y, a⟩ ⟨Y', a'⟩ h
    simp only [Prefunctor.star_apply, Sigma.mk.inj_iff] at h
    have hv : Y.v = Y'.v := h.1
    have ht : Y.t = Y'.t := by have := a.down.2; have := a'.down.2; omega
    have : Y = Y' := ZVert.ext hv ht
    subst this
    exact congrArg _ (Subsingleton.elim a a')
  · rintro ⟨y, b⟩
    refine ⟨⟨⟨y, X.t + 1, ?_⟩, ⟨b.down, rfl⟩⟩, rfl⟩
    push_cast
    rw [X.ht]
    exact (T.par_adj b.down).symm
  · rintro ⟨Y, a⟩ ⟨Y', a'⟩ h
    simp only [Prefunctor.costar_apply, Sigma.mk.inj_iff] at h
    have hv : Y.v = Y'.v := h.1
    have ht : Y.t = Y'.t := by have := a.down.2; have := a'.down.2; omega
    have : Y = Y' := ZVert.ext hv ht
    subst this
    exact congrArg _ (Subsingleton.elim a a')
  · rintro ⟨y, b⟩
    have hpar : ((X.t - 1 : ℤ) : ZMod 2) = T.par y := by
      have h1 : T.par X.v = T.par (y : D) + 1 := T.par_adj b.down
      push_cast
      rw [X.ht, h1]
      ring_nf
    refine ⟨⟨⟨y, X.t - 1, hpar⟩, ⟨b.down, by simp⟩⟩, rfl⟩

/-- A vertex of `Δ`, as a vertex of the doubled quiver. -/
def toDbl (v : D) : T.Dbl := v

/-- The arrows into `X` correspond to the edges at `X.v`. -/
def costarEquiv (X : T.ZVert) : (Σ Y : T.ZVert, Y ⟶ X) ≃ (Σ y : T.Dbl, T.toDbl X.v ⟶ y) where
  toFun e := ⟨T.toDbl e.1.v, ⟨e.2.down.1.symm⟩⟩
  invFun e := ⟨⟨e.1, X.t - 1, by
      have h1 : T.par X.v = T.par (e.1 : D) + 1 :=
        T.par_adj (show T.G.Adj (e.1 : D) X.v from (PLift.down e.2).symm)
      rw [Int.cast_sub, X.ht, h1]; push_cast; ring_nf⟩, ⟨e.2.down.symm, by simp⟩⟩
  left_inv e := by
    obtain ⟨Y, a⟩ := e
    have ht : Y.t = X.t - 1 := by have := a.down.2; omega
    obtain ⟨v, t, h⟩ := Y
    simp only at ht
    subst ht
    rfl
  right_inv e := rfl

variable (k : Type u) [CommRing k] [DecidableRel T.orient]

/-- Forgetting heights sends the signed mesh relation at `(x, t)` to `ρ_x`. -/
theorem mapPaths_forget_meshRelation (X : T.zQuiver.nonprojective) :
    LinearPaths.mapPaths (k := k) T.forget _ _ (meshRelation (T.zSigned k) X) =
      T.preprojRel k (T.toDbl X.1.v) := by
  unfold meshRelation preprojRel
  rw [map_sum]
  refine Fintype.sum_equiv (T.costarEquiv X.1) _ _ fun e ↦ ?_
  rw [map_smul, LinearPaths.mapPaths_path, Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath,
    Prefunctor.mapPath_toPath]
  rfl

theorem ztau_ztauInv (Z : T.ZVert) : T.ztau (T.ztauInv Z) = Z := by
  ext <;> simp [ztau, ztauInv]

/-- Forgetting heights maps the signed mesh ideal of `ℤΔ` into the ideal of
`Π(Δ)`. -/
theorem forget_mem_preproj {X Y : T.ZVert} {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ (RelSystem.mesh (T.zSigned k)).ideal _ _) :
    LinearPaths.mapPaths T.forget X Y f ∈ (T.preproj k).ideal _ _ := by
  refine RelSystem.mapPaths_mem_ideal T.forget _ _ (fun i p p' ↦ ?_) hf
  rw [LinearPaths.mapPaths_comp, LinearPaths.mapPaths_comp, LinearPaths.mapPaths_path,
    LinearPaths.mapPaths_path]
  change _ ≫ LinearPaths.mapPaths T.forget _ _ (meshRelation (T.zSigned k) i) ≫ _ ∈ _
  rw [mapPaths_forget_meshRelation]
  exact (T.preproj k).comp_rel_comp_mem (T.toDbl i.1.v) _ _

/-- **Lifting `Π(Δ)` relations to `ℤΔ`**: forgetting heights reflects the
ideal. -/
theorem mem_mesh_of_forget {X Y : T.ZVert} {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : LinearPaths.mapPaths T.forget X Y f ∈ (T.preproj k).ideal _ _) :
    f ∈ (RelSystem.mesh (T.zSigned k)).ideal _ _ := by
  refine RelSystem.mem_ideal_of_mapPaths_mem T.forget _ _ T.forget_isCovering
    (RelSystem.lift_condition T.forget T.forget_isCovering _ _ ?_) hf
  intro Z i' h
  change i' = Z.v at h
  subst h
  refine ⟨⟨T.ztauInv Z, trivial⟩, T.ztau_ztauInv Z, rfl, ?_⟩
  change LinearPaths.mapPaths T.forget _ _ (meshRelation (T.zSigned k) _) = _
  rw [mapPaths_forget_meshRelation]
  simp
  rfl

end OrientedTree



end MultiplicativeBasisDeformations
