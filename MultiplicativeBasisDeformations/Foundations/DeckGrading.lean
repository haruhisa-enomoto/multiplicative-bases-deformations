import MultiplicativeBasisDeformations.Foundations.PeriodicDepth
import MultiplicativeBasisDeformations.Foundations.WeightGrading

/-!
# The deck group and the walk-class grading

Subsection 4.2 (`subsec:universal-cover`, `scalar-normalization.tex:182–236`):
"Let `K̃` be the universal cover of `K`, constructed from walks starting at a
basepoint, modulo edge cancellation and the triangle relations. The fundamental
group `G` acts on this cover by deck transformations." A lifted vertex is a
vertex `X` with the class of a walk from the basepoint; a path of `Γ` lifts
uniquely from a chosen lift of its source.

Formally we fix a basepoint `v₀` and adjoin to `K` a cone of edges
`s_X : v₀ → X` without triangles. This makes the complex connected without
changing the argument (the source assumes `A` connected; with the cone, the
cover is a disjoint union of universal covers of the components of `K`, and
`G` is still free by the collapse of Lemma 4.2). The lift `(X, h)` of `X` in
sheet `h ∈ G` is the walk class `h · s_X`; a path `p : X → Y` lifts from sheet
`h` to sheet `h · deg p`, where `deg p = s_X p s_Y⁻¹` (`degW`). Mesh relations
are homogeneous for `deg` (their terms are homotopic to `t_X`), so `deg`
grades `C(Q, c)` (`WeightGrading.lean`): this is the covering formula
`eq:walk-hom-sum`. Edges have length one, translation edges length two and
cone edges length zero; triangles preserve length, so length is a
homomorphism `ℓ : G → ℤ` with `ℓ (deg p) = |p|` (`len_degW`); this is the
height of the source.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace Morse

variable {V Ed E : Type} {src tgt : Ed → V} (S : Tris src tgt) (srcE tgtE : E → V)

/-- The complex with additional edges and the same triangles. -/
def Tris.ext : Tris (Sum.elim src srcE) (Sum.elim tgt tgtE) where
  T := S.T
  f t := Sum.inl (S.f t)
  g t := Sum.inl (S.g t)
  h t := Sum.inl (S.h t)
  hfg t := S.hfg t
  hfh t := S.hfh t
  hgh t := S.hgh t

theorem Tris.ext_edge (t : S.T) (i : Fin 3) :
    (S.ext srcE tgtE).edge t i = Sum.inl (S.edge t i) := by
  fin_cases i <;> rfl

variable {S}

/-- A matching extends to the complex with additional edges. -/
def Matching.ext (M : Matching S) : Matching (S.ext srcE tgtE) where
  m := M.m
  inj t t' h := M.inj (Sum.inl_injective ((S.ext_edge srcE tgtE t (M.m t)).symm.trans
    (h.trans (S.ext_edge srcE tgtE t' (M.m t')))))
  pot := M.pot
  dec t i hi t' h := M.dec t i hi t' (Sum.inl_injective ((S.ext_edge srcE tgtE t' (M.m t')).symm.trans
    (h.trans (S.ext_edge srcE tgtE t i))))

section LiftEdges

variable {V Ed : Type} {src tgt : Ed → V} (S : Tris src tgt) {D : Type*} [Groupoid D]
  (obj : V → D) (val : ∀ e, obj (src e) ⟶ obj (tgt e))

/-- The prefunctor on edges given by values in a groupoid. -/
def edgesP : EQ src tgt ⥤q D where
  obj := obj
  map {X Y} e := eqToHom (congrArg obj e.2.1.symm) ≫ val e.1 ≫ eqToHom (congrArg obj e.2.2)

/-- **A functor out of the fundamental groupoid**, from values on edges that
respect the triangles. -/
def liftEdges (hrel : ∀ t, val (S.f t) ≫ eqToHom (congrArg obj (S.hfg t)) ≫ val (S.g t) =
    eqToHom (congrArg obj (S.hfh t)) ≫ val (S.h t) ≫ eqToHom (congrArg obj (S.hgh t).symm)) :
    Pi S ⥤ D :=
  CategoryTheory.Quotient.lift _ (Quiver.FreeGroupoid.lift (edgesP obj val)) (by
    have h1 : ∀ e, (Quiver.FreeGroupoid.lift (edgesP obj val)).map (ofE src tgt e) = val e := by
      intro e
      have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (edgesP obj val))
        (show @Quiver.Hom (EQ src tgt) _ (src e) (tgt e) from ⟨e, rfl, rfl⟩)
      have h' := eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
      refine h'.trans ?_
      simp [edgesP]
      rfl
    rintro _ _ _ _ ⟨t⟩
    simp only [Functor.map_comp, eqToHom_map, h1]
    exact hrel t)

theorem liftEdges_obj (hrel) (X : V) :
    (liftEdges S obj val hrel).obj ((Qf (S := S)).obj (ob src tgt X)) = obj X := rfl

theorem liftEdges_edge (hrel) (e : Ed) :
    (liftEdges S obj val hrel).map ((Qf (S := S)).map (ofE src tgt e)) = val e := by
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (edgesP obj val))
    (show @Quiver.Hom (EQ src tgt) _ (src e) (tgt e) from ⟨e, rfl, rfl⟩)
  have h' := eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
  refine h'.trans ?_
  simp [edgesP]
  rfl

end LiftEdges

end Morse

namespace MeshWalk

variable {V : Type} [Quiver.{0} V] (Q : TranslationQuiver V) (v₀ : V)

/-- The source of an edge of the coned complex. -/
abbrev srcC : Ed Q ⊕ V → V := Sum.elim (src Q) (fun _ ↦ v₀)

/-- The target of an edge of the coned complex. -/
abbrev tgtC : Ed Q ⊕ V → V := Sum.elim (tgt Q) id

/-- The complex `K` with a cone of edges `s_X : v₀ → X`. -/
def coneTris : Morse.Tris (srcC Q v₀) (tgtC Q) := (meshTris Q).ext _ _

/-- Its fundamental groupoid. -/
abbrev PiC := Morse.Pi (coneTris Q v₀)

/-- A vertex as an object of `PiC`. -/
abbrev obC (X : V) : PiC Q v₀ :=
  (Morse.Qf (S := coneTris Q v₀)).obj (Morse.ob (srcC Q v₀) (tgtC Q) X)

/-- The class of an edge. -/
def edgeC (e : Ed Q ⊕ V) : obC Q v₀ (srcC Q v₀ e) ⟶ obC Q v₀ (tgtC Q e) :=
  (Morse.Qf (S := coneTris Q v₀)).map (Morse.ofE (srcC Q v₀) (tgtC Q) e)

/-- The class of an arrow. -/
def arrC {y x : V} (a : y ⟶ x) : obC Q v₀ y ⟶ obC Q v₀ x :=
  edgeC Q v₀ (Sum.inl (Sum.inl ⟨y, x, a⟩))

/-- The class of a translation edge `t_x : τ x → x`. -/
def tC (x : Q.nonprojective) : obC Q v₀ (Q.tau x).1 ⟶ obC Q v₀ x.1 :=
  edgeC Q v₀ (Sum.inl (Sum.inr x))

/-- The class of a cone edge `s_X : v₀ → X`. -/
def coneC (X : V) : obC Q v₀ v₀ ⟶ obC Q v₀ X := edgeC Q v₀ (Sum.inr X)

/-- The class of a path. -/
def pathC : ∀ {x y : V}, Quiver.Path x y → (obC Q v₀ x ⟶ obC Q v₀ y)
  | _, _, Quiver.Path.nil => 𝟙 _
  | _, _, Quiver.Path.cons p a => pathC p ≫ arrC Q v₀ a

theorem pathC_comp {x y z : V} (p : Quiver.Path x y) :
    ∀ q : Quiver.Path y z, pathC Q v₀ (p.comp q) = pathC Q v₀ p ≫ pathC Q v₀ q
  | Quiver.Path.nil => by simp [pathC]
  | Quiver.Path.cons q a => by
      simp only [Quiver.Path.comp_cons, pathC]
      rw [pathC_comp p q, Category.assoc]

theorem pathC_toPath {x y : V} (a : x ⟶ y) : pathC Q v₀ a.toPath = arrC Q v₀ a := by
  change pathC Q v₀ (Quiver.Path.cons Quiver.Path.nil a) = _
  simp only [pathC, Category.id_comp]

/-- **The mesh triangles**: `(σ a) a = t_x` in the fundamental groupoid. -/
theorem tri_rel (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) :
    arrC Q v₀ (Q.mate x a.1 a.2) ≫ arrC Q v₀ a.2 = tC Q v₀ x := by
  have h := Morse.Q_rel (S := coneTris Q v₀) (⟨x, a.1, a.2⟩ : Tri Q)
  have h' : arrC Q v₀ (Q.mate x a.1 a.2) ≫ 𝟙 _ ≫ arrC Q v₀ a.2 = 𝟙 _ ≫ tC Q v₀ x ≫ 𝟙 _ := h
  simpa using h'

/-- The deck group: loops at the basepoint, multiplied in walk order. -/
abbrev Deck := (End (obC Q v₀ v₀))ᵐᵒᵖ

/-- **The walk-class weight** `deg p = s_X p s_Y⁻¹`. -/
def degW : PathWeight V (Deck Q v₀) where
  deg {x y} p := MulOpposite.op (coneC Q v₀ x ≫ pathC Q v₀ p ≫ Groupoid.inv (coneC Q v₀ y))
  deg_nil x := by
    apply MulOpposite.unop_injective
    simp [pathC, End.one_def]
  deg_comp {x y z} p q := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul, End.mul_def, pathC_comp,
      Category.assoc]
    rw [← Category.assoc (Groupoid.inv (coneC Q v₀ y)) (coneC Q v₀ y), Groupoid.inv_comp,
      Category.id_comp]

theorem degW_deg {x y : V} (p : Quiver.Path x y) :
    (degW Q v₀).deg p =
      MulOpposite.op (coneC Q v₀ x ≫ pathC Q v₀ p ≫ Groupoid.inv (coneC Q v₀ y)) := rfl

/-- The mesh relations are homogeneous for the walk-class weight. -/
theorem meshHomogeneous : ScalarMeshCategory.MeshHomogeneous (Q := Q) (degW Q v₀) := by
  intro x a b
  rw [degW_deg, degW_deg, pathC_comp, pathC_comp, pathC_toPath, pathC_toPath, pathC_toPath,
    pathC_toPath, tri_rel, tri_rel]

/-! ### Freeness of the deck group -/

section Free

variable [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {k : Type*} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k
    (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

include hfin in
/-- **The deck group is free** (Lemma 4.2, for the coned complex). -/
theorem isFreeGroup_deck : IsFreeGroup (Deck Q v₀) :=
  have : IsFreeGroup (End (obC Q v₀ v₀)) :=
    Morse.isFreeGroup_end ((meshMatching (meshDepth c hfin)).ext (fun _ : V ↦ v₀) id) v₀
  IsFreeGroup.ofMulEquiv (MulEquiv.inv' (End (obC Q v₀ v₀)))

end Free

/-! ### Length -/

/-- Lengths of edges: one for arrows, two for translation edges, zero for cone
edges. -/
def lenE : Ed Q ⊕ V → ℤ
  | Sum.inl (Sum.inl _) => 1
  | Sum.inl (Sum.inr _) => 2
  | Sum.inr _ => 0

/-- The length functor on the fundamental groupoid. -/
def lenF : PiC Q v₀ ⥤ SingleObj (Multiplicative ℤ) :=
  Morse.liftEdges (coneTris Q v₀) (fun _ ↦ SingleObj.star _)
    (fun e ↦ (Multiplicative.ofAdd (lenE Q e) : Multiplicative ℤ)) (by
      intro t
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id, SingleObj.comp_as_mul]
      rw [← ofAdd_add]
      rfl)

theorem lenF_edge (e : Ed Q ⊕ V) :
    (lenF Q v₀).map (edgeC Q v₀ e) = Multiplicative.ofAdd (lenE Q e) :=
  Morse.liftEdges_edge _ _ _ _ e

theorem lenF_arrC {x y : V} (a : x ⟶ y) :
    (lenF Q v₀).map (arrC Q v₀ a) = Multiplicative.ofAdd 1 :=
  lenF_edge Q v₀ (Sum.inl (Sum.inl ⟨x, y, a⟩))

theorem lenF_coneC (X : V) : (lenF Q v₀).map (coneC Q v₀ X) = Multiplicative.ofAdd 0 :=
  lenF_edge Q v₀ (Sum.inr X)

theorem lenF_pathC {x y : V} : ∀ p : Quiver.Path x y,
    (lenF Q v₀).map (pathC Q v₀ p) = Multiplicative.ofAdd (p.length : ℤ)
  | Quiver.Path.nil => by
      simp only [pathC, CategoryTheory.Functor.map_id, Quiver.Path.length_nil, Nat.cast_zero,
        ofAdd_zero]
      rfl
  | Quiver.Path.cons p a => by
      rw [pathC, Functor.map_comp, lenF_pathC p, lenF_arrC, SingleObj.comp_as_mul,
        ← ofAdd_add]
      simp [add_comm]

/-- The length homomorphism `ℓ : G → ℤ`. -/
def hgt (g : Deck Q v₀) : ℤ := Multiplicative.toAdd ((lenF Q v₀).map g.unop)

theorem hgt_mul (g h : Deck Q v₀) : hgt Q v₀ (g * h) = hgt Q v₀ g + hgt Q v₀ h := by
  simp only [hgt, MulOpposite.unop_mul, End.mul_def, Functor.map_comp, SingleObj.comp_as_mul]
  rw [toAdd_mul, add_comm]

theorem hgt_one : hgt Q v₀ 1 = 0 := by
  simp only [hgt, MulOpposite.unop_one, End.one_def, CategoryTheory.Functor.map_id,
    SingleObj.id_as_one, toAdd_one]

/-- **Height**: the length of a path is the length of its walk class. -/
theorem hgt_degW {x y : V} (p : Quiver.Path x y) : hgt Q v₀ ((degW Q v₀).deg p) = p.length := by
  have hinv : (lenF Q v₀).map (Groupoid.inv (coneC Q v₀ y)) = Multiplicative.ofAdd 0 := by
    have e1 : (lenF Q v₀).map (Groupoid.inv (coneC Q v₀ y)) =
        Groupoid.inv ((lenF Q v₀).map (coneC Q v₀ y)) := by
      rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Functor.map_inv]
    rw [e1, lenF_coneC, Groupoid.inv_eq_inv, SingleObj.inv_as_inv, ofAdd_zero]
    exact inv_one (G := Multiplicative ℤ)
  simp only [hgt, degW_deg, MulOpposite.unop_op, Functor.map_comp, hinv, lenF_pathC, lenF_coneC,
    SingleObj.comp_as_mul, ofAdd_zero]
  have e : ((1 : Multiplicative ℤ) * Multiplicative.ofAdd (p.length : ℤ) * 1) =
      Multiplicative.ofAdd (p.length : ℤ) := by simp
  exact (congrArg Multiplicative.toAdd e).trans (toAdd_ofAdd _)

end MeshWalk

end MultiplicativeBasisDeformations
