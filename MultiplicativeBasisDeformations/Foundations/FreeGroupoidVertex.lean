import Mathlib

/-!
# Vertex groups of free groupoids are free

The last step of Lemma 4.2 (`lem:mesh-walk-free`, `scalar-normalization.tex`):
"Contracting spanning trees gives a graph. Its edges outside a spanning tree
freely generate the fundamental group." Mathlib proves this for a connected
free groupoid (`IsFreeGroupoid.endIsFreeOfConnectedFree`, by a spanning tree).
Here the free groupoid on any quiver is shown to be free in Mathlib's sense, and
the vertex group at `X₀` is identified with the vertex group of the free
groupoid on the connected component of `X₀`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.FreeVertex

universe u

/-- The free groupoid on a quiver is a free groupoid. -/
instance isFreeGroupoid (W : Type u) [Quiver.{u} W] :
    IsFreeGroupoid (Quiver.FreeGroupoid W) where
  quiverGenerators := ⟨fun a b ↦ (show W from a.as) ⟶ b.as⟩
  of g := (Quiver.FreeGroupoid.of W).map g
  unique_lift {X} _ f := by
    let φ : W ⥤q SingleObj X :=
      { obj := fun _ ↦ SingleObj.star X
        map := fun {a b} e ↦ @f ⟨a⟩ ⟨b⟩ e }
    refine ⟨Quiver.FreeGroupoid.lift φ, fun a b g ↦ ?_, fun F hF ↦ ?_⟩
    · have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ) g
      exact eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
    · apply Quiver.FreeGroupoid.lift_unique
      refine Prefunctor.ext (fun _ ↦ rfl) fun a b g ↦ ?_
      exact hF ⟨a⟩ ⟨b⟩ g

variable {U : Type u} [Quiver.{u} U]

/-- Reachability by zigzags of arrows. -/
def Reach (X Y : U) : Prop := Relation.EqvGen (fun a b : U ↦ Nonempty (a ⟶ b)) X Y

/-- The connected component of `X₀`, as a full subquiver. -/
def Comp (X₀ : U) : Type u := {Y : U // Reach X₀ Y}

instance (X₀ : U) : Quiver.{u} (Comp X₀) where
  Hom Y Z := Y.1 ⟶ Z.1

variable (X₀ : U)

/-- The base point of the component. -/
def base : Comp X₀ := ⟨X₀, Relation.EqvGen.refl _⟩

theorem reach_of_hom {Y Z : U} (hY : Reach X₀ Y) (_ : Y ⟶ Z) : Reach X₀ Z :=
  Relation.EqvGen.trans _ _ _ hY (Relation.EqvGen.rel _ _ ⟨‹_›⟩)

theorem reach_of_hom' {Y Z : U} (hZ : Reach X₀ Z) (_ : Y ⟶ Z) : Reach X₀ Y :=
  Relation.EqvGen.trans _ _ _ hZ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨‹_›⟩))

/-- The inclusion of the component. -/
def incl : Comp X₀ ⥤q U where
  obj Y := Y.1
  map e := e

/-- The induced functor of free groupoids. -/
def ι : Quiver.FreeGroupoid (Comp X₀) ⥤ Quiver.FreeGroupoid U :=
  Quiver.freeGroupoidFunctor (incl X₀)

abbrev obC (Y : Comp X₀) : Quiver.FreeGroupoid (Comp X₀) := (Quiver.FreeGroupoid.of _).obj Y

theorem ι_of {Y Z : Comp X₀} (e : Y ⟶ Z) :
    (ι X₀).map ((Quiver.FreeGroupoid.of _).map e) =
      (Quiver.FreeGroupoid.of U).map (show Y.1 ⟶ Z.1 from e) := by
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec
    (incl X₀ ⋙q Quiver.FreeGroupoid.of U)) e
  exact eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))

/-- The component is connected. -/
theorem nonempty_hom (Y Z : U) (h : Relation.EqvGen (fun a b : U ↦ Nonempty (a ⟶ b)) Y Z)
    (hY : Reach X₀ Y) :
    Nonempty (obC X₀ ⟨Y, hY⟩ ⟶ obC X₀ ⟨Z, Relation.EqvGen.trans _ _ _ hY h⟩) := by
  induction h with
  | rel a b e =>
      obtain ⟨e⟩ := e
      exact ⟨(Quiver.FreeGroupoid.of (Comp X₀)).map
        (show (⟨a, hY⟩ : Comp X₀).1 ⟶ (⟨b, _⟩ : Comp X₀).1 from e)⟩
  | refl a => exact ⟨𝟙 _⟩
  | symm a b h ih =>
      obtain ⟨g⟩ := ih (Relation.EqvGen.trans _ _ _ hY (Relation.EqvGen.symm _ _ h))
      exact ⟨Groupoid.inv g⟩
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      obtain ⟨g₁⟩ := ih₁ hY
      obtain ⟨g₂⟩ := ih₂ (Relation.EqvGen.trans _ _ _ hY h₁)
      exact ⟨g₁ ≫ g₂⟩

instance isConnected : IsConnected (Quiver.FreeGroupoid (Comp X₀)) := by
  have : Nonempty (Quiver.FreeGroupoid (Comp X₀)) := ⟨obC X₀ (base X₀)⟩
  have hb : ∀ Y : Quiver.FreeGroupoid (Comp X₀), Nonempty (obC X₀ (base X₀) ⟶ Y) := by
    rintro ⟨⟨Y, hY⟩⟩
    exact nonempty_hom X₀ X₀ Y hY (Relation.EqvGen.refl _)
  refine zigzag_isConnected fun a b ↦ ?_
  obtain ⟨f⟩ := hb a
  obtain ⟨g⟩ := hb b
  exact Relation.ReflTransGen.single (Or.inl ⟨Groupoid.inv f ≫ g⟩)

/-! ### Injectivity: conjugating back to the base point -/

/-- Chosen morphisms from the base point. -/
def γ (Y : Comp X₀) : obC X₀ (base X₀) ⟶ obC X₀ Y :=
  Classical.choice (nonempty_hom X₀ X₀ Y.1 Y.2 (Relation.EqvGen.refl _))

/-- The vertex group at the base point. -/
abbrev E := End (obC X₀ (base X₀))

/-- The underlying vertex of an object. -/
def pt (Y : Quiver.FreeGroupoid (Comp X₀)) : Comp X₀ := Y.as

/-- `γ` on objects of the free groupoid. -/
def γ' (Y : Quiver.FreeGroupoid (Comp X₀)) : obC X₀ (base X₀) ⟶ Y := γ X₀ (pt X₀ Y)

/-- Conjugation to the base point, as a functor to the vertex group. -/
def conj : Quiver.FreeGroupoid (Comp X₀) ⥤ SingleObj (E X₀) where
  obj _ := SingleObj.star _
  map {Y Z} g := (show E X₀ from γ' X₀ Y ≫ g ≫ Groupoid.inv (γ' X₀ Z))
  map_id Y := by
    change γ' X₀ Y ≫ 𝟙 _ ≫ Groupoid.inv (γ' X₀ Y) = 𝟙 _
    simp
  map_comp {Y Z W} f g := by
    rw [SingleObj.comp_as_mul]
    change γ' X₀ Y ≫ (f ≫ g) ≫ Groupoid.inv (γ' X₀ W) =
      (γ' X₀ Y ≫ f ≫ Groupoid.inv (γ' X₀ Z)) ≫ (γ' X₀ Z ≫ g ≫ Groupoid.inv (γ' X₀ W))
    simp

/-- A vertex of the component. -/
def mk (Y : U) (h : Reach X₀ Y) : Comp X₀ := ⟨Y, h⟩

open scoped Classical in
/-- The labelling of the arrows of `U` by conjugated loops. -/
def lab : U ⥤q SingleObj (E X₀) where
  obj _ := SingleObj.star _
  map {Y Z} a := if h : Reach X₀ Y then
      (show E X₀ from γ X₀ (mk X₀ Y h) ≫ (Quiver.FreeGroupoid.of (Comp X₀)).map
        (show mk X₀ Y h ⟶ mk X₀ Z (reach_of_hom X₀ h a) from a) ≫
          Groupoid.inv (γ X₀ (mk X₀ Z (reach_of_hom X₀ h a))))
    else 1

/-- The functor `F` of the labelling. -/
def F : Quiver.FreeGroupoid U ⥤ SingleObj (E X₀) := Quiver.FreeGroupoid.lift (lab X₀)

theorem ι_F : ι X₀ ⋙ F X₀ = conj X₀ := by
  apply IsFreeGroupoid.ext_functor
  intro a b e
  let a' : Comp X₀ := a.as
  let b' : Comp X₀ := b.as
  let e' : a' ⟶ b' := e
  change (F X₀).map ((ι X₀).map ((Quiver.FreeGroupoid.of (Comp X₀)).map e')) =
    (conj X₀).map ((Quiver.FreeGroupoid.of (Comp X₀)).map e')
  rw [ι_of]
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (lab X₀))
    (show a'.1 ⟶ b'.1 from e')
  have h' := eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
  refine h'.trans ?_
  simp only [lab, dif_pos a'.2]
  rfl

theorem ι_injective {f g : obC X₀ (base X₀) ⟶ obC X₀ (base X₀)}
    (h : (ι X₀).map f = (ι X₀).map g) : f = g := by
  have hf := Functor.congr_hom (ι_F X₀) f
  have hg := Functor.congr_hom (ι_F X₀) g
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [h, hg] at hf
  change γ' X₀ _ ≫ g ≫ Groupoid.inv (γ' X₀ _) = γ' X₀ _ ≫ f ≫ Groupoid.inv (γ' X₀ _) at hf
  rw [Groupoid.inv_eq_inv] at hf
  exact ((cancel_mono (inv _)).1 ((cancel_epi _).1 hf)).symm

/-! ### Surjectivity: walks from the component stay in it -/

/-- The class of a walk in the free groupoid. -/
abbrev cls {Y Z : U} (p : Quiver.Path (show Quiver.Symmetrify U from Y) Z) :
    (Quiver.FreeGroupoid.of U).obj Y ⟶ (Quiver.FreeGroupoid.of U).obj Z :=
  (CategoryTheory.Quotient.functor Quiver.FreeGroupoid.redStep).map
    (show (Paths.of (Quiver.Symmetrify U)).obj Y ⟶ (Paths.of (Quiver.Symmetrify U)).obj Z from p)

theorem surj_aux {Y : U} (hY : Reach X₀ Y) : ∀ {Z : U}
    (p : Quiver.Path (show Quiver.Symmetrify U from Y) Z),
    ∃ (hZ : Reach X₀ Z) (g : obC X₀ (mk X₀ Y hY) ⟶ obC X₀ (mk X₀ Z hZ)), (ι X₀).map g = cls p
  | _, Quiver.Path.nil => ⟨hY, 𝟙 _, by rw [CategoryTheory.Functor.map_id]; rfl⟩
  | _, Quiver.Path.cons p e => by
      obtain ⟨hW, g, hg⟩ := surj_aux hY p
      rcases e with a | a
      · refine ⟨reach_of_hom X₀ hW a, g ≫ (Quiver.FreeGroupoid.of (Comp X₀)).map
          (show mk X₀ _ hW ⟶ mk X₀ _ (reach_of_hom X₀ hW a) from a), ?_⟩
        rw [Functor.map_comp, hg, ι_of]
        rfl
      · refine ⟨reach_of_hom' X₀ hW a, g ≫ Groupoid.inv ((Quiver.FreeGroupoid.of (Comp X₀)).map
          (show mk X₀ _ (reach_of_hom' X₀ hW a) ⟶ mk X₀ _ hW from a)), ?_⟩
        have hinv : ∀ {A B : Quiver.FreeGroupoid (Comp X₀)} (x : A ⟶ B),
            (ι X₀).map (Groupoid.inv x) = Groupoid.inv ((ι X₀).map x) := by
          intro A B x
          rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Functor.map_inv]
        rw [Functor.map_comp, hg, hinv, ι_of]
        rfl

theorem ι_surjective (g : (Quiver.FreeGroupoid.of U).obj X₀ ⟶ (Quiver.FreeGroupoid.of U).obj X₀) :
    ∃ f : obC X₀ (base X₀) ⟶ obC X₀ (base X₀), (ι X₀).map f = g := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep g
  obtain ⟨_, f, hf⟩ := surj_aux X₀ (Relation.EqvGen.refl X₀) p
  exact ⟨f, hf⟩

/-- **Vertex groups of free groupoids are free** (the spanning-tree step of
Lemma 4.2). -/
theorem isFreeGroup_end (X₀ : U) : IsFreeGroup (End ((Quiver.FreeGroupoid.of U).obj X₀)) := by
  have : IsFreeGroup (End (obC X₀ (base X₀))) :=
    IsFreeGroupoid.endIsFreeOfConnectedFree _
  let φ : End (obC X₀ (base X₀)) →* End ((Quiver.FreeGroupoid.of U).obj X₀) :=
    (ι X₀).mapEnd _
  have hφ : Function.Bijective φ :=
    ⟨fun f g h ↦ ι_injective X₀ h, fun g ↦ ι_surjective X₀ g⟩
  exact IsFreeGroup.ofMulEquiv (MulEquiv.ofBijective φ hφ)

end MultiplicativeBasisDeformations.FreeVertex
