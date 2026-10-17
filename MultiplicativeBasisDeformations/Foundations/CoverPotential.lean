import MultiplicativeBasisDeformations.Foundations.DeckGrading

/-!
# Weights on the universal cover are ratios of object values

Lemma 4.13 (`scalar-normalization.tex`): "Assign `ν_X` to `t_X`. These
weights respect the triangles of `K̃`. Since this complex is simply connected,
multiplying along walks gives object values `ζ_X` with
`w(a) = ζ_{target(a)} / ζ_{source(a)}`."

A lifted vertex of `K̃` is a walk class `γ : v₀ → X` of the coned complex
(`lift`, `sheet`), and a weight assigns to each edge `e` and each lift `γ` of its
source a value `W e γ` in a group. Weights respecting the triangles define a
functor out of the fundamental groupoid into the semidirect groupoid `SD`
(morphisms: a walk class together with values along it). Its first component is
the identity (`Ψ_fst`, "simply connected"), and its values along walks from the
basepoint are the object values: `pot (γ ≫ e) = pot γ · W e γ` (`pot_comp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

universe w

variable {V : Type} [Quiver.{0} V] (Q : TranslationQuiver V) (v₀ : V) (K : Type w) [CommGroup K]

/-- The objects of the semidirect groupoid. -/
@[nolint unusedArguments]
def SD (_Q : TranslationQuiver V) (_v₀ : V) (_K : Type w) : Type := V

instance : Groupoid (SD Q v₀ K) where
  Hom A B := (obC Q v₀ A ⟶ obC Q v₀ B) × ((obC Q v₀ v₀ ⟶ obC Q v₀ A) → K)
  id A := (𝟙 _, fun _ ↦ 1)
  comp f g := (f.1 ≫ g.1, fun γ ↦ f.2 γ * g.2 (γ ≫ f.1))
  id_comp f := Prod.ext (Category.id_comp _) (funext fun γ ↦ by simp)
  comp_id f := Prod.ext (Category.comp_id _) (funext fun γ ↦ by simp)
  assoc f g h := Prod.ext (Category.assoc _ _ _) (funext fun γ ↦ by simp [mul_assoc])
  inv f := (Groupoid.inv f.1, fun γ ↦ (f.2 (γ ≫ Groupoid.inv f.1))⁻¹)
  inv_comp f := Prod.ext (Groupoid.inv_comp _) (funext fun γ ↦ by
    change (f.2 (γ ≫ Groupoid.inv f.1))⁻¹ * f.2 (γ ≫ Groupoid.inv f.1) = 1
    exact inv_mul_cancel _)
  comp_inv f := Prod.ext (Groupoid.comp_inv _) (funext fun γ ↦ by
    change f.2 γ * (f.2 ((γ ≫ f.1) ≫ Groupoid.inv f.1))⁻¹ = 1
    rw [Category.assoc, Groupoid.comp_inv, Category.comp_id, mul_inv_cancel])

theorem SD_comp_fst {A B C : SD Q v₀ K} (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

theorem SD_comp_snd {A B C : SD Q v₀ K} (f : A ⟶ B) (g : B ⟶ C) (γ) :
    (f ≫ g).2 γ = f.2 γ * g.2 (γ ≫ f.1) := rfl

/-- A vertex as an object of the semidirect groupoid. -/
def toSD (X : V) : SD Q v₀ K := X

/-- The projection to the fundamental groupoid. -/
def prj : SD Q v₀ K ⥤ PiC Q v₀ where
  obj A := obC Q v₀ A
  map f := f.1
  map_id _ := rfl
  map_comp _ _ := rfl

variable {Q v₀ K}

variable (W : ∀ e : Ed Q ⊕ V, (obC Q v₀ v₀ ⟶ obC Q v₀ (srcC Q v₀ e)) → K)
  (hW : ∀ (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) (γ : obC Q v₀ v₀ ⟶ obC Q v₀ (Q.tau x).1),
    W (Sum.inl (Sum.inl ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)) γ *
      W (Sum.inl (Sum.inl ⟨a.1, x.1, a.2⟩)) (γ ≫ arrC Q v₀ (Q.mate x a.1 a.2)) =
    W (Sum.inl (Sum.inr x)) γ)

include hW in
/-- **The transport functor** of a weight respecting the triangles. -/
def Ψ : PiC Q v₀ ⥤ SD Q v₀ K :=
  Morse.liftEdges (coneTris Q v₀) (toSD Q v₀ K) (fun e ↦ (edgeC Q v₀ e, W e)) (by
    rintro ⟨x, y, a⟩
    refine Prod.ext ?_ (funext fun γ ↦ ?_)
    · change arrC Q v₀ (Q.mate x y a) ≫ 𝟙 _ ≫ arrC Q v₀ a = 𝟙 _ ≫ tC Q v₀ x ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      exact tri_rel Q v₀ x ⟨y, a⟩
    · change W (Sum.inl (Sum.inl ⟨(Q.tau x).1, y, Q.mate x y a⟩)) γ *
          (1 * W (Sum.inl (Sum.inl ⟨y, x.1, a⟩)) ((γ ≫ arrC Q v₀ (Q.mate x y a)) ≫ 𝟙 _)) =
        1 * (W (Sum.inl (Sum.inr x)) (γ ≫ 𝟙 _) * 1)
      simp only [one_mul, mul_one]
      erw [Category.comp_id, Category.comp_id]
      exact hW x ⟨y, a⟩ γ)

theorem Ψ_edge (e : Ed Q ⊕ V) : (Ψ W hW).map (edgeC Q v₀ e) = (edgeC Q v₀ e, W e) :=
  Morse.liftEdges_edge _ _ _ _ e

/-- **Simple connectivity**: the walk component of the transport is the walk. -/
theorem Ψ_prj : Ψ W hW ⋙ prj Q v₀ K = 𝟭 (PiC Q v₀) := by
  set S := coneTris Q v₀
  have e1 : Morse.Qf (S := S) ⋙ Ψ W hW ⋙ prj Q v₀ K = Quiver.FreeGroupoid.lift
      (Quiver.FreeGroupoid.of (Morse.EQ (srcC Q v₀) (tgtC Q)) ⋙q
        (Morse.Qf (S := S)).toPrefunctor) := by
    apply Quiver.FreeGroupoid.lift_unique
    refine Prefunctor.ext (fun X ↦ rfl) fun X Y a ↦ ?_
    obtain ⟨e, hs, ht⟩ := a
    subst hs ht
    change ((Ψ W hW).map (edgeC Q v₀ e)).1 = edgeC Q v₀ e
    rw [Ψ_edge]
  have e2 : Morse.Qf (S := S) = Quiver.FreeGroupoid.lift
      (Quiver.FreeGroupoid.of (Morse.EQ (srcC Q v₀) (tgtC Q)) ⋙q
        (Morse.Qf (S := S)).toPrefunctor) := by
    apply Quiver.FreeGroupoid.lift_unique
    rfl
  have h1 := CategoryTheory.Quotient.lift_unique (Morse.TriRel S)
    (Morse.Qf (S := S) ⋙ Ψ W hW ⋙ prj Q v₀ K)
    (fun X Y f₁ f₂ h ↦ by
      simp only [Functor.comp_map]
      rw [CategoryTheory.Quotient.sound _ h]) (Ψ W hW ⋙ prj Q v₀ K) rfl
  have h2 := CategoryTheory.Quotient.lift_unique (Morse.TriRel S) (Morse.Qf (S := S))
    (fun X Y f₁ f₂ h ↦ CategoryTheory.Quotient.sound _ h) (𝟭 (PiC Q v₀)) (Functor.comp_id _)
  rw [h1, h2]
  congr 1
  rw [e1, ← e2]

theorem Ψ_fst {A B : V} (π : obC Q v₀ A ⟶ obC Q v₀ B) : ((Ψ W hW).map π).1 = π := by
  have := Functor.congr_hom (Ψ_prj W hW) π
  change ((Ψ W hW).map π).1 = eqToHom rfl ≫ π ≫ eqToHom rfl at this
  simpa using this

/-- **The object values**: the transport along a walk from the basepoint. -/
def potW {X : V} (γ : obC Q v₀ v₀ ⟶ obC Q v₀ X) : K := ((Ψ W hW).map γ).2 (𝟙 _)

theorem potW_comp (e : Ed Q ⊕ V) (γ : obC Q v₀ v₀ ⟶ obC Q v₀ (srcC Q v₀ e)) :
    potW W hW (γ ≫ edgeC Q v₀ e) = potW W hW γ * W e γ := by
  unfold potW
  rw [Functor.map_comp]
  change ((Ψ W hW).map γ).2 (𝟙 _) * ((Ψ W hW).map (edgeC Q v₀ e)).2 (𝟙 _ ≫ ((Ψ W hW).map γ).1) = _
  rw [Ψ_edge]
  have h1 : (𝟙 _ ≫ ((Ψ W hW).map γ).1 : obC Q v₀ v₀ ⟶ obC Q v₀ (srcC Q v₀ e)) = γ :=
    (Category.id_comp _).trans (Ψ_fst W hW γ)
  exact congrArg (fun z ↦ ((Ψ W hW).map γ).2 (𝟙 _) * W e z) h1

end MeshWalk

end MultiplicativeBasisDeformations
