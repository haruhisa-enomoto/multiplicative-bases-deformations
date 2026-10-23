module

public import MultiplicativeBasisDeformations.Foundations.TreeRepetition
public import MultiplicativeBasisDeformations.Foundations.SectionalCover

/-!
# Transporting `ℤΔ` along a tree isomorphism

An isomorphism of trees `e : Δ₁ ≃ Δ₂` induces an isomorphism of their
repetitions in height coordinates, `(v, t) ↦ (e v, t + δ)`, where the constant
`δ` matches the two-colourings ("Changing the orientation of the tree changes its
repetition quiver only by the corresponding vertex shifts",
`periodic-mesh-calculations.tex`). It commutes with translation and
transports coverings.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Function

namespace MultiplicativeBasisDeformations

universe u v v' w

namespace OrientedTree

variable {D₁ : Type v} {D₂ : Type v'} (T₁ : OrientedTree D₁) (T₂ : OrientedTree D₂)
  (e : D₁ ≃ D₂) (he : ∀ a b, T₁.G.Adj a b ↔ T₂.G.Adj (e a) (e b))

include he in
/-- The two-colourings differ by a constant on a connected tree. -/
theorem exists_par_shift (hc : T₁.G.Connected) (d₀ : D₁) :
    ∀ d, T₂.par (e d) - T₁.par d = T₂.par (e d₀) - T₁.par d₀ := by
  intro d
  obtain ⟨p⟩ := hc.preconnected d₀ d
  induction p with
  | nil => rfl
  | cons h p ih =>
      rw [ih, T₁.par_adj h, T₂.par_adj ((he _ _).1 h)]
      ring

/-- The induced map on `ℤΔ`, for a matching shift `δ`. -/
def zMap (δ : ℤ) (hδ : ∀ d, T₂.par (e d) = T₁.par d + δ) (X : T₁.ZVert) : T₂.ZVert :=
  ⟨e X.v, X.t + δ, by push_cast; rw [X.ht, hδ]⟩

/-- The induced map on `ℤΔ`, inverse direction. -/
def zMapInv (δ : ℤ) (hδ : ∀ d, T₂.par (e d) = T₁.par d + δ) (Y : T₂.ZVert) : T₁.ZVert :=
  ⟨e.symm Y.v, Y.t - δ, by
    have := hδ (e.symm Y.v)
    rw [Equiv.apply_symm_apply] at this
    push_cast; rw [Y.ht, this]; ring⟩

/-- The isomorphism of repetitions. -/
def zEquiv (δ : ℤ) (hδ : ∀ d, T₂.par (e d) = T₁.par d + δ) : T₁.ZVert ≃ T₂.ZVert where
  toFun := zMap T₁ T₂ e δ hδ
  invFun := zMapInv T₁ T₂ e δ hδ
  left_inv X := by ext <;> simp [zMap, zMapInv]
  right_inv Y := by ext <;> simp [zMap, zMapInv]

include he in
theorem nonempty_hom_zMap_iff (δ : ℤ) (hδ : ∀ d, T₂.par (e d) = T₁.par d + δ)
    (X Y : T₁.ZVert) :
    Nonempty (zMap T₁ T₂ e δ hδ X ⟶ zMap T₁ T₂ e δ hδ Y) ↔ Nonempty (X ⟶ Y) := by
  constructor
  · rintro ⟨⟨h1, h2⟩⟩
    refine ⟨⟨(he _ _).2 h1, ?_⟩⟩
    simp only [zMap] at h2
    omega
  · rintro ⟨⟨h1, h2⟩⟩
    exact ⟨⟨(he _ _).1 h1, by simp only [zMap]; omega⟩⟩

end OrientedTree

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u₁ u₂ u₃ w₁ w₂ w₃

section CoveringTransport

variable {W₁ : Type u₁} [Quiver.{w₁} W₁] {W₂ : Type u₂} [Quiver.{w₂} W₂] {V : Type u₃}
  [Quiver.{w₃} V] [∀ x y : W₁, Subsingleton (x ⟶ y)] [∀ x y : W₂, Subsingleton (x ⟶ y)]
  [∀ x y : V, Subsingleton (x ⟶ y)]

/-- Coverings transport along isomorphisms of quivers with at most one arrow
between two vertices. -/
theorem isCovering_transport (f : W₁ ≃ W₂) (hf : ∀ X Y, Nonempty (f X ⟶ f Y) ↔ Nonempty (X ⟶ Y))
    (π : W₁ ⥤q V) (hπ : π.IsCovering) (π' : W₂ ⥤q V) (hobj : ∀ Y, π'.obj Y = π.obj (f.symm Y)) :
    π'.IsCovering := by
  have hf' : ∀ X Y, Nonempty (X ⟶ Y) ↔ Nonempty (f.symm X ⟶ f.symm Y) := fun X Y ↦ by
    rw [← hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨fun Y ↦ star_bijective_of π' ?_ ?_, fun Y ↦ costar_bijective_of π' ?_ ?_⟩
  · intro Z Z' hZ hZ' h
    rw [hobj, hobj] at h
    exact f.symm.injective (eq_of_star_bijective π (hπ.1 _) ((hf' _ _).1 hZ) ((hf' _ _).1 hZ') h)
  · intro y hy
    rw [hobj] at hy
    obtain ⟨Z, hZ, hZy⟩ := exists_of_star_bijective π (hπ.1 _) hy
    refine ⟨f Z, (hf' _ _).2 (by rwa [Equiv.symm_apply_apply]), ?_⟩
    rw [hobj, Equiv.symm_apply_apply, hZy]
  · intro Z Z' hZ hZ' h
    rw [hobj, hobj] at h
    have hc := hπ.2 (f.symm Y)
    obtain ⟨a⟩ := (hf' _ _).1 hZ
    obtain ⟨a'⟩ := (hf' _ _).1 hZ'
    have : π.costar (f.symm Y) ⟨f.symm Z, a⟩ = π.costar (f.symm Y) ⟨f.symm Z', a'⟩ := by
      simp only [Prefunctor.costar_apply]
      exact Sigma.ext h (Subsingleton.helim (congrArg (· ⟶ π.obj (f.symm Y)) h) _ _)
    exact f.symm.injective (congrArg Sigma.fst (hc.1 this))
  · intro y hy
    rw [hobj] at hy
    obtain ⟨Z, hZ, hZy⟩ := exists_of_costar_bijective π (hπ.2 _) hy
    refine ⟨f Z, (hf' _ _).2 (by rwa [Equiv.symm_apply_apply]), ?_⟩
    rw [hobj, Equiv.symm_apply_apply, hZy]

end CoveringTransport

end MultiplicativeBasisDeformations
