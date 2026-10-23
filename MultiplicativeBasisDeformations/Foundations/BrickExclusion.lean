module

public import MultiplicativeBasisDeformations.Foundations.DeletionTransfer

/-!
# Excluding periods by the brick hypothesis

Appendix A (`periodic-mesh-calculations.tex`): "Delete all lifts
of the two outer vertices of the long arms. The retained vertices are closed
under translation, and (5.2) identifies the object quotient with the `D₄` mesh
category of the same period. Its degree-four closed paths … remain nonzero, so
it has no brick." In general: if every retained vertex carries a closed path
whose lift is nonzero in `Π(Δ)` modulo the deleted vertices, then every
retained object of the object quotient has a nonzero radical endomorphism
besides the identity, and the brick hypothesis fails for that quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v v' w

open ScalarMeshCategory

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D) [Fintype D] [DecidableEq D] [DecidableRel T.orient]
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))

include hπ hτ in
/-- **No brick after deletion.** Let `D` be a set of vertices of `Q` whose lifts
lie over the deleted vertices `Del` of `Δ`. If every lift `X` of a retained
vertex starts a path `P` to another lift `E` of the same vertex such that the
image of `P` in `Π(Δ)` modulo `Del` is nonzero (and `e_X` is nonzero there),
then the brick hypothesis fails. -/
theorem not_brick (Dset : Set V) (Del : Set T.Dbl)
    (hD : ∀ Z : T.ZVert, π.obj Z ∈ Dset → T.toDbl Z.v ∈ Del)
    (hsurj : ∀ x : V, ∃ X, π.obj X = x) (x₀ : V) (hx₀ : x₀ ∉ Dset)
    (hgood : ∀ X : T.ZVert, π.obj X ∉ Dset → ∃ (E : T.ZVert) (P : Quiver.Path X E),
      X ≠ E ∧ π.obj E = π.obj X ∧
      LinearPaths.path (k := k) (T.forget.mapPath P) ∉ ((T.preproj k).del Del).ideal _ _ ∧
      LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path (T.forget.obj X) (T.forget.obj X)) ∉
        ((T.preproj k).del Del).ideal _ _) :
    ¬ BrickHypothesis c := by
  -- independence of `𝟙` and the closed path
  have key : ∀ (X E : T.ZVert) (P : Quiver.Path X E) (hXE : X ≠ E) (hE : π.obj E = π.obj X),
      LinearPaths.path (k := k) (T.forget.mapPath P) ∉ ((T.preproj k).del Del).ideal _ _ →
      LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path (T.forget.obj X) (T.forget.obj X)) ∉
        ((T.preproj k).del Del).ideal _ _ →
      ∀ a b : k, a • 𝟙 (LinearPaths.obj (k := k) (π.obj X)) +
        b • LinearPaths.path ((π.mapPath P).cast rfl hE) ∈
          meshIdealSub c _ _ ⊔ through k Dset (π.obj X) (π.obj X) → a = 0 ∧ b = 0 := by
    intro X E P hXE hE hP h0 a b hab
    obtain ⟨hb, ha⟩ := T.transfer_del hQ π c hπ hτ Dset Del hD hXE hE P a b hab
    constructor
    · by_contra ha0
      apply h0
      have := Submodule.smul_mem _ a⁻¹ ha
      rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this
    · by_contra hb0
      apply hP
      have := Submodule.smul_mem _ b⁻¹ hb
      rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at this
  have hid : ∀ X : T.ZVert, π.obj X ∉ Dset → 𝟙 (ObjectQuotient.obj c Dset (π.obj X)) ≠ 0 := by
    intro X hX
    obtain ⟨E, P, hXE, hE, hP, h0⟩ := hgood X hX
    rw [oq_id_ne_zero_iff]
    intro hmem
    have := key X E P hXE hE hP h0 1 0 (by rwa [one_smul, zero_smul, add_zero])
    exact one_ne_zero this.1
  intro hb
  obtain ⟨X₀, rfl⟩ := hsurj x₀
  obtain ⟨x, hx⟩ := hb Dset ⟨_, hid X₀ hx₀⟩
  by_cases hxD : x ∈ Dset
  · have h0 := oq_id_eq_zero_of_mem c Dset hxD
    have : Subsingleton (ObjectQuotient.obj c Dset x ⟶ ObjectQuotient.obj c Dset x) :=
      ⟨fun f g ↦ by rw [← Category.id_comp f, ← Category.id_comp g, h0, Limits.zero_comp,
        Limits.zero_comp]⟩
    rw [Module.finrank_zero_of_subsingleton] at hx
    exact zero_ne_one hx
  · obtain ⟨X, rfl⟩ := hsurj x
    obtain ⟨E, P, hXE, hE, hP, h0⟩ := hgood X hxD
    set e₂ : ObjectQuotient.obj c Dset (π.obj X) ⟶ ObjectQuotient.obj c Dset (π.obj X) :=
      (oqFunctor c Dset).map (LinearPaths.path ((π.mapPath P).cast rfl hE))
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ (hid X hxD)).1 hx e₂
    have hz : (oqFunctor c Dset).map ((-t) • 𝟙 (LinearPaths.obj (k := k) (π.obj X)) +
        (1 : k) • LinearPaths.path ((π.mapPath P).cast rfl hE)) = 0 := by
      rw [Functor.map_add, Functor.map_smul, Functor.map_smul, CategoryTheory.Functor.map_id, one_smul]
      rw [show (oqFunctor c Dset).map (LinearPaths.path ((π.mapPath P).cast rfl hE)) = e₂ from rfl,
        ← ht, neg_smul]
      exact neg_add_cancel _
    rw [oqFunctor_map_eq_zero_iff] at hz
    exact one_ne_zero (key X E P hXE hE hP h0 _ _ hz).2

end OrientedTree

end MultiplicativeBasisDeformations
