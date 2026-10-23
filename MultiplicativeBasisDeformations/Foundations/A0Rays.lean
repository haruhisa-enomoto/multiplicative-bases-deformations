module

public import MultiplicativeBasisDeformations.Foundations.A0Normed
public import MultiplicativeBasisDeformations.Foundations.GradedRays

/-!
# The ray basis of `A₀`

Proposition 3.8 and Proposition 4.14 for `A₀`: the homogeneous normed
multiplicative basis of `A₀` (`A0Normed.lean`) is, after reindexing by the
nonzero rays, a ray transversal killing zero ray products. This is the ray table
`P = ray A₀` with `A₀ ≅ kP` (`exists_hasRayBasis_A0`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)

variable [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- **`A₀` has a ray basis** for its vertex idempotents. -/
theorem exists_hasRayBasis_A0 (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ) :
    ∃ Fp : PrimitiveIdempotents (Alg D.F0)ᵐᵒᵖ, Fp.HasRayBasis k := by
  have hfin' : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y) := fun x y ↦ hfd x y
  obtain ⟨bv, hmem, hspan, hne, hid, hmul⟩ := exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) hF
  have hid0 : ∀ x : D.PV, 𝟙 (D.F0 x) ≠ 0 := fun x ↦ id_ne_zero (L := L) x.1
  set B := basisA0 bv hmem hspan hne
  have hloc : ∀ (x : D.PV) (φ : D.F0 x ⟶ D.F0 x), φ ≫ φ = φ → φ = 0 ∨ φ = 𝟙 (D.F0 x) := by
    intro x φ hφ
    haveI := L.end_isLocalRing x.1
    exact idem_eq_zero_or_one (R := End (meshFam Q c x.1)) (p := φ) hφ
  set eι := Fintype.equivFin D.PV
  let Fp : PrimitiveIdempotents (Alg D.F0)ᵐᵒᵖ :=
    { m := Fintype.card D.PV
      e := fun i ↦ B (idIdx bv hmem hid hid0 (eι.symm i))
      complete := (CompleteOrthogonalIdempotents.equiv eι.symm).2
        (idIdx_complete bv hmem hspan hne hid hid0)
      primitive := fun i ↦ idIdx_primitive bv hmem hspan hne hid hid0 hloc _ }
  have hFe : ∀ x : D.PV, Fp.e (eι x) = MulOpposite.op (unitM x x (𝟙 (D.F0 x))) := fun x ↦ by
    change B (idIdx bv hmem hid hid0 (eι.symm (eι x))) = _
    rw [Equiv.symm_apply_apply, basisA0_idIdx]
  set G := lenA0 D hfin'
  have hone0 : ∀ x : D.PV, 𝟙 (D.F0 x) ∈ degreePart c 0 x.1 x.1 := fun x ↦ by
    have := pathMor_mem_degreePart c (Quiver.Path.nil : Quiver.Path x.1 x.1)
    rwa [pathMor_nil] at this
  have he0 : ∀ i, G.IsHom 0 (Fp.e i) := fun i ↦ by
    obtain ⟨x, rfl⟩ := eι.surjective i
    rw [hFe]
    exact unitM_isHom D hfin' (hone0 x)
  have hcorner0 : ∀ (i : Fin Fp.m) (a : (Alg D.F0)ᵐᵒᵖ), a ∈ Fp.corner (k := k) i i →
      G.IsHom 0 a → ∃ t : k, a = t • Fp.e i := by
    intro i a ha h0
    obtain ⟨x, rfl⟩ := eι.surjective i
    rw [Fp.mem_corner_iff', hFe] at ha
    rw [hFe]
    obtain ⟨a', rfl⟩ : ∃ a' : Alg D.F0, MulOpposite.op a' = a := ⟨a.unop, rfl⟩
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, MulOpposite.op_inj] at ha
    set E := unitM x x (𝟙 (D.F0 x))
    have hEE : E * E = E := by rw [unitM_mul, Category.comp_id]
    have h1 : a' * E = a' := by
      calc a' * E = E * (a' * E) * E := by rw [ha]
        _ = E * (a' * (E * E)) := by simp only [mul_assoc]
        _ = a' := by rw [hEE, ha]
    have h2 : E * a' = a' := by
      calc E * a' = E * (E * (a' * E)) := by rw [ha]
        _ = E * E * (a' * E) := by rw [mul_assoc]
        _ = a' := by rw [hEE, ha]
    have heq := eq_unitM_of_corner h1 h2
    have hdeg : a' x x ∈ degreePart c 0 x.1 x.1 := by
      have := congrArg (fun z : (Alg D.F0)ᵐᵒᵖ ↦ z.unop x x) h0
      change degProj c 0 x.1 x.1 (a' x x) = a' x x at this
      rw [← this]
      exact degProj_mem c 0 _
    obtain ⟨t, ht⟩ := degreePart_zero_eq c hdeg
    refine ⟨t, ?_⟩
    rw [heq, ht, unitM_smul, MulOpposite.op_smul]
  have hb : ∀ t : Idx (D0 Q c v₀ D), ∃ i j d, B t ∈ Fp.corner (k := k) i j ∧ G.IsHom d (B t) := by
    rintro ⟨⟨x, y, g⟩, ht⟩
    refine ⟨eι y, eι x, (hgt Q v₀ g).toNat, ?_, ?_⟩
    · rw [basisA0_apply, Fp.mem_corner_iff', hFe, hFe]
      exact op_unitM_corner_mul x y _
    · rw [basisA0_apply]
      exact unitM_isHom D hfin' (deck_part_le v₀ g x.1 y.1 (hmem x y g))
  have hnorm : IsNormedMultiplicativeBasis B := by
    refine ⟨basisA0_isMultiplicative bv hmem hspan hne hmul, ?_, fun n hn ↦ ?_⟩
    · let E : Finset (Idx (D0 Q c v₀ D)) := Finset.univ.image fun x ↦ idIdx bv hmem hid hid0 x
      have hinj : Function.Injective fun x : D.PV ↦ idIdx bv hmem hid hid0 x := by
        intro x y h
        have := congrArg (fun t : Idx (D0 Q c v₀ D) ↦ t.1.1) h
        exact this
      let φ : D.PV ≃ E := Equiv.ofBijective
        (fun x ↦ ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
        ⟨fun x y h ↦ hinj (congrArg Subtype.val h), fun ⟨t, ht⟩ ↦ by
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
          exact ⟨x, rfl⟩⟩
      refine ⟨E, (CompleteOrthogonalIdempotents.equiv φ).1 ?_, fun t ht ↦ ?_⟩
      · exact idIdx_complete bv hmem hspan hne hid hid0
      · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
        exact idIdx_primitive bv hmem hspan hne hid hid0 hloc x
    · exact Fp.span_basis_ideal G he0 hcorner0 hF B hb (algebraRadicalPow k _ n)
        (fun a z hz ↦ algebraRadicalPow_mul_left hn a hz)
        (fun a z hz ↦ algebraRadicalPow_mul_right hn a hz)
  refine ⟨Fp, Fp.hasRayBasis_of_graded G he0 hcorner0 hF B hb hnorm fun i ↦ ?_⟩
  exact ⟨idIdx bv hmem hid hid0 (eι.symm i), rfl⟩

end MeshWalk

end MultiplicativeBasisDeformations
