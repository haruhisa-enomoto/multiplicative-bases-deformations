import MultiplicativeBasisDeformations.Foundations.InitialFormProducts

/-!
# Proposition 4.14: `A₀ ≅ kP` with `P = ray A₀`

`scalar-normalization.tex:620–625` (`prop:scalar-normalization`): "For `A₀` of
Construction 2.8 and `P = ray A₀`, there is an isomorphism `A₀ ≅ kP` preserving the labelled
primitive idempotents and homogeneous ray lines. In particular `A₀` has a normed multiplicative
basis."

The table `A0Mult` of the normed ray basis `basisR` is the ray table of `A₀` in the sense of
Definition 3.9: it presents the rays of `A₀` (`A0Mult_rayPres`; each ray contains a unique
homogeneous line, Proposition 3.8, and homogeneous lines are the lines of `basisR`,
`eq_smul_basisR`). With `thetaA0 : kP ≃ A₀` (`b_t ↦ basisR t`, identities to the labelled
idempotents) this is the proposition (`scalarNormalization`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]
  (F : PrimitiveIdempotents B)

/-- **Nonzero multiples stay in the ray.** -/
theorem smul_mem_ray_self {x y : Fin F.m} {f : B} (hf : f ∈ F.corner (k := k) x y) {t : k}
    (ht : t ≠ 0) : t • f ∈ F.ray (k := k) x y f := by
  refine ⟨t • F.e x, F.e y, ⟨Submodule.smul_mem _ t (F.e_mem_corner x), t⁻¹ • F.e x,
    Submodule.smul_mem _ _ (F.e_mem_corner x), ?_, ?_⟩, F.isCornerUnit_e y, ?_⟩
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ ht, one_smul, (F.complete.idem x).eq]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ ht, one_smul, (F.complete.idem x).eq]
  · rw [smul_mul_assoc, smul_mul_assoc, (F.mem_corner_iff').1 hf]

end PrimitiveIdempotents

namespace MeshWalk

open ScalarMeshCategory CatAlg

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

include v₀ hF in
theorem finiteDimensional_A0 : FiniteDimensional k (Alg D.F0)ᵐᵒᵖ :=
  Module.Finite.of_basis (basisR D v₀ hF)

/-- **`P = ray A₀`**: the table of the normed ray basis presents the rays of `A₀`. -/
theorem A0Mult_rayPres :
    (FpA0 D v₀ hF).IsRayPres (k := k) (A0Mult D v₀ hF) (idxA0 D v₀ hF) (basisR D v₀ hF) := by
  haveI := finiteDimensional_A0 D v₀ hF
  set G := lenA0 D (hfinObj (c := c))
  have he0 := FpA0_he0 D v₀ hF
  have hc0 := FpA0_hcorner0 D v₀ hF
  have hmul : ∀ r s, basisR D v₀ hF r * basisR D v₀ hF s =
      ((A0Mult D v₀ hF).mul r s).elim 0 (basisR D v₀ hF) :=
    RaySys.OfBasis.b_mul_b _ (basisR_mult D v₀ hF)
  refine ⟨fun r ↦ basisR_mem_corner D v₀ hF r, fun r ↦ (basisR D v₀ hF).ne_zero r,
    fun r s hrs ↦ ?_, fun x y f hf hf0 ↦ ?_, fun r s t h ↦ ?_, fun r s h _ ↦ ?_⟩
  · -- injectivity: two ray vectors in one ray are proportional
    have hcs := basisR_mem_corner D v₀ hF s
    have hcr := (FpA0 D v₀ hF).ray_subset_corner hcs hrs
    have hray := (FpA0 D v₀ hF).ray_eq_of_mem hcs hrs
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 ((FpA0 D v₀ hF).mem_span_of_ray_eq G he0 hc0
      hcs hcr ((basisR D v₀ hF).ne_zero r) (basisR_isHom' D v₀ hF s) (basisR_isHom' D v₀ hF r)
      hray)
    by_contra hne
    have := congrArg (fun z ↦ (basisR D v₀ hF).repr z r) ht
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      if_neg (Ne.symm hne), smul_zero, if_pos rfl] at this
    exact zero_ne_one this
  · -- surjectivity: each ray contains a homogeneous line
    obtain ⟨g, d, hgd, hg0, hg⟩ := (FpA0 D v₀ hF).exists_hom_mem_ray G he0 hc0 hF hf hf0
    have hgc := (FpA0 D v₀ hF).ray_subset_corner hf hg
    obtain ⟨r, h1, h2, -, t, ht0, rfl⟩ := eq_smul_basisR D v₀ hF hgc hgd hg0
    refine ⟨r, h1, h2, ?_⟩
    have hbc := basisR_mem_corner D v₀ hF r
    rw [h1, h2] at hbc
    have e1 : (FpA0 D v₀ hF).ray (k := k) x y (t • basisR D v₀ hF r) =
        (FpA0 D v₀ hF).ray (k := k) x y (basisR D v₀ hF r) :=
      (FpA0 D v₀ hF).ray_eq_of_mem hbc ((FpA0 D v₀ hF).smul_mem_ray_self hbc ht0)
    have e2 := (FpA0 D v₀ hF).ray_eq_of_mem hf hg
    change f ∈ (FpA0 D v₀ hF).ray (k := k) x y (basisR D v₀ hF r)
    rw [h1, h2] at *
    rw [← e1, e2]; exact (FpA0 D v₀ hF).mem_ray_self hf
  · have hb := (RaySys.OfBasis.mulB_eq_some _).1 h
    refine ⟨fun hM ↦ (basisR D v₀ hF).ne_zero t ?_, ?_⟩
    · rw [← hb]
      exact ((FpA0 D v₀ hF).mul_mem_insertionSpan_iff G he0 hc0 (basisR_isHom' D v₀ hF r)
        (basisR_isHom' D v₀ hF s)).1 hM
    · rw [hb]; exact (FpA0 D v₀ hF).mem_ray_self (basisR_mem_corner D v₀ hF t)
  · have h0 := hmul r s
    rw [h, Option.elim_none] at h0
    rw [h0]; exact Submodule.zero_mem _

/-- **Proposition 4.14** (`prop:scalar-normalization`): `A₀ ≅ kP` for `P = ray A₀`, preserving
the labelled primitive idempotents and the homogeneous ray lines; `A₀` has a normed
multiplicative basis. -/
theorem scalarNormalization :
    (FpA0 D v₀ hF).IsRayPres (k := k) (A0Mult D v₀ hF) (idxA0 D v₀ hF) (basisR D v₀ hF) ∧
    (∀ t, thetaA0 D v₀ hF ((A0Tab D v₀ hF).b k t) = basisR D v₀ hF t) ∧
    (∀ x, thetaA0 D v₀ hF ((A0Tab D v₀ hF).b k ((A0Tab D v₀ hF).e x)) =
      MulOpposite.op (unitM x x (𝟙 (D.F0 x)))) ∧
    (∀ t, (lenA0 D (hfinObj (c := c))).IsHom (dA D v₀ t) (basisR D v₀ hF t)) ∧
    HasNormedMultiplicativeBasis k (Alg D.F0)ᵐᵒᵖ :=
  ⟨A0Mult_rayPres D v₀ hF, thetaA0_b D v₀ hF, fun x ↦ by rw [thetaA0_b]; exact basisR_eR D v₀ hF x,
    basisR_isHom' D v₀ hF, hasNormedBasis_A0 D v₀ hF⟩

end MeshWalk

end MultiplicativeBasisDeformations
