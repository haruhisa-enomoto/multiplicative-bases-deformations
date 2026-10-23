module

public import MultiplicativeBasisDeformations.Foundations.BasicLabels
public import MultiplicativeBasisDeformations.Foundations.A0Normed
public import MultiplicativeBasisDeformations.Foundations.ARInjData
public import MultiplicativeBasisDeformations.Foundations.NormedTransport

/-!
# A standard basic algebra is its projective algebra `A₀`

Corollary 5.5 (`mesh-deformations.tex`): "Restrict the resulting
isomorphism `ind(mod A) ≅ C` to the labelled projective objects and take
opposite algebras. Construction 2.8 and Proposition 4.14 give `A ≅ A₀ ≅ kP`."

For a basic algebra with idempotents `e_i`, the projective vertices of `Γ_A`
correspond to the `e_i` (`pvEquiv`, with `S.obj p ≅ e_{σ p} A`). A standard
equivalence `k(Γ_A) ≃ ind(mod A)` then gives `A₀ = (Alg F₀)ᵒᵖ ≅
(Alg (e_{σ p} A))ᵒᵖ ≅ A` (`algEquivA0`, with the Peirce isomorphism).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open MBDVendor.Magnitude.RightModule

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)
  {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
  (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
    y * x = e j) → i = j)

theorem isPrimitive_of_data {a : A} (D : PrimitiveIdempotentData a) : IsPrimitiveIdempotent a :=
  ⟨D.idempotent, D.nonzero, D.corner_idempotent⟩

theorem data_of_isPrimitive {a : A} (h : IsPrimitiveIdempotent a) : PrimitiveIdempotentData a :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- An isomorphism of finitely generated modules as an isomorphism of modules. -/
def isoObj {M N : ModCat A} (φ : M ≅ N) : M.obj ≅ N.obj := (ObjectProperty.ι _).mapIso φ

include he hprim in
/-- **Each projective label is some `e_i A`.** -/
theorem exists_iso_label (p : (S.arMeshData b).PV) :
    ∃ i, Nonempty (S.obj (S.index p.1) ≅ idealMod (e i)) := by
  obtain ⟨e0, D, ⟨φ⟩⟩ := S.exists_primitive (S.index p.1) (S.projective_of_proj b p)
  obtain ⟨i, ⟨ψ⟩⟩ := exists_iso_ideal k (isPrimitive_of_data D) he hprim
  exact ⟨i, ⟨(isoObj φ).symm ≪≫ ψ⟩⟩

/-- The idempotent of a projective vertex. -/
def σv (p : (S.arMeshData b).PV) : Fin n := Classical.choose (S.exists_iso_label b he hprim p)

/-- `S.obj p ≅ e_{σ p} A`. -/
def isoLabel (p : (S.arMeshData b).PV) : S.obj (S.index p.1) ≅ idealMod (e (S.σv b he hprim p)) :=
  (Classical.choose_spec (S.exists_iso_label b he hprim p)).some

theorem σv_injective : Function.Injective (S.σv b he hprim) := by
  intro p q h
  have φ := S.isoLabel b he hprim p ≪≫ eqToIso (by rw [h]) ≪≫ (S.isoLabel b he hprim q).symm
  exact Subtype.ext (S.pairwise _ _ ⟨φ⟩)

include hbasic in
theorem σv_surjective : Function.Surjective (S.σv b he hprim) := by
  intro i
  obtain ⟨j, ⟨φ⟩⟩ := S.toVendor.fgObj_complete (rightIdealFGObj (e i))
    (rightIdealFGObj_indecomposable (data_of_isPrimitive (hprim i)))
  have hproj : Projective (S.fg j) := Projective.of_iso φ (rightIdealFGObj_projective (hprim i).1)
  let p : (S.arMeshData b).PV := ⟨S.vertex j, not_not.2 hproj⟩
  refine ⟨p, (hbasic _ _ ?_).symm⟩
  have ψ : idealMod (e i) ≅ idealMod (e (S.σv b he hprim p)) :=
    isoObj φ ≪≫ S.isoLabel b he hprim p
  exact basic_data_of_iso (hprim i).1 (hprim _).1 ψ

include hbasic in
/-- **Projective vertices ↔ idempotents.** -/
def pvEquiv : (S.arMeshData b).PV ≃ Fin n :=
  Equiv.ofBijective (S.σv b he hprim)
    ⟨S.σv_injective b he hprim, S.σv_surjective b he hprim hbasic⟩

theorem pvEquiv_apply (p : (S.arMeshData b).PV) : S.pvEquiv b he hprim hbasic p = S.σv b he hprim p :=
  rfl

/-- **`A ≅ A₀`** for a basic algebra with a standard equivalence. -/
def algEquivA0 (Φ0 : S.ARMeshCategory b ⥤ S.Ind) [Φ0.IsEquivalence]
    (hlin : IsLinearFunctor (k := k) Φ0) (β : ∀ x, Φ0.obj (S.meshObj b x) ≅ S.label x) :
    A ≃ₐ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ := by
  haveI : Φ0.Additive := ⟨fun {X Y f g} ↦ by simpa using hlin X Y 1 f g⟩
  haveI : Φ0.Linear k := ⟨fun {X Y} f c ↦ by
    have := hlin X Y c f 0
    rwa [add_zero, Functor.map_zero, add_zero] at this⟩
  haveI : S.incl.Linear k := ⟨fun _ _ ↦ rfl⟩
  haveI : S.incl.Additive := ⟨rfl⟩
  let Φ := Φ0 ⋙ S.incl
  let σE := S.pvEquiv b he hprim hbasic
  let α : ∀ p : (S.arMeshData b).PV, Φ.obj ((S.arMeshData b).F0 p) ≅ idealMod ((e ∘ σE) p) :=
    fun p ↦ S.incl.mapIso (β p.1) ≪≫ S.isoLabel b he hprim p
  have he' : CompleteOrthogonalIdempotents (e ∘ σE) := (CompleteOrthogonalIdempotents.equiv σE).2 he
  exact (peirceEquiv he').trans (AlgEquiv.op (CatAlg.algEquivOfFunctor Φ α).symm)

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- A trivial algebra has a normed multiplicative basis (the empty one). -/
theorem hasNormedBasis_of_subsingleton [Subsingleton A] : HasNormedMultiplicativeBasis k A := by
  refine ⟨PEmpty, Module.Basis.empty A, ⟨fun i ↦ i.elim, ⟨∅, ?_, fun i hi ↦ by simp at hi⟩,
    fun n _ ↦ Subsingleton.elim _ _⟩⟩
  refine ⟨⟨fun i ↦ absurd i.2 (Finset.notMem_empty _), fun i ↦ absurd i.2 (Finset.notMem_empty _)⟩,
    Subsingleton.elim _ _⟩

include he hprim hbasic in
/-- **A standard basic algebra has a normed multiplicative basis** (Corollary 5.5(2)):
`A ≅ A₀` and `A₀` has one (Proposition 4.14). -/
theorem hasNormedBasis_of_isStandard (hstd : S.IsStandard) : HasNormedMultiplicativeBasis k A := by
  classical
  by_cases hn : n = 0
  · subst hn
    haveI : Subsingleton A := by
      have h := he.complete
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact subsingleton_of_zero_eq_one h
    exact hasNormedBasis_of_subsingleton
  obtain ⟨b, Φ0, hEq, hlin, hβ⟩ := hstd
  haveI := hEq
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  let φ := S.algEquivA0 b he hprim hbasic Φ0 hlin fun x ↦ (hβ x).some
  let v₀ : S.ARVertex := ((S.pvEquiv b he hprim hbasic).symm ⟨0, Nat.pos_of_ne_zero hn⟩).1
  exact HasNormedMultiplicativeBasis.of_algEquiv φ
    (MeshWalk.hasNormedBasis_A0 (D := S.arMeshData b) v₀
      (CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)))

end MultiplicativeBasisDeformations.IndSkeleton
