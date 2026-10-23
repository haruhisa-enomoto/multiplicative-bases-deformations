module

public import MultiplicativeBasisDeformations.Foundations.RepFinite
public import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd
public import MBDVendor.Magnitude.Algebra.IndecomposableLocalEnd

/-!
# Twisting modules by automorphisms

For Lemma 4.13 (`lem:scalar-object-values`, `scalar-normalization.tex`):
"A weight scales morphism lines and thus defines an automorphism of `L`. These
automorphisms act on the indecomposable module classes with any fixed finite
support, by precomposing their actions with the scalar automorphism. […] only
finitely many indecomposable classes supported in `S` occur. Their permutation
image is finite, abelian and divisible, hence trivial."

For an automorphism `σ` of a representation-finite algebra, the twist
`M ↦ M^σ` permutes the finitely many indecomposable classes, so a fixed power
`N` (the order of the permutation group) of any automorphism fixes every class
(`twist_pow_iso`). With the divisibility of weights this gives the triviality of
the action.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B]

/-- The ring automorphism of `Bᵐᵒᵖ` induced by an algebra automorphism. -/
def opHom (σ : B ≃ₐ[k] B) : Bᵐᵒᵖ →+* Bᵐᵒᵖ := RingHom.op (σ : B →+* B)

/-- The twist of a right module by an automorphism: `m · b = m · σ(b)`. -/
def twist (σ : B ≃ₐ[k] B) (M : RightModuleCat B) : RightModuleCat B :=
  (ModuleCat.restrictScalars (opHom σ)).obj M

/-- The twist as a functor. -/
def twistF (σ : B ≃ₐ[k] B) : RightModuleCat B ⥤ RightModuleCat B :=
  ModuleCat.restrictScalars (opHom σ)

/-- The twist is an equivalence. -/
def twistEquiv (σ : B ≃ₐ[k] B) : RightModuleCat B ≌ RightModuleCat B :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.op (σ : B ≃+* B) : Bᵐᵒᵖ ≃+* Bᵐᵒᵖ)

theorem twistEquiv_functor (σ : B ≃ₐ[k] B) : (twistEquiv σ).functor = twistF σ := rfl

instance (σ : B ≃ₐ[k] B) : (twistF σ).Full := by rw [← twistEquiv_functor]; infer_instance
instance (σ : B ≃ₐ[k] B) : (twistF σ).Faithful := by rw [← twistEquiv_functor]; infer_instance
instance (σ : B ≃ₐ[k] B) : (twistF σ).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (opHom σ)).Additive

theorem twist_smul (σ : B ≃ₐ[k] B) (M : RightModuleCat B) (b : Bᵐᵒᵖ) (m : twist σ M) :
    b • m = (MulOpposite.op (σ b.unop)) • (show M from m) := rfl

/-- The identity map `M → M^σ` is `k`-linear. -/
def twistK (σ : B ≃ₐ[k] B) (M : RightModuleCat B) : M →ₗ[k] twist σ M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := by
    change algebraMap k Bᵐᵒᵖ c • m = (MulOpposite.op (σ (algebraMap k Bᵐᵒᵖ c).unop)) • m
    congr 1
    apply MulOpposite.unop_injective
    simp [MulOpposite.algebraMap_apply]

theorem twist_finite (σ : B ≃ₐ[k] B) (M : RightModuleCat B) [Module.Finite k M] :
    Module.Finite k (twist σ M) :=
  Module.Finite.of_surjective (twistK σ M) fun m ↦ ⟨m, rfl⟩

variable [FiniteDimensional k B]

theorem twist_isFiniteIndecomposable (σ : B ≃ₐ[k] B) {M : RightModuleCat B}
    (hM : IsFiniteIndecomposable k B M) : IsFiniteIndecomposable k B (twist σ M) := by
  haveI := hM.1
  haveI : Module.Finite k Bᵐᵒᵖ := inferInstance
  haveI : IsLocalRing (End M) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Bᵐᵒᵖ) M hM.2
  have hloc : IsLocalRing (End ((twistF σ).obj M)) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful (twistF σ) M)
  exact ⟨twist_finite σ M,
    @MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _ _ _ _ (twist σ M) hloc⟩

/-- Twisting twice. -/
theorem twist_mul (σ τ : B ≃ₐ[k] B) (M : RightModuleCat B) :
    Nonempty (twist (σ * τ) M ≅ twist τ (twist σ M)) :=
  ⟨LinearEquiv.toModuleIso (show twist (σ * τ) M ≃ₗ[Bᵐᵒᵖ] twist τ (twist σ M) from
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })⟩

theorem twist_one (M : RightModuleCat B) : Nonempty (twist (1 : B ≃ₐ[k] B) M ≅ M) :=
  ⟨LinearEquiv.toModuleIso (show twist (1 : B ≃ₐ[k] B) M ≃ₗ[Bᵐᵒᵖ] M from
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })⟩

theorem twist_iso (σ : B ≃ₐ[k] B) {M M' : RightModuleCat B} (e : M ≅ M') :
    Nonempty (twist σ M ≅ twist σ M') := ⟨(twistF σ).mapIso e⟩

theorem twist_reflect (σ : B ≃ₐ[k] B) {M M' : RightModuleCat B} (e : twist σ M ≅ twist σ M') :
    Nonempty (M ≅ M') := ⟨(twistF σ).preimageIso e⟩

/-- **A fixed power of every automorphism of a representation-finite algebra fixes
every indecomposable class** (the permutation image is a finite group). -/
theorem twist_pow_iso (hB : IsRepresentationFinite k B) :
    ∃ N : ℕ, 0 < N ∧ ∀ (τ : B ≃ₐ[k] B) (M : RightModuleCat B), IsFiniteIndecomposable k B M →
      Nonempty (twist (τ ^ N) M ≅ M) := by
  classical
  obtain ⟨n, X, hX, hcov⟩ := hB
  let rel : Setoid (Fin n) := ⟨fun i j ↦ Nonempty (X i ≅ X j), ⟨fun i ↦ ⟨Iso.refl _⟩,
    fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e ≪≫ e'⟩⟩⟩
  let Q := Quotient rel
  refine ⟨Fintype.card (Equiv.Perm Q), Fintype.card_pos, fun τ M hM ↦ ?_⟩
  -- the permutation of classes induced by `τ`
  have hj : ∀ i, ∃ j, Nonempty (twist τ (X i) ≅ X j) := fun i ↦
    hcov _ (twist_isFiniteIndecomposable (k := k) τ (hX i))
  choose j hj using hj
  let π₀ : Q → Q := Quotient.map j (fun i i' ⟨e⟩ ↦ by
    obtain ⟨e1⟩ := hj i
    obtain ⟨e2⟩ := hj i'
    obtain ⟨e3⟩ := twist_iso τ e
    exact ⟨e1.symm ≪≫ e3 ≪≫ e2⟩)
  have hinj : Function.Injective π₀ := by
    rintro ⟨i⟩ ⟨i'⟩ h
    have h' : Nonempty (X (j i) ≅ X (j i')) := Quotient.exact h
    obtain ⟨e⟩ := h'
    obtain ⟨e1⟩ := hj i
    obtain ⟨e2⟩ := hj i'
    obtain ⟨e3⟩ := twist_reflect τ (e1 ≪≫ e ≪≫ e2.symm)
    exact Quotient.sound ⟨e3⟩
  let π : Equiv.Perm Q := Equiv.ofBijective π₀ (Finite.injective_iff_bijective.1 hinj)
  -- iterated twists follow the permutation
  have hiter : ∀ (m : ℕ) (i : Fin n), ∃ i', ⟦i'⟧ = (π ^ m) ⟦i⟧ ∧
      Nonempty (twist (τ ^ m) (X i) ≅ X i') := by
    intro m
    induction m with
    | zero =>
        intro i
        obtain ⟨e⟩ := twist_one (k := k) (X i)
        exact ⟨i, by simp, ⟨(by rw [pow_zero]; exact e)⟩⟩
    | succ m ih =>
        intro i
        obtain ⟨i', hi', ⟨e⟩⟩ := ih i
        obtain ⟨e1⟩ := twist_mul (τ ^ m) τ (X i)
        obtain ⟨e2⟩ := twist_iso τ e
        obtain ⟨e3⟩ := hj i'
        refine ⟨j i', ?_, ⟨?_⟩⟩
        · rw [pow_succ', Equiv.Perm.mul_apply, ← hi']
          rfl
        · rw [pow_succ]
          exact e1 ≪≫ e2 ≪≫ e3
  obtain ⟨i, ⟨eM⟩⟩ := hcov M hM
  obtain ⟨i', hi', ⟨e⟩⟩ := hiter (Fintype.card (Equiv.Perm Q)) i
  rw [pow_card_eq_one, Equiv.Perm.one_apply] at hi'
  obtain ⟨e'⟩ : Nonempty (X i' ≅ X i) := Quotient.exact hi'
  obtain ⟨e''⟩ := twist_iso (τ ^ Fintype.card (Equiv.Perm Q)) eM
  exact ⟨e'' ≪≫ e ≪≫ e' ≪≫ eM.symm⟩

end MultiplicativeBasisDeformations
