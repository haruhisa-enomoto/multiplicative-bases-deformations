module

public import MultiplicativeBasisDeformations.Foundations.MeshExact
public import MultiplicativeBasisDeformations.Foundations.ARInjData
public import MultiplicativeBasisDeformations.Foundations.UnitCoefficients
public import MultiplicativeBasisDeformations.Foundations.ExtHigher
public import MultiplicativeBasisDeformations.Foundations.HochschildMesh

/-!
# The prime-field model `C⁽²⁾` of `k(Γ_A)` (Section 10)

`integral-deformations.tex`: "The all-one meshes of Section 7 define a graded category
`C⁽²⁾` with `k ⊗_{𝔽₂} C⁽²⁾ = C`. […] Evaluation identifies `C⁽²⁾` with their full Hom category,
since it does so after the faithful field extension to `k`. The same extension commutes with
graded Ext […]. Lemma 6.3 therefore gives `Ext^n_{A⁽²⁾}(M_i⁽²⁾, M_j⁽²⁾)_d = 0` (`n ≥ 1`,
`d ≥ 0`)."

For `char k = 2`: the all-one scalar mesh category `C⁽²⁾ = C(Γ_A, 1)` over `𝔽₂` (`prime2`), the
gauge of Lemma 4.4 (`arGauge`), the form functor to `k(Γ_A)` with equal Hom dimensions, and the
mesh data of `C⁽²⁾` (`primeMeshData`) obtained by descent of the exact meshes of `k(Γ_A)`
(`arMeshExact`, Proposition 2.6), with injective labels (`primeInjData`) and degree-one arrows.
Lemma 6.3 then holds for `C⁽²⁾` (`primeExtVanish`): the same proof, for the descended mesh data,
replaces the base change of `Ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe w

namespace ScalarMeshCategory

variable {k : Type w} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}

/-- The arrows and scaled mates of `meshDataOf` have degree one. -/
theorem degOne_meshDataOf (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
    (hE : MeshExact c) : MeshWalk.DegOne (meshDataOf hfin hE) :=
  ⟨fun _ a ↦ MeshWalk.arrowMor_mem_degreePart a.2,
    fun _ _ _ ↦ Submodule.smul_mem _ _ (MeshWalk.arrowMor_mem_degreePart _)⟩

end ScalarMeshCategory

namespace IndSkeleton

open ScalarMeshCategory

attribute [local instance] ZMod.algebra

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **The meshes of `k(Γ_A)` are exact** (Proposition 2.6(1)(2)). -/
theorem arMeshExact : MeshExact (S.arCoefficients b) :=
  ⟨fun x w g hg ↦ S.ar_cov_exact b x.1 x.2 w g hg, fun x w z hz ↦ S.ar_cov_mono b x.1 x.2 w z hz,
    fun x w v hv ↦ S.ar_contra_exact b x.1 x.2 w v hv,
    fun x w u hu ↦ S.ar_contra_mono b x.1 x.2 w u hu,
    fun x hx w g hg a ↦ S.ar_proj_mono b x hx w g hg a⟩

/-- The all-one coefficients. -/
abbrev oneC (K : Type) [Field K] : MeshCoefficients K S.arTranslationQuiver := fun _ _ _ ↦ 1

/-- The all-one coefficients over `k`. -/
abbrev oneK : MeshCoefficients k S.arTranslationQuiver := fun _ _ _ ↦ 1

/-- **The gauge of Lemma 4.4**: `c_{x,a} = η_x μ_{σa} μ_a`. -/
theorem exists_arGauge : ∃ (μ : ∀ {x y : S.ARVertex}, (x ⟶ y) → kˣ)
    (η : S.arTranslationQuiver.nonprojective → kˣ), ∀ (x : S.arTranslationQuiver.nonprojective)
      (y : S.ARVertex) (a : y ⟶ x.1), S.arCoefficients b x y a =
        η x * S.oneK x y a * μ (S.arTranslationQuiver.mate x y a) * μ a := by
  have : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  obtain ⟨φ, ψ, hφψ⟩ := MeshWalk.exists_unit_rescaling (S.arCoefficients b)
    (S.finiteDimensional_meshHom b) (S.arCoefficients b)
  refine ⟨fun {x y} a ↦ (φ ⟨x, y, a⟩)⁻¹, ψ, fun x y a ↦ ?_⟩
  rw [← hφψ x y a]
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, mul_one]
  field_simp

/-- A chosen gauge. -/
def arMu : ∀ {x y : S.ARVertex}, (x ⟶ y) → kˣ := (S.exists_arGauge b).choose

/-- A chosen gauge. -/
def arEta : S.arTranslationQuiver.nonprojective → kˣ := (S.exists_arGauge b).choose_spec.choose

theorem arGauge (x : S.arTranslationQuiver.nonprojective) (y : S.ARVertex) (a : y ⟶ x.1) :
    S.arCoefficients b x y a =
      S.arEta b x * S.oneK x y a * S.arMu b (S.arTranslationQuiver.mate x y a) * S.arMu b a :=
  (S.exists_arGauge b).choose_spec.choose_spec x y a

variable [CharP k 2]

theorem hredOne : ∀ (x : S.arTranslationQuiver.nonprojective) (y : S.ARVertex) (a : y ⟶ x.1),
    algebraMap (ZMod 2) k ((S.oneC (ZMod 2) x y a : (ZMod 2)ˣ) : ZMod 2) = (S.oneK x y a : k) :=
  fun _ _ _ ↦ by simp

/-- **Equal dimensions** of `C⁽²⁾` and `k(Γ_A)`. -/
theorem prime_finrank (x y : S.ARVertex) :
    FiniteDimensional (ZMod 2) (ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶ ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) ∧
      Module.finrank (ZMod 2) (ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶ ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) =
        Module.finrank k (S.meshObj b x ⟶ S.meshObj b y) := by
  have := S.finiteDimensional_meshHom b x y
  exact finiteDimensional_finrank_Fm (S.oneC (ZMod 2)) S.oneK (S.arCoefficients b) (S.hredOne)
    (S.arMu b) (S.arEta b) (S.arGauge b)

include b in
theorem prime_fd (x y : S.ARVertex) :
    FiniteDimensional (ZMod 2) (ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶ ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) :=
  (S.prime_finrank b x y).1

include b in
/-- **The exact meshes of `C⁽²⁾`.** -/
theorem primeMeshExact : MeshExact (S.oneC (ZMod 2)) :=
  MeshExact.descend (S.oneC (ZMod 2)) S.oneK (S.arCoefficients b) S.hredOne (S.arMu b)
    (S.arEta b) (S.arGauge b) (S.arMeshExact b)

/-- **The mesh data of `C⁽²⁾`.** -/
def primeMeshData : CatAlg.MeshData (fun x : S.ARVertex ↦ ScalarMeshCategory.obj (S.oneC (ZMod 2)) x)
    (localFamily (S.oneC (ZMod 2)) (S.prime_fd b)) :=
  meshDataOf (S.prime_fd b) (S.primeMeshExact b)

/-- **The injective labels of `C⁽²⁾`**, those of `k(Γ_A)`. -/
def primeInjData : CatAlg.MeshData.InjData (S.primeMeshData b) where
  S p := (S.arInjData b).S p
  I p := (S.arInjData b).I p
  dimS p q := by
    rw [(S.prime_finrank b _ _).2]
    exact (S.arInjData b).dimS p q
  dimSI p q := by
    rw [(S.prime_finrank b _ _).2]
    exact (S.arInjData b).dimSI p q
  dimI p q := by
    rw [(S.prime_finrank b _ _).2, (S.prime_finrank b _ _).2]
    exact (S.arInjData b).dimI p q

theorem primeDegOne : MeshWalk.DegOne (S.primeMeshData b) :=
  degOne_meshDataOf (S.prime_fd b) (S.primeMeshExact b)

end IndSkeleton

end MultiplicativeBasisDeformations
