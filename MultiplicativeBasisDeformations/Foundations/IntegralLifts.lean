import MultiplicativeBasisDeformations.Foundations.IntegralA0
import MultiplicativeBasisDeformations.Foundations.HochschildMesh

/-!
# The lifted modules and arrows over `ℤ/4` (Proposition 10.1)

`integral-deformations.tex:67–74`: "Lift the action matrices arbitrarily to free graded
`𝒪`-modules. […] Equation (prime-field-ext-vanishing) supplies a correction. […] The same bar
calculation, using `Ext¹`, gives uniqueness and lifts all homogeneous maps of nonnegative
degree."

Every evaluated module `M_X` of `A⁽²⁾` lifts to a graded `𝒪P`-module on `Fin n_X → 𝒪`
(`exists_modLift`), and every arrow map `M_y → M_x` lifts to a degree-one `𝒪P`-linear map
between the lifts (`exists_arrowLift`). These data are bundled in `WData`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace WLift

open GExt

variable {Λ : Type*} [Ring Λ] [Algebra 𝔽₂ Λ] {GΛ : GAlg (R := 𝔽₂) Λ}

/-! ### Linear lifts between free lifts -/

section Free

variable {M N : Type*} [AddCommGroup M] [Module 𝔽₂ M] [AddCommGroup N] [Module 𝔽₂ N]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (β : Module.Basis ι 𝔽₂ M) (γ : Module.Basis κ 𝔽₂ N)

/-- The coordinatewise lift of a `𝔽₂`-linear map between free lifts. -/
def linLift (f : M →ₗ[𝔽₂] N) : (ι → ZMod 4) →ₗ[ZMod 4] (κ → ZMod 4) :=
  (Pi.basisFun (ZMod 4) ι).constr (ZMod 4) fun i ↦ lv γ (f (β i))

theorem linLift_apply (f : M →ₗ[𝔽₂] N) (m : ι → ZMod 4) :
    linLift β γ f m = ∑ i, m i • lv γ (f (β i)) := by
  rw [linLift, Module.Basis.constr_apply_fintype]
  simp

theorem ρF_linLift (f : M →ₗ[𝔽₂] N) (m : ι → ZMod 4) : ρF γ (linLift β γ f m) = f (ρF β m) := by
  rw [linLift_apply, map_sum, ρF_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ρF_smul, ρF_lv, map_smul]

variable (dβ : ι → ℤ) (dγ : κ → ℤ) {MM : GMod GΛ M} {NN : GMod GΛ N}
  (hβ : ∀ i, MM.gr.IsHom (dβ i) (β i)) (hγ : ∀ j, NN.gr.IsHom (dγ j) (γ j))

include hβ hγ in
theorem linLift_isHom (f : M →ₗ[𝔽₂] N) {d : ℤ}
    (hf : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + d) (f m)) {p : ℤ} {m : ι → ZMod 4}
    (hm : (grF dβ).IsHom p m) : (grF dγ).IsHom (p + d) (linLift β γ f m) := by
  rw [grF_isHom] at hm
  rw [linLift_apply]
  refine (grF dγ).isHom_sum _ _ fun i _ ↦ ?_
  by_cases hi : dβ i = p
  · exact (grF dγ).isHom_smul _ (lv_isHom γ dγ hγ (hf _ _ (hi ▸ hβ i)))
  · rw [hm i hi, zero_smul]; exact (grF dγ).isHom_zero _

end Free

end WLift

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} (T : TabIso D P)

/-- **A lift of an evaluated module** `M_X` to a free graded `𝒪P`-module. -/
structure ModLift (X : V) where
  n : ℕ
  β : Module.Basis (Fin n) 𝔽₂ (Rep D.F0 (meshFam Q c X))
  dβ : Fin n → ℤ
  hβ : ∀ i, (zgrEv D (hfin2 (c := c)) X).IsHom (dβ i) (β i)
  MM : GMod (galgO T) (Fin n → ZMod 4)
  lift : IsLift MM (gmodEv D (hfin2 (c := c)) X) (πO T) (ρF β)
  gr : MM.gr = grF dβ

/-- **Proposition 10.1, the module lifts** (`prop:fixed-integral-companion`). -/
theorem exists_modLift (J : InjData D) (h1 : DegOne D) (X : V) :
    Nonempty (ModLift T X) := by
  obtain ⟨n, β, dβ, hβ⟩ := exists_homBasis (zgrEv D (hfin2 (c := c)) X)
  have hExt : ExtVanish (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) X) 1 0 :=
    extVanish_ev D (hfin2 (c := c)) J h1 1 X X 0 (Or.inr (by norm_num))
  obtain ⟨MM', hL, hgr⟩ := exists_liftMod (β := β) (dβ := dβ)
    (bΛ := P.basis (ZMod 4)) (hπ := isRed_πO T)
    (dΛ := T.d)
    (hbΛ := fun r ↦ by
      rw [RaySys.Mult.basis_apply]
      exact P.grLin_b T.d (ZMod 4) r)
    (hβ := hβ) hExt
  exact ⟨⟨n, β, dβ, hβ, MM', hL, hgr⟩⟩


/-- **Proposition 10.1, the arrow lifts**: the arrow maps lift to degree-one maps. -/
theorem exists_arrowLift (J : InjData D) (h1 : DegOne D) (N : ∀ X, ModLift T X)
    {y x : V} (a : y ⟶ x) :
    ∃ φ : (Fin (N y).n → ZMod 4) →ₗ[ZMod 4] (Fin (N x).n → ZMod 4),
      (∀ m b, φ ((N y).MM.act m b) = (N x).MM.act (φ m) b) ∧
      (∀ m, ρF (N x).β (φ m) = fA D a (ρF (N y).β m)) ∧
      (∀ p m, (N y).MM.gr.IsHom p m → (N x).MM.gr.IsHom (p + 1) (φ m)) := by
  have hExt : ExtVanish (gmodEv D (hfin2 (c := c)) y) (gmodEv D (hfin2 (c := c)) x) 0 1 :=
    extVanish_ev D (hfin2 (c := c)) J h1 0 y x 1 (Or.inr (by norm_num))
  refine exists_liftHom (isRed_πO T) (N y).lift (N x).lift (fA D a) (fA_act D a) hExt
    (linLift (N y).β (N x).β (fA D a)) (ρF_linLift _ _ _) fun p m hm ↦ ?_
  rw [(N y).gr] at hm
  rw [(N x).gr]
  exact linLift_isHom (MM := gmodEv D (hfin2 (c := c)) y) (NN := gmodEv D (hfin2 (c := c)) x)
    (N y).β (N x).β (N y).dβ (N x).dβ (N y).hβ (N x).hβ (fA D a)
    (fun p m hm ↦ fA_deg D (hfin2 (c := c)) a hm) hm

/-- **The lifted modules and arrows.** -/
structure WData where
  N : ∀ X, ModLift T X
  φ : ∀ {y x : V}, (y ⟶ x) → (Fin (N y).n → ZMod 4) →ₗ[ZMod 4] (Fin (N x).n → ZMod 4)
  φ_act : ∀ {y x : V} (a : y ⟶ x) m b, φ a ((N y).MM.act m b) = (N x).MM.act (φ a m) b
  φ_red : ∀ {y x : V} (a : y ⟶ x) m, ρF (N x).β (φ a m) = fA D a (ρF (N y).β m)
  φ_deg : ∀ {y x : V} (a : y ⟶ x) p m, (N y).MM.gr.IsHom p m → (N x).MM.gr.IsHom (p + 1) (φ a m)

theorem exists_wData (J : InjData D) (h1 : DegOne D) : Nonempty (WData T) := by
  have N := fun X ↦ Classical.choice (exists_modLift T J h1 X)
  choose φ h1' h2 h3 using fun (a : Σ y x : V, y ⟶ x) ↦ exists_arrowLift T J h1 N a.2.2
  exact ⟨⟨N, fun {y x} a ↦ φ ⟨y, x, a⟩, fun {y x} a ↦ h1' ⟨y, x, a⟩, fun {y x} a ↦ h2 ⟨y, x, a⟩,
    fun {y x} a ↦ h3 ⟨y, x, a⟩⟩⟩

end MeshWalk

end MultiplicativeBasisDeformations
