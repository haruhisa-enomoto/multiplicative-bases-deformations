module

public import MultiplicativeBasisDeformations.Refinements.FamilyPresentation
public import MultiplicativeBasisDeformations.Refinements.FamilyPsi
public import MultiplicativeBasisDeformations.Refinements.LiftedLayers

/-!
# Proposition 12.8: the polynomial mesh comparison

`deformation-refinements.tex` (`prop:polynomial-mesh-comparison`): "Let `m + Σ_{i∈I} t_i μ_i`
be an associative family satisfying the hypotheses of Proposition 7.9 […], now indexed by
`I = I₀`. There are polynomial lifts of the normalized modules, their morphisms, and their mesh
presentations for which the retained mesh coefficients are `F_i(t) = a_i t_i`, `a_i ∈ k^*`. After
every specialization to `k`, these modules exhaust the indecomposables of the fibre algebra."

`polynomialMeshComparison`, for the mesh category `C` of mesh data whose positive degrees are
radical (as for `k(Γ_A)`, `IndSkeleton.arHrad`). Hypotheses: the family `μ_i` (`FamHyp`:
internal degrees `q_i ≥ 1`, normalized, `m + Σ_i t_i μ_i` associative for all `t`), of characters
`χ_i` for a mesh weight `W`, with coordinates `χ_i ↦ e_i` (part of an integer basis,
Proposition 7.5); retained rows `R_i` of length `q_i + 2` and relative weight `χ_i` whose classes
span the cokernels of the mesh derivatives (`CokerSpan`); no `μ_i` is a coboundary (its class in
`HH²(A₀)_{χ_i}` is nonzero). Conclusions, for every `t : I → k`:
* the lifted actions on the evaluated modules and the lifted arrows are polynomial in `t`;
* the lifted arrows satisfy `r_x = Σ_i a_i t_i R_i` with `a_i ≠ 0`, and present the lifted
  category of the fibre: the realization of `kQ` is surjective, with kernel
  `(𝔪^{N+1}, r_x − Σ_i a_i t_i R_i)`;
* the lifted modules exhaust the indecomposable modules of the fibre algebra (Corollary 12.1).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration MGr PathReal FlatPert

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)} [Fintype Q.nonprojective]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {I : Type} [Fintype I] [DecidableEq I]
  {μ : I → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ} {qd : I → ℕ}
  {Wt : Type} [AddCommGroup Wt] {χ : I → Wt} {coords : Wt →+ (I → ℤ)} [Infinite k]

/-- **Proposition 12.8 (polynomial mesh comparison).** -/
theorem polynomialMeshComparison (H : FamHyp D hfin μ qd) (W : MeshWt Q Wt)
    (hχ : ∀ i, HasChar W hfin D (χ i) (μ i)) (hco : ∀ i, coords (χ i) = Pi.single i 1)
    (J : D.InjData) (h1 : DegOne D)
    (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y)
    (Rw : I → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hlen : ∀ i, (Rw i).2.length = qd i + 2) (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i)
    (hS : CokerSpan c (Set.range Rw))
    (hnc : ∀ j, ¬ ∃ Hc : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
      (∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + qd j) (Hc a)) ∧
        μ j = hcobdry Hc) :
    ∃ (A : ArrowL H W hχ J h1 hco) (a : I → k) (N : ℕ), (∀ i, a i ≠ 0) ∧
      -- the lifts are polynomial in `t`
      (∀ X : V, IsPoly fun t ↦ (famAct H W hχ J h1 hco t X).tot) ∧
      (∀ {y x : V} (b : y ⟶ x), IsPoly fun t ↦ toLin (twArrow A t b)) ∧
      ∀ t : I → k,
        -- the retained mesh coefficients are `a_i t_i`
        (∀ x, realizeR k (twArrow A t) _ _ (meshRelation c x) =
          ∑ i, (a i * t i) • realizeR k (twArrow A t) _ _ (rowQ (k := k) Rw i x)) ∧
        -- the mesh presentation of the lifted category of the fibre
        (∀ {y x : V} (f : FB (famLifts H W hχ J h1 hco t) y ⟶ FB (famLifts H W hχ J h1 hco t) x),
          ∃ F, realizeR k (twArrow A t) y x F = f) ∧
        (∀ {y x : V} (F : Hm k y x), realizeR k (twArrow A t) y x F = 0 ↔
          F ∈ (idealB (meshPres c) (ftp Rw a t) (ftp_mem (H := H) hlen hwt a t) N).I y x) ∧
        -- the lifted modules are pairwise nonisomorphic indecomposables
        (∀ x, IsFiniteIndecomposable k (Fib (famAM H t))
            (FB (famLifts H W hχ J h1 hco t) x)) ∧
        (∀ x y, Nonempty (FB (famLifts H W hχ J h1 hco t) x ≅
            FB (famLifts H W hχ J h1 hco t) y) → x = y) ∧
        -- the lifted modules exhaust the indecomposables of the fibre
        (∀ M : RightModuleCat (Fib (famAM H t)), IsFiniteIndecomposable k (Fib (famAM H t)) M →
          ∃ x, Nonempty (M ≅ FB (famLifts H W hχ J h1 hco t) x)) := by
  classical
  obtain ⟨A, lam, hA⟩ := exists_normalForm_one (H := H) (W := W) (hχ := hχ) (J := J) (h1 := h1)
    (hco := hco) hlen hwt hS
  set Dm := Finset.univ.sup fun X : V ↦ degBound (gmodEv D hfin X).gr
  refine ⟨A, lam, Nb hfin + 2 * Dm, fun j ↦ lam_ne_zero hlen hwt A lam hA j (hnc j),
    fun X ↦ ?_, fun b ↦ ?_, fun t ↦ ⟨fun x ↦ tw_relation hlen hwt A lam hA t x,
      fun f ↦ realize_tw_surjective A t f, fun F ↦ realize_tw_ker hlen hwt A lam hA t _ (by omega)
        (fun X Y ↦ ?_) F, ?_⟩⟩
  · simp only [famAct_tot]
    exact isPoly_twb (coords := coords) _ _ _ 0 _
  · simp only [toLin_twArrow]
    exact isPoly_twl (coords := coords) _ _ _ _
  · have h1' : degBound (gmodEv D hfin X).gr ≤ Dm :=
      Finset.le_sup (f := fun X : V ↦ degBound (gmodEv D hfin X).gr) (Finset.mem_univ _)
    have h2' : degBound (gmodEv D hfin Y).gr ≤ Dm :=
      Finset.le_sup (f := fun X : V ↦ degBound (gmodEv D hfin X).gr) (Finset.mem_univ _)
    omega
  · have hc := (positiveDeformationCompleteness (famPF H t) J h1 hrad).2.2
      (famLifts H W hχ J h1 hco t)
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

end MeshWalk

end MultiplicativeBasisDeformations
