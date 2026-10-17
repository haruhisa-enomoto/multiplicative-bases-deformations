import MultiplicativeBasisDeformations.Refinements.SameSupportForms
import MultiplicativeBasisDeformations.Foundations.ResidualSpaces

/-!
# Lemma 12.6 for the residual paths of Proposition 6.1

`lem:same-support-forms`: "Let `C(λ)` and `C(λ')` be the mesh normal forms of Proposition 12.2,
using the same normalized meshes and the residual paths of Proposition 6.1. If `λ_i = 0` exactly
when `λ'_i = 0`, there is an object-preserving isomorphism `C(λ) ≅ C(λ')`."

The rows of Proposition 6.1 (`residualCorrectionSpaces`) satisfy the hypotheses of the generic
`sameSupport`: they lie at periodic vertices of pairwise distinct components, have length at
least four (degree `2s + 2`), and stay inside their component, since a row through a
nonperiodic vertex has zero class (`row_mem_imageD_of_not_periodic`) while the classes of the
rows are nonzero (`pathIn_residual`). The statement is `sameSupport_residual`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace SameSupport

open ScalarMeshCategory TranslationQuiver FlatPert

variable {V : Type} [Quiver.{0} V]

theorem pathIn_of_vertices {C : Set V} {x : V} :
    ∀ {y : V} (p : Quiver.Path x y), (∀ v ∈ p.vertices, v ∈ C) → PathIn C p
  | _, Quiver.Path.nil, _ => trivial
  | _, Quiver.Path.cons p e, h => by
      have hsub : ∀ v ∈ p.vertices, v ∈ C := fun v hv ↦ h v
        ((Quiver.Path.mem_vertices_cons p e).2 (Or.inl hv))
      exact ⟨pathIn_of_vertices p hsub, hsub _ (Quiver.Path.end_mem_vertices p)⟩

variable {k : Type} [Field k] [IsAlgClosed k] [Fintype V] [DecidableEq V]
  [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {Q : TranslationQuiver V} (c : MeshCoefficients k Q)

/-- **Lemma 12.6** (`lem:same-support-forms`) for the residual paths of Proposition 6.1: in
characteristic two, for a finite-dimensional scalar mesh category with the brick hypothesis,
there are rows `p_i : τ v_i → v_i` as in Proposition 6.1 (at periodic vertices of pairwise
distinct components, with nonzero classes spanning the cokernels) such that for every `N` and
parameters `λ, λ'` with the same zeros, a diagonal automorphism of `kQ` maps the ideal
`(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)` of `C(λ)` onto that of `C(λ')`. -/
theorem sameSupport_residual (hQ : HasAtMostOneArrow V) (hchar : (2 : k) = 0)
    (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ (n : ℕ) (v₀ : Fin n → Q.nonprojective) (p : ∀ i, Quiver.Path (Q.tau (v₀ i)).1 (v₀ i).1),
      Function.Injective (fun i ↦ (⟨v₀ i, p i⟩ : Σ x : Q.nonprojective,
        Quiver.Path (Q.tau x).1 x.1)) ∧
      (∀ i, (v₀ i).1 ∈ Q.periodic) ∧ (∀ i j, (v₀ j).1 ∈ Q.component (v₀ i).1 → i = j) ∧
      CokerSpan c (Set.range fun i ↦ (⟨v₀ i, p i⟩ : Σ x : Q.nonprojective,
        Quiver.Path (Q.tau x).1 x.1)) ∧
      (∀ i, row c (v₀ i) (p i) ∉ imageD c ((p i).length - 1)) ∧
      ∃ (hint : ∀ i, PathIn (Q.component (v₀ i).1) (p i)) (hlen : ∀ i, 3 ≤ (p i).length),
        ∀ (N : ℕ) (lam lam' : Fin n → k), (∀ i, lam i = 0 ↔ lam' i = 0) →
          ∃ μ : ∀ {x y : V}, (x ⟶ y) → kˣ,
            (∀ x y (g : Hm k x y), gaugeMap (fun α ↦ (μ α)⁻¹) x y (gaugeMap μ x y g) = g) ∧
            (∀ x y (g : Hm k x y), gaugeMap μ x y (gaugeMap (fun α ↦ (μ α)⁻¹) x y g) = g) ∧
            ∀ x y, Submodule.map (gaugeMap μ x y)
                ((idealT c (rowTup v₀ p) (rowTup_mem v₀ p hlen) lam N).I x y) =
              (idealT c (rowTup v₀ p) (rowTup_mem v₀ p hlen) lam' N).I x y := by
  classical
  haveI : Fintype Q.nonprojective := Fintype.ofFinite _
  obtain ⟨S, hper, huniq, hspan, hnz, -, -, hmod, -⟩ := residualCorrectionSpaces c hQ hchar hfin hbrick
  have hfinS : S.Finite := by
    refine Set.Finite.of_finite_image (f := fun R ↦ R.1.1) (Set.toFinite _) ?_
    intro R hR R' hR' h
    exact huniq R hR R' hR' (by
      have : R'.1.1 = R.1.1 := h.symm
      rw [this]; exact mem_component_self (hper R hR))
  haveI : Fintype S := hfinS.fintype
  set e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hlen4 : ∀ R ∈ S, 4 ≤ R.2.length := by
    intro R hR
    obtain ⟨x, -, -, R₀, ⟨L, π, ρ, s, g, -, -, -, -, -, -, hs, -, -, hl⟩, he⟩ := hmod R hR
    rw [← he, hl]; omega
  have hint : ∀ R ∈ S, PathIn (Q.component R.1.1) R.2 := by
    intro R hR
    have hall : ∀ v ∈ R.2.vertices, v ∈ Q.periodic := by
      intro v hv
      by_contra hvp
      apply hnz R hR
      exact row_mem_imageD_of_not_periodic c R.1 R.2 (by have := hlen4 R hR; omega) hv hvp
    exact pathIn_of_vertices R.2 (vertices_mem_component (tau_mem_component (hper R hR)) R.2 hall)
  set v₀ : Fin (Fintype.card S) → Q.nonprojective := fun i ↦ (e i).1.1
  set p : ∀ i, Quiver.Path (Q.tau (v₀ i)).1 (v₀ i).1 := fun i ↦ (e i).1.2
  have hinj : Function.Injective (fun i ↦ (⟨v₀ i, p i⟩ : Σ x : Q.nonprojective,
      Quiver.Path (Q.tau x).1 x.1)) := fun i j h ↦ e.injective (Subtype.ext h)
  have hrange : (Set.range fun i ↦ (⟨v₀ i, p i⟩ : Σ x : Q.nonprojective,
      Quiver.Path (Q.tau x).1 x.1)) = S := by
    ext R; constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hR; exact ⟨e.symm ⟨R, hR⟩, by simp [v₀, p]⟩
  have hperi : ∀ i, (v₀ i).1 ∈ Q.periodic := fun i ↦ hper _ (e i).2
  have hdisj : ∀ i j, (v₀ j).1 ∈ Q.component (v₀ i).1 → i = j := fun i j h ↦
    hinj (huniq _ (e i).2 _ (e j).2 h)
  have hinti : ∀ i, PathIn (Q.component (v₀ i).1) (p i) := fun i ↦ hint _ (e i).2
  have hleni : ∀ i, 3 ≤ (p i).length := fun i ↦ by
    show 3 ≤ (e i).1.2.length
    have := hlen4 _ (e i).2; omega
  refine ⟨_, v₀, p, hinj, hperi, hdisj, by rw [hrange]; exact hspan, fun i ↦ hnz _ (e i).2,
    hinti, hleni, fun N lam lam' hsupp ↦ ?_⟩
  exact sameSupport v₀ p c hperi hdisj hinti hleni N lam lam' hsupp

end SameSupport

end MultiplicativeBasisDeformations
