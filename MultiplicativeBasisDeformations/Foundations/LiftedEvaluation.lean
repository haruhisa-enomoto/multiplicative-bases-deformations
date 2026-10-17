import MultiplicativeBasisDeformations.Foundations.InjectiveLabels
import MultiplicativeBasisDeformations.Foundations.CoverCategory

/-!
# Lemma 4.8: evaluation of lifted objects is fully faithful

`lem:lifted-projective-evaluation` (`scalar-normalization.tex:327–390`). For a
lifted object `X̃` put `V_X̃(z) = C̃(P_z, X̃)` on the lifted projective vertices
`z`. "By `eq:walk-hom-sum`, for each projective label `x`,
`C(P_x, X) = ⊕_g V_X̃(g x̃)`. Thus `ev(X)` is the direct sum of the components
of `V_X̃` […]. A map `φ : V_X̃ → V_Ỹ` of `L`-modules therefore defines an
`A₀`-module map `ev(X) → ev(Y)` […]. By Proposition 2.10, this map is `ev(f)`
for a unique `f ∈ C(X, Y)`. […] write `f = Σ_g f̄_g` […] `ev(f̄_g)` maps the
component at `z̃` to the component at `g⁻¹ z̃`. The deck action is free, so for
`g ≠ 1` these blocks are off the diagonal, where `ev(f)` vanishes. Hence
`ev(f̄_g) = 0` for `g ≠ 1`. Faithfulness of `ev` gives `f̄_g = 0` […]. Thus
`f = f̄_1` […]; this proves fullness. If the evaluation of
`f ∈ C̃(X̃, Ỹ)` is zero, then the image of `f` in `C(X, Y)` is killed by `ev`;
the same two facts give `f = 0`, proving faithfulness."

Here the cover is the graded covering category of a `G`-graded family with
mesh data: a lifted object is `(X, h)`, a lifted projective vertex is
`z = (p, g)` with `p` projective, and `V_X̃(z)` is the degree `g⁻¹h` part of
`C(P_p, X)`. A map `V_X̃ → V_Ỹ` of modules over the lifted projectives is a
natural family (`NatFam`); the deck degree `g` of `f̄_g` is relative to the
sheets of `X̃` and `Ỹ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G] [DecidableEq G]

namespace HomGrading

variable (Dg : HomGrading (k := k) F G) [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

/-- All degrees occurring between labels. -/
def degs : Finset G :=
  Finset.univ.biUnion fun xy : ι × ι ↦ (finite_degrees (D := Dg) xy.1 xy.2).toFinset

theorem proj_eq_zero_of_not_mem {g : G} (hg : g ∉ Dg.degs) {x y : ι} (f : F x ⟶ F y) :
    Dg.proj g x y f = 0 := by
  have hbot : Dg.part g x y = ⊥ := by
    by_contra h
    exact hg (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, (Set.Finite.mem_toFinset _).2 h⟩)
  have hm : Dg.proj g x y f ∈ Dg.part g x y := ⟨f, rfl⟩
  rw [hbot, Submodule.mem_bot] at hm
  exact hm

theorem eq_zero_of_not_mem {g : G} (hg : g ∉ Dg.degs) {x y : ι} {f : F x ⟶ F y}
    (hf : Dg.IsHom g f) : f = 0 := by
  rw [← hf]; exact Dg.proj_eq_zero_of_not_mem hg f

theorem eq_sum_degs {x y : ι} (f : F x ⟶ F y) : f = ∑ g ∈ Dg.degs, Dg.proj g x y f := by
  obtain ⟨s, hs⟩ := Dg.sum x y f
  calc f = ∑ h ∈ s, Dg.proj h x y f := hs
    _ = ∑ h ∈ s, ∑ g ∈ Dg.degs, Dg.proj g x y (Dg.proj h x y f) := by
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        simp_rw [Dg.proj_proj]
        rw [Finset.sum_ite_eq]
        split_ifs with hh
        · rfl
        · exact Dg.proj_eq_zero_of_not_mem hh f
    _ = ∑ g ∈ Dg.degs, Dg.proj g x y f := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        rw [← map_sum, ← hs]

/-- Projection after a homogeneous morphism. -/
theorem proj_comp_left {a c : G} {x y z : ι} {m : F x ⟶ F y} (hm : Dg.IsHom a m)
    (f : F y ⟶ F z) : Dg.proj c x z (m ≫ f) = m ≫ Dg.proj (a⁻¹ * c) y z f := by
  have := Dg.proj_sandwich (g := c) hm (Dg.isHom_id z) f
  simpa using this

end HomGrading

namespace MeshData

variable {L : LocalFamily (k := k) F} (D : MeshData F L)
  [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (Dg : HomGrading (k := k) F G)

/-- **A map `V_X̃ → V_Ỹ` of modules over the lifted projectives**: a natural
family of maps `C̃(P_z, X̃) → C̃(P_z, Ỹ)`, `z = (p, g)`. -/
structure NatFam (X Y : ι × G) where
  φ : ∀ z : D.PV × G, (F z.1.1 ⟶ F X.1) →ₗ[k] (F z.1.1 ⟶ F Y.1)
  mem : ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
    φ z m ∈ Dg.part (z.2⁻¹ * Y.2) z.1.1 Y.1
  nat : ∀ (z z' : D.PV × G) (u : F z'.1.1 ⟶ F z.1.1) (m : F z.1.1 ⟶ F X.1),
    u ∈ Dg.part (z'.2⁻¹ * z.2) z'.1.1 z.1.1 → m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
    φ z' (u ≫ m) = u ≫ φ z m

variable {D Dg} {X Y : ι × G} (N : NatFam D Dg X Y)

namespace NatFam

/-- The term identity behind the module map. -/
theorem term (p q : D.PV) (a b : G) (μ : F p.1 ⟶ F q.1) (m : F q.1 ⟶ F X.1) :
    ∑ e ∈ Dg.degs, N.φ (p, X.2 * e⁻¹)
        (Dg.proj e p.1 X.1 (Dg.proj a p.1 q.1 μ ≫ Dg.proj b q.1 X.1 m)) =
      Dg.proj a p.1 q.1 μ ≫ N.φ (q, X.2 * b⁻¹) (Dg.proj b q.1 X.1 m) := by
  have key : N.φ (p, X.2 * (a * b)⁻¹) (Dg.proj a p.1 q.1 μ ≫ Dg.proj b q.1 X.1 m) =
      Dg.proj a p.1 q.1 μ ≫ N.φ (q, X.2 * b⁻¹) (Dg.proj b q.1 X.1 m) := by
    apply N.nat (q, X.2 * b⁻¹) (p, X.2 * (a * b)⁻¹)
    · rw [HomGrading.mem_part_iff, show (X.2 * (a * b)⁻¹)⁻¹ * (X.2 * b⁻¹) = a by group]
      exact Dg.isHom_proj _ _
    · rw [HomGrading.mem_part_iff, show (X.2 * b⁻¹)⁻¹ * X.2 = b by group]
      exact Dg.isHom_proj _ _
  simp_rw [Dg.proj_comp, apply_ite (N.φ _), map_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact key
  · rw [← key, Dg.eq_zero_of_not_mem h (Dg.isHom_comp (Dg.isHom_proj a μ) (Dg.isHom_proj b m)),
      map_zero]

/-- **The `A₀`-module map** `ev(X) → ev(Y)` assembled from the components. -/
def Ψ : Rep D.F0 (F X.1) →ₗ[Alg D.F0] Rep D.F0 (F Y.1) where
  toFun m p := ∑ e ∈ Dg.degs, N.φ (p, X.2 * e⁻¹) (Dg.proj e p.1 X.1 (m p))
  map_add' m m' := by
    funext p
    have h : ∀ e, Dg.proj e p.1 X.1 ((m + m') p) =
        Dg.proj e p.1 X.1 (m p) + Dg.proj e p.1 X.1 (m' p) := fun e ↦ map_add _ _ _
    simp only [h, map_add, Finset.sum_add_distrib]
    rfl
  map_smul' μ m := by
    funext p
    change ∑ e ∈ Dg.degs, N.φ (p, X.2 * e⁻¹) (Dg.proj e p.1 X.1 (∑ q, μ p q ≫ m q)) =
      ∑ q, μ p q ≫ ∑ e ∈ Dg.degs, N.φ (q, X.2 * e⁻¹) (Dg.proj e q.1 X.1 (m q))
    have hm : ∀ q, μ p q ≫ m q = ∑ a ∈ Dg.degs, ∑ b ∈ Dg.degs,
        Dg.proj a p.1 q.1 (μ p q) ≫ Dg.proj b q.1 X.1 (m q) := by
      intro q
      conv_lhs => rw [Dg.eq_sum_degs (μ p q), Dg.eq_sum_degs (m q)]
      rw [Preadditive.sum_comp]
      simp_rw [Preadditive.comp_sum]
    have hr : ∀ q, μ p q ≫ ∑ e ∈ Dg.degs, N.φ (q, X.2 * e⁻¹) (Dg.proj e q.1 X.1 (m q)) =
        ∑ a ∈ Dg.degs, ∑ b ∈ Dg.degs, ∑ e ∈ Dg.degs, N.φ (p, X.2 * e⁻¹)
          (Dg.proj e p.1 X.1 (Dg.proj a p.1 q.1 (μ p q) ≫ Dg.proj b q.1 X.1 (m q))) := by
      intro q
      simp_rw [term]
      conv_lhs => rw [Dg.eq_sum_degs (μ p q)]
      rw [Preadditive.sum_comp]
      simp_rw [Preadditive.comp_sum]
    simp_rw [hr, hm, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_comm]

/-- A morphism concentrated at one label. -/
def single (p : D.PV) (m : F p.1 ⟶ F X.1) : Rep D.F0 (F X.1) := Pi.single p m

theorem Ψ_apply (m : Rep D.F0 (F X.1)) (p : D.PV) :
    N.Ψ m p = ∑ e ∈ Dg.degs, N.φ (p, X.2 * e⁻¹) (Dg.proj e p.1 X.1 (m p)) := rfl

/-- `Ψ` on a homogeneous component concentrated at one label. -/
theorem Ψ_single (p : D.PV) {e : G} {m : F p.1 ⟶ F X.1} (hm : Dg.IsHom e m) :
    N.Ψ (single p m) p = N.φ (p, X.2 * e⁻¹) m := by
  rw [Ψ_apply, single, Pi.single_eq_same]
  simp_rw [Dg.proj_of_isHom hm, apply_ite (N.φ _), map_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Dg.eq_zero_of_not_mem h hm, map_zero]

end NatFam

include hfd in
/-- **Lemma 4.8, fullness**: a natural family is composition with a morphism
`X̃ → Ỹ` of the cover. -/
theorem NatFam.exists_hom : ∃ f : F X.1 ⟶ F Y.1, Dg.IsHom (X.2⁻¹ * Y.2) f ∧
    ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
      N.φ z m = m ≫ f := by
  obtain ⟨f₀, hf₀⟩ := D.hom_eq_repMap X.1 Y.1 N.Ψ
  -- the value on a homogeneous component
  have hval : ∀ (p : D.PV) (e : G) (m : F p.1 ⟶ F X.1), Dg.IsHom e m →
      m ≫ f₀ = N.φ (p, X.2 * e⁻¹) m := by
    intro p e m hm
    have := congrFun (hf₀ (NatFam.single p m)) p
    rw [N.Ψ_single p hm, repMap_apply, NatFam.single, Pi.single_eq_same] at this
    exact this.symm
  -- off-diagonal blocks vanish
  have hoff : ∀ g, g ≠ X.2⁻¹ * Y.2 → Dg.proj g X.1 Y.1 f₀ = 0 := by
    intro g hg
    refine D.repMap_eq_zero X.1 Y.1 _ fun m ↦ funext fun p ↦ ?_
    rw [repMap_apply]
    change m p ≫ _ = 0
    rw [Dg.eq_sum_degs (m p), Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun e _ ↦ ?_
    have he := Dg.isHom_proj e (m p)
    have h1 := Dg.proj_comp_left he f₀ (c := e * g)
    rw [show e⁻¹ * (e * g) = g by group] at h1
    rw [← h1, hval p e _ he]
    have hmem := N.mem (p, X.2 * e⁻¹) (Dg.proj e p.1 X.1 (m p))
      (by rw [HomGrading.mem_part_iff, show (X.2 * e⁻¹)⁻¹ * X.2 = e by group]; exact he)
    rw [HomGrading.mem_part_iff] at hmem
    rw [Dg.proj_of_isHom hmem, if_neg]
    intro h
    apply hg
    have : e * (X.2⁻¹ * Y.2) = e * g := by rw [← h]; group
    exact (mul_left_cancel this).symm
  have hhom : Dg.IsHom (X.2⁻¹ * Y.2) f₀ := by
    unfold HomGrading.IsHom
    conv_rhs => rw [Dg.eq_sum_degs f₀]
    by_cases hc : X.2⁻¹ * Y.2 ∈ Dg.degs
    · rw [Finset.sum_eq_single_of_mem _ hc fun g _ hg ↦ hoff g hg]
    · rw [Dg.proj_eq_zero_of_not_mem hc, Finset.sum_eq_zero fun g hg ↦ hoff g ?_]
      rintro rfl; exact hc hg
  refine ⟨f₀, hhom, fun z m hm ↦ ?_⟩
  rw [HomGrading.mem_part_iff] at hm
  rw [hval z.1 _ m hm]
  congr 2
  exact Prod.ext rfl (by simp)

include hfd in
/-- **Lemma 4.8, faithfulness**: a morphism killed by every lifted projective
vertex is zero. -/
theorem eq_zero_of_lifted {X Y : ι × G} (f : F X.1 ⟶ F Y.1)
    (h : ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
      m ≫ f = 0) : f = 0 := by
  refine D.repMap_eq_zero X.1 Y.1 _ fun m ↦ funext fun p ↦ ?_
  rw [repMap_apply]
  change m p ≫ f = 0
  rw [Dg.eq_sum_degs (m p), Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun e _ ↦ h (p, X.2 * e⁻¹) _ ?_
  rw [HomGrading.mem_part_iff, show (X.2 * e⁻¹)⁻¹ * X.2 = e by group]
  exact Dg.isHom_proj _ _

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
