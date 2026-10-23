module

public import MultiplicativeBasisDeformations.Foundations.MGrading
public import MultiplicativeBasisDeformations.Foundations.HomBasis

/-!
# Coordinates of a simultaneous integer grading

A grading by an abelian group (for simultaneous integer weights, `ℤʳ`) gives an integer grading
for each coordinate `M →+ ℤ` (`MGr.coord`); their projections preserve each other's homogeneous elements and those of
any grading commuting with the `ℤʳ`-grading (`coord_preserve`). A `ℤ`-grading and a commuting
grading by an abelian group combine into one grading (`MGr.comb`), and a finite-dimensional
space has a basis homogeneous for both (`exists_homBasis_comb`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace MGr

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

section Coord

variable {M : Type*} [AddCommGroup M] [DecidableEq M] (G : MGr R M N)

/-- **The grading by a coordinate `φ : M → ℤ` of the weight.** -/
def coord (i : M →+ ℤ) : GExt.ZGr (R := R) N where
  proj n := ∑ g ∈ G.supp with i g = n, G.proj g
  supp := G.supp.image (fun g ↦ i g)
  proj_proj p q x := by
    classical
    simp only [LinearMap.sum_apply, map_sum]
    simp_rw [G.proj_proj]
    rw [Finset.sum_comm]
    split_ifs with hqp
    · subst hqp
      refine Finset.sum_congr rfl fun h hh ↦ ?_
      rw [Finset.sum_eq_single_of_mem h hh]
      · rw [if_pos rfl]
      · intro g _ hne; rw [if_neg hne]
    · refine Finset.sum_eq_zero fun h hh ↦ Finset.sum_eq_zero fun g hg ↦ ?_
      rw [if_neg]
      rintro rfl
      exact hqp ((Finset.mem_filter.1 hh).2.symm.trans (Finset.mem_filter.1 hg).2).symm
  proj_out n hn := by
    refine Finset.sum_eq_zero fun g hg ↦ ?_
    exact absurd (Finset.mem_image.2 ⟨g, (Finset.mem_filter.1 hg).1,
      (Finset.mem_filter.1 hg).2⟩) hn
  sum x := by
    classical
    conv_lhs => rw [G.sum x]
    simp only [LinearMap.sum_apply]
    exact (Finset.sum_fiberwise_of_maps_to (fun g hg ↦ Finset.mem_image_of_mem (fun g ↦ i g) hg) _).symm

theorem coord_proj (i : M →+ ℤ) (n : ℤ) (x : N) :
    (G.coord i).proj n x = ∑ g ∈ G.supp with i g = n, G.proj g x := by
  simp [coord]

theorem coord_isHom {g : M} {x : N} (h : G.IsHom g x) (i : M →+ ℤ) :
    (G.coord i).IsHom (i g) x := by
  classical
  change (G.coord i).proj (i g) x = x
  rw [coord_proj]
  simp_rw [G.proj_of_isHom h]
  rw [Finset.sum_ite_eq]
  by_cases hg : g ∈ G.supp
  · simp [hg]
  · rw [if_neg (fun h' ↦ hg (Finset.mem_filter.1 h').1), G.eq_zero_of_isHom_out h hg]

/-- **Coordinate projections preserve what the projections of `G` preserve.** -/
theorem coord_preserve {P : N → Prop} (h0 : ∀ x y, P x → P y → P (x + y)) (hz : P 0)
    (hG : ∀ g x, P x → P (G.proj g x)) (i : M →+ ℤ) (n : ℤ) {x : N} (hx : P x) :
    P ((G.coord i).proj n x) := by
  classical
  rw [coord_proj]
  induction (G.supp.filter fun g ↦ i g = n) using Finset.induction_on with
  | empty => simpa using hz
  | insert g s hg ih => rw [Finset.sum_insert hg]; exact h0 _ _ (hG g x hx) ih

theorem coord_proj_proj (j : M →+ ℤ) (p : ℤ) (g : M) (y : N) :
    (G.coord j).proj p (G.proj g y) = if g ∈ G.supp ∧ j g = p then G.proj g y else 0 := by
  classical
  rw [coord_proj]
  simp_rw [G.proj_proj]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter]

/-- The projections of `G` preserve the homogeneous elements of the coordinates. -/
theorem proj_coord (j : M →+ ℤ) (p : ℤ) (g : M) {y : N} (hy : (G.coord j).IsHom p y) :
    (G.coord j).IsHom p (G.proj g y) := by
  classical
  change (G.coord j).proj p (G.proj g y) = G.proj g y
  rw [coord_proj_proj]
  split_ifs with hg
  · rfl
  · rw [← hy, coord_proj, map_sum]
    simp_rw [G.proj_proj]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_filter]
    rw [if_neg hg]

/-- The coordinate projections preserve the homogeneous elements of the other coordinates. -/
theorem coord_coord (i j : M →+ ℤ) (n p : ℤ) {x : N} (hx : (G.coord j).IsHom p x) :
    (G.coord j).IsHom p ((G.coord i).proj n x) :=
  G.coord_preserve (P := (G.coord j).IsHom p) (fun _ _ ↦ (G.coord j).isHom_add)
    ((G.coord j).isHom_zero p) (fun g _ hy ↦ G.proj_coord j p g hy) i n hx

end Coord

/-! ### Homogeneous bases -/

section Basis

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [DecidableEq M] {N' : Type*}
  [AddCommGroup N'] [Module k N'] (G : MGr k M N')

/-- The homogeneous component of weight `g`, indexed by the support. -/
abbrev homPart (g : G.supp) : Submodule k N' := LinearMap.range (G.proj g)

theorem proj_homPart {g : M} {h : G.supp} {x : N'} (hx : x ∈ G.homPart h) :
    G.proj g x = if (h : M) = g then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [G.proj_proj]

theorem isInternal_homPart : DirectSum.IsInternal G.homPart := by
  classical
  let inv : N' →ₗ[k] DirectSum G.supp (fun g ↦ G.homPart g) :=
    ∑ g : G.supp, (DirectSum.lof k G.supp (fun g ↦ G.homPart g) g) ∘ₗ (G.proj g).rangeRestrict
  have hrr : ∀ (g : G.supp) (x : N'), ((G.proj g).rangeRestrict x : N') = G.proj g x :=
    fun _ _ ↦ rfl
  have hr : ∀ x, DirectSum.coeLinearMap G.homPart (inv x) = x := by
    intro x
    simp only [inv, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
      DirectSum.coeLinearMap_lof, hrr]
    conv_rhs => rw [G.sum x]
    rw [← Finset.sum_attach G.supp]
    rfl
  have hl : ∀ f, inv (DirectSum.coeLinearMap G.homPart f) = f := by
    intro f
    induction f using DirectSum.induction_on with
    | zero => simp
    | of q y =>
        rw [DirectSum.coeLinearMap_of]
        simp only [inv, LinearMap.sum_apply, LinearMap.comp_apply]
        rw [Finset.sum_eq_single q]
        · rw [DirectSum.lof_eq_of]
          congr 1
          apply Subtype.ext
          rw [hrr, G.proj_homPart y.2, if_pos rfl]
        · intro p _ hp
          have : (G.proj p).rangeRestrict y = 0 := by
            apply Subtype.ext
            rw [hrr, G.proj_homPart y.2, if_neg (fun h ↦ hp (Subtype.ext h).symm)]
            rfl
          rw [this, map_zero]
        · intro h; exact absurd (Finset.mem_univ q) h
    | add f f' hf hf' => rw [map_add, map_add, hf, hf']
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

/-- **Homogeneous bases** for a grading by an abelian group. -/
theorem exists_homBasis [FiniteDimensional k N'] :
    ∃ (n : ℕ) (β : Module.Basis (Fin n) k N') (w : Fin n → M), ∀ i, G.IsHom (w i) (β i) := by
  classical
  set B := (G.isInternal_homPart).collectedBasis fun g ↦ Module.finBasis k (G.homPart g)
  refine ⟨_, B.reindex (Fintype.equivFin _), fun i ↦ ((Fintype.equivFin _).symm i).1, fun i ↦ ?_⟩
  rw [Module.Basis.reindex_apply]
  obtain ⟨y, hy⟩ := (G.isInternal_homPart).collectedBasis_mem
    (fun g ↦ Module.finBasis k (G.homPart g)) ((Fintype.equivFin _).symm i)
  change G.proj _ _ = _
  rw [← hy, G.proj_proj, if_pos rfl]

end Basis

/-! ### Degree and weight together -/

section Comb

variable {M : Type*} [AddCommGroup M] [DecidableEq M] (o : GExt.ZGr (R := R) N) (G : MGr R M N)
  (hc : ∀ p g x, o.proj p (G.proj g x) = G.proj g (o.proj p x))

include hc in
/-- **The combined grading by degree and weight.** -/
def comb : MGr R (ℤ × M) N where
  proj pg := o.proj pg.1 ∘ₗ G.proj pg.2
  supp := o.supp ×ˢ G.supp
  proj_proj pg qh x := by
    obtain ⟨p, g⟩ := pg
    obtain ⟨q, h⟩ := qh
    simp only [LinearMap.comp_apply]
    rw [← hc q g (G.proj h x), G.proj_proj]
    by_cases hhg : h = g
    · subst hhg
      rw [if_pos rfl, o.proj_proj]
      by_cases hqp : q = p
      · subst hqp; simp
      · rw [if_neg hqp, if_neg (fun e ↦ hqp (Prod.ext_iff.1 e).1)]
    · rw [if_neg hhg, map_zero, map_zero, if_neg (fun e ↦ hhg (Prod.ext_iff.1 e).2)]
  proj_out pg hpg := by
    rw [Finset.mem_product, not_and_or] at hpg
    rcases hpg with h | h
    · rw [o.proj_out _ h, LinearMap.zero_comp]
    · rw [G.proj_out _ h, LinearMap.comp_zero]
  sum x := by
    rw [Finset.sum_product]
    conv_lhs => rw [o.sum x]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    conv_lhs => rw [G.sum (o.proj p x)]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp only [LinearMap.comp_apply]
    rw [hc]

theorem comb_isHom {p : ℤ} {g : M} {x : N} (h : (comb o G hc).IsHom (p, g) x) :
    o.IsHom p x ∧ G.IsHom g x := by
  change o.proj p (G.proj g x) = x at h
  constructor
  · change o.proj p x = x
    conv_lhs => rw [← h]
    rw [o.proj_proj, if_pos rfl, h]
  · change G.proj g x = x
    conv_lhs => rw [← h]
    rw [← hc, G.proj_proj, if_pos rfl, h]

end Comb

end MGr

end MultiplicativeBasisDeformations
