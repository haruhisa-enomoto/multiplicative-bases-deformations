import MultiplicativeBasisDeformations.Foundations.RowSpan
import MultiplicativeBasisDeformations.Foundations.WeightEv

/-!
# Weighted decomposition of mesh errors (toward Proposition 12.8)

`deformation-refinements.tex:404–408`: "In each path degree `q ≥ 3`, decompose their current mesh
errors into the image of the original derivative and the span of the retained `p_i` of that
degree", with the choices made "separately in each degree and weight".

The retained tuples are rows `R_i = (x_i, w_i)` whose classes span the cokernels of the mesh
derivatives (`CokerSpan`). Every mesh family of degree `m + 1` is `D f + Σ_i c_i R_i`
(`exists_span`); if it has relative weight `γ`, then `f` can be taken of relative weight `γ` and
only the rows of weight `γ` occur (`exists_span_wt`), since the weight projections commute with
`D` (`wπ_meshDerivative`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  [Fintype Q.nonprojective] {I : Type} [Fintype I] [DecidableEq I]
  {Rw : I → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1}

variable (c) in
theorem mem_span_rows {m : ℕ} (g : MeshFamily c) (hg : ∀ x, g x ∈ degreePart c (m + 1) _ _) :
    g ∈ Submodule.span k {e | ∃ x w, w.length = m + 1 ∧ e = row c x w} := by
  have hsingle : ∀ x (e : obj c (Q.tau x).1 ⟶ obj c x.1),
      e ∈ degreePart c (m + 1) (Q.tau x).1 x.1 →
        Pi.single x e ∈ Submodule.span k {e | ∃ x w, w.length = m + 1 ∧ e = row c x w} := by
    intro x e he
    rw [degreePart_eq_span] at he
    induction he using Submodule.span_induction with
    | mem e he =>
        obtain ⟨w, hw, rfl⟩ := he
        exact Submodule.subset_span ⟨x, w, hw, rfl⟩
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add e₁ e₂ _ _ h₁ h₂ => rw [Pi.single_add]; exact add_mem h₁ h₂
    | smul t e _ he => rw [Pi.single_smul]; exact Submodule.smul_mem _ t he
  have hg' : g = ∑ x, Pi.single x (g x) := (Finset.univ_sum_single g).symm
  rw [hg']
  exact sum_mem fun x _ ↦ hsingle x (g x) (hg x)

/-- **Mesh errors modulo the image of `D` are combinations of the retained rows.** -/
theorem exists_span (hS : CokerSpan c (Set.range Rw)) {m : ℕ} (hm : 2 ≤ m) (g : MeshFamily c)
    (hg : ∀ x, g x ∈ degreePart c (m + 1) _ _) :
    ∃ f ∈ familiesDeg c m, ∃ cc : I → k, (∀ i, cc i ≠ 0 → (Rw i).2.length = m + 1) ∧
      g = meshDerivative c f + ∑ i, cc i • row c (Rw i).1 (Rw i).2 := by
  classical
  set S' : Submodule k (MeshFamily c) :=
    Submodule.span k (Set.range fun i : {i // (Rw i).2.length = m + 1} ↦
      row c (Rw i.1).1 (Rw i.1).2)
  have hrow : ∀ x w, w.length = m + 1 → row c x w ∈ imageD c m ⊔ S' := by
    intro x w hw
    have h := hS m hm x w hw
    unfold rowSpan at h
    have hmap : (fun R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1 ↦ rowClass c m R.1 R.2) ''
        {R | R ∈ Set.range Rw ∧ R.2.length = m + 1} =
        (imageD c m).mkQ '' (Set.range fun i : {i // (Rw i).2.length = m + 1} ↦
          row c (Rw i.1).1 (Rw i.1).2) := by
      ext e
      constructor
      · rintro ⟨R, ⟨⟨i, rfl⟩, hl⟩, rfl⟩
        exact ⟨_, ⟨⟨i, hl⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨⟨i, hl⟩, rfl⟩, rfl⟩
        exact ⟨Rw i, ⟨⟨i, rfl⟩, hl⟩, rfl⟩
    rw [hmap, ← Submodule.map_span] at h
    obtain ⟨s, hs, hse⟩ := h
    have : row c x w - s ∈ imageD c m := by
      rw [← Submodule.Quotient.eq]; exact hse.symm
    have e : row c x w = (row c x w - s) + s := by abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left this) (Submodule.mem_sup_right hs)
  have hgm : g ∈ imageD c m ⊔ S' := by
    have := mem_span_rows c g hg
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨x, w, hw, rfl⟩
    exact hrow x w hw
  obtain ⟨d, hd, s, hs, rfl⟩ := Submodule.mem_sup.1 hgm
  obtain ⟨f, hf, rfl⟩ := hd
  obtain ⟨cs, hcs⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hs
  refine ⟨f, hf, fun i ↦ if h : (Rw i).2.length = m + 1 then cs ⟨i, h⟩ else 0, fun i hi ↦ ?_, ?_⟩
  · by_contra h; exact hi (dif_neg h)
  · rw [meshDerivativeₗ_apply, ← hcs]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ (Rw i).2.length = m + 1)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i ↦ ¬(Rw i).2.length = m + 1)
      (fun i hi ↦ by dsimp only; rw [dif_neg (Finset.mem_filter.1 hi).2, zero_smul]), add_zero]
    rw [Finset.sum_subtype (Finset.univ.filter fun i ↦ (Rw i).2.length = m + 1)
      (p := fun i ↦ (Rw i).2.length = m + 1) (fun i ↦ by simp)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only
    rw [dif_pos j.2]

/-! ### Weights -/

variable {Wt : Type} [AddCommGroup Wt] (W : MeshWt Q Wt)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

include hfin in
/-- **The weight projections commute with the mesh derivative.** -/
theorem wπ_meshDerivative (γ : Wt) (f : ArrowFamily c) (x : Q.nonprojective) :
    wπ c W (W.ν x + γ) _ _ (meshDerivative c f x) =
      meshDerivative c (fun a ↦ wπ c W (W.w a.2.2 + γ) _ _ (f a)) x := by
  simp only [meshDerivative, map_sum, map_smul, map_add]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  congr 1
  · have := wπ_comp_right W hfin (arrowMor_mem_wP W a.2) (W.w (Q.mate x a.1 a.2) + γ)
      (f ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)
    rw [show W.w (Q.mate x a.1 a.2) + γ + W.w a.2 = W.ν x + γ by
      rw [add_right_comm, W.mesh x a]] at this
    exact this
  · have := wπ_comp_left W hfin (arrowMor_mem_wP W (Q.mate x a.1 a.2)) (W.w a.2 + γ)
      (f ⟨a.1, x.1, a.2⟩)
    rw [show W.w (Q.mate x a.1 a.2) + (W.w a.2 + γ) = W.ν x + γ by
      rw [← add_assoc, W.mesh x a]] at this
    exact this

variable {χ : I → Wt}

include hfin in
/-- **Weighted decomposition of a homogeneous mesh error.** -/
theorem exists_span_wt (hS : CokerSpan c (Set.range Rw))
    (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i) {m : ℕ} (hm : 2 ≤ m) (γ : Wt)
    (g : MeshFamily c) (hg : ∀ x, g x ∈ degreePart c (m + 1) _ _)
    (hgw : ∀ x, g x ∈ wP c W (W.ν x + γ) _ _) :
    ∃ f : ArrowFamily c, (∀ a, f a ∈ degreePart c m a.1 a.2.1 ∧
        f a ∈ wP c W (W.w a.2.2 + γ) a.1 a.2.1) ∧
      ∃ cc : I → k, (∀ i, cc i ≠ 0 → (Rw i).2.length = m + 1 ∧ χ i = γ) ∧
        g = meshDerivative c f + ∑ i, cc i • row c (Rw i).1 (Rw i).2 := by
  classical
  obtain ⟨f, hf, cc, hcc, hg'⟩ := exists_span hS hm g hg
  refine ⟨fun a ↦ wπ c W (W.w a.2.2 + γ) _ _ (f a), fun a ↦ ⟨wπ_mem_degreePart W _ (hf a),
    wπ_mem W _ _⟩, fun i ↦ if χ i = γ then cc i else 0, fun i hi ↦ ?_, ?_⟩
  · dsimp only at hi
    by_cases h : χ i = γ
    · rw [if_pos h] at hi; exact ⟨hcc i hi, h⟩
    · rw [if_neg h] at hi; exact absurd rfl hi
  · funext x
    have e1 : g x = wπ c W (W.ν x + γ) _ _ (g x) := by
      rw [wπ_of_mem W (hgw x), if_pos rfl]
    rw [e1, hg', Pi.add_apply, map_add, wπ_meshDerivative W hfin, Pi.add_apply]
    congr 1
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [row]
    by_cases hx : x = (Rw i).1
    · subst hx
      simp only [Pi.single_eq_same]
      rw [wπ_of_mem W (show pathMor c (Rw i).2 ∈ wP c W (W.ν (Rw i).1 + χ i) _ _ by
          rw [← hwt i]; exact pathMor_mem_wP W _)]
      by_cases h : χ i = γ
      · rw [if_pos (by rw [h]), if_pos h]
      · rw [if_neg (fun h' ↦ h (add_left_cancel h')), if_neg h, zero_smul, smul_zero]
    · simp [Pi.single_eq_of_ne hx]

end MeshWalk

end MultiplicativeBasisDeformations
