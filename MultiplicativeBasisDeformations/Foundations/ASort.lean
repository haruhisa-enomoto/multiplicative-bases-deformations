import MultiplicativeBasisDeformations.Foundations.StarAut
import MultiplicativeBasisDeformations.Foundations.ReRoot
import MultiplicativeBasisDeformations.Foundations.CoveringIdeals

/-!
# Long paths of `Π(A_N)` vanish

`characteristic-two-mesh-calculations.tex`: "For the preprojective category of
`A_N`, … the interior relations interchange `s₊s₋` and `s₋s₊`, while the endpoint
backtracks are zero. For paths starting at `i`, sorting the steps in either order
shows that the paths `s₊^a s₋^b`, `0 ≤ a ≤ N − i`, `0 ≤ b ≤ i − 1`, span. An
interchange at an endpoint makes the path zero. … In particular all paths of degree
at least `N` are zero."

We work on the path rooted at an end (`starTree L` with one arm, depths
`0, …, L 0 + 1`). A path has `rc` steps to the right (away from the root) and `lc` steps
to the left. Replacing a peak `u → u+1 → u` by the dip `u → u−1 → u` (the relation at
`u`), or by zero at the root, lowers the number `inv` of pairs (right step, later left
step). A path without such pairs makes all its left steps first, so it has at most
`depth` left steps. Hence a path with more left steps than its start depth lies in the
ideal (`left_overflow`); symmetrically for right steps (`right_overflow`), and every
path of length at least `L 0 + 2` lies in the ideal (`long_mem`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace ASort

open OrientedTree

variable {L : Fin 1 → ℕ}

/-- The depth of a vertex of the doubled path. -/
abbrev dep (u : (starTree L).Dbl) : ℕ := starDepth (u : StarV L)

theorem arrow_dep {u v : (starTree L).Dbl} (e : u ⟶ v) : dep v = dep u + 1 ∨ dep u = dep v + 1 :=
  (ReRoot.adj_one (u : StarV L) (v : StarV L)).1 e.down

theorem dep_injective {u v : (starTree L).Dbl} (h : dep u = dep v) : u = v :=
  depth_injective (L := L) h

/-- A step to the right. -/
def isR {u v : (starTree L).Dbl} (_ : u ⟶ v) : Prop := dep v = dep u + 1

instance {u v : (starTree L).Dbl} (e : u ⟶ v) : Decidable (isR e) := by unfold isR; infer_instance

/-- The numbers of right steps, left steps and inversions. -/
def rc : ∀ {a b : (starTree L).Dbl}, Quiver.Path a b → ℕ
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p e => rc p + if isR e then 1 else 0

def lc : ∀ {a b : (starTree L).Dbl}, Quiver.Path a b → ℕ
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p e => lc p + if isR e then 0 else 1

def inv : ∀ {a b : (starTree L).Dbl}, Quiver.Path a b → ℕ
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p e => inv p + if isR e then 0 else rc p

theorem dep_end {a : (starTree L).Dbl} : ∀ {b : (starTree L).Dbl} (p : Quiver.Path a b),
    dep b + lc p = dep a + rc p
  | _, Quiver.Path.nil => by simp [lc, rc]
  | _, Quiver.Path.cons p e => by
      have ih := dep_end p
      simp only [lc, rc]
      split_ifs with h
      · unfold isR at h; omega
      · rcases arrow_dep e with h' | h' <;> [exact absurd h' h; omega]

theorem length_eq {a : (starTree L).Dbl} : ∀ {b : (starTree L).Dbl} (p : Quiver.Path a b),
    p.length = rc p + lc p
  | _, Quiver.Path.nil => by simp [rc, lc]
  | _, Quiver.Path.cons p e => by
      rw [Quiver.Path.length_cons, length_eq p]
      simp only [rc, lc]
      split_ifs <;> omega

theorem rc_comp {a b : (starTree L).Dbl} (p : Quiver.Path a b) :
    ∀ {c : (starTree L).Dbl} (q : Quiver.Path b c), rc (p.comp q) = rc p + rc q
  | _, Quiver.Path.nil => by simp [rc]
  | _, Quiver.Path.cons q e => by
      rw [Quiver.Path.comp_cons]; simp only [rc]; rw [rc_comp p q]; omega

theorem lc_comp {a b : (starTree L).Dbl} (p : Quiver.Path a b) :
    ∀ {c : (starTree L).Dbl} (q : Quiver.Path b c), lc (p.comp q) = lc p + lc q
  | _, Quiver.Path.nil => by simp [lc]
  | _, Quiver.Path.cons q e => by
      rw [Quiver.Path.comp_cons]; simp only [lc]; rw [lc_comp p q]; omega

theorem inv_comp {a b : (starTree L).Dbl} (p : Quiver.Path a b) :
    ∀ {c : (starTree L).Dbl} (q : Quiver.Path b c), inv (p.comp q) = inv p + inv q + rc p * lc q
  | _, Quiver.Path.nil => by simp [inv, lc]
  | _, Quiver.Path.cons q e => by
      rw [Quiver.Path.comp_cons]
      simp only [inv, lc]
      rw [inv_comp p q, rc_comp]
      split_ifs <;> ring

/-- **Sorted paths make their left steps first.** -/
theorem sorted_lc {a : (starTree L).Dbl} : ∀ {b : (starTree L).Dbl} (p : Quiver.Path a b),
    inv p = 0 → lc p ≤ dep a
  | _, Quiver.Path.nil, _ => by simp [lc]
  | _, Quiver.Path.cons p e, h => by
      simp only [inv] at h
      have h1 : inv p = 0 := by omega
      have ih := sorted_lc p h1
      simp only [lc]
      split_ifs with he
      · omega
      · rw [if_neg he] at h
        have hr : rc p = 0 := by omega
        have hd := dep_end p
        rcases arrow_dep e with h' | h'
        · exact absurd h' he
        · omega

theorem back_eq {u v x : (starTree L).Dbl} (e₁ : u ⟶ v) (e₂ : v ⟶ x) (h1 : isR e₁)
    (h2 : ¬ isR e₂) : x = u := by
  apply dep_injective
  have := arrow_dep e₂
  unfold isR at h1 h2
  omega

/-- **A path with an inversion contains a peak.** -/
theorem exists_peak {a : (starTree L).Dbl} : ∀ {b : (starTree L).Dbl} (p : Quiver.Path a b),
    0 < inv p → ∃ (u v : (starTree L).Dbl) (q : Quiver.Path a u) (e₁ : u ⟶ v) (e₂ : v ⟶ u)
      (r : Quiver.Path u b), isR e₁ ∧ p = q.comp (e₁.toPath.comp (e₂.toPath.comp r))
  | _, Quiver.Path.nil, h => by simp [inv] at h
  | _, Quiver.Path.cons Quiver.Path.nil e, h => by simp [inv, rc] at h
  | _, Quiver.Path.cons (Quiver.Path.cons p' e') e, h => by
      by_cases hp : 0 < inv (p'.cons e')
      · obtain ⟨u, v, q, e₁, e₂, r, hv, hpq⟩ := exists_peak (p'.cons e') hp
        refine ⟨u, v, q, e₁, e₂, r.cons e, hv, ?_⟩
        rw [hpq]; simp [Quiver.Path.comp_cons]
      · simp only [inv] at h hp
        by_cases he : isR e
        · rw [if_pos he] at h; omega
        · rw [if_neg he] at h
          have he' : isR e' := by
            by_contra hne
            rw [if_neg hne] at hp h
            simp only [rc, if_neg hne] at h
            omega
          obtain rfl := back_eq e' e he' he
          exact ⟨_, _, p', e', e, Quiver.Path.nil, he', by simp⟩

/-! ### The relation at a vertex of the path -/

variable (k : Type*) [Field k]

/-- The backtrack along an arrow. -/
def bt {u v : (starTree L).Dbl} (e : u ⟶ v) : Quiver.Path u u :=
  e.toPath.comp (Quiver.Hom.toPath (show v ⟶ u from ⟨e.down.symm⟩))

theorem bt_eq {u v : (starTree L).Dbl} (e₁ : u ⟶ v) (e₂ : v ⟶ u) :
    bt e₁ = e₁.toPath.comp e₂.toPath := by
  rw [bt, Subsingleton.elim (⟨e₁.down.symm⟩ : v ⟶ u) e₂]

theorem rel_mem (u : (starTree L).Dbl) :
    (starTree L).preprojRel k u ∈ ((starTree L).preproj k).ideal _ _ := by
  have := ((starTree L).preproj k).comp_rel_comp_mem (k := k) u (𝟙 _) (𝟙 _)
  simp only [Category.id_comp, Category.comp_id] at this
  exact this

/-- The neighbours of a vertex are its depth neighbours. -/
theorem out_cases (u : (starTree L).Dbl) (x : (Σ y : (starTree L).Dbl, u ⟶ y)) :
    dep x.1 = dep u + 1 ∨ dep u = dep x.1 + 1 := arrow_dep x.2

theorem out_eq {u : (starTree L).Dbl} (x y : (Σ y : (starTree L).Dbl, u ⟶ y)) (h : dep x.1 = dep y.1) :
    x = y := by
  obtain ⟨x, a⟩ := x
  obtain ⟨y, b⟩ := y
  obtain rfl : x = y := dep_injective h
  rw [Subsingleton.elim a b]

/-- **The relation at a vertex**: the peak through the right neighbour lies in the ideal
at the root, and is a multiple of the dip modulo the ideal otherwise. -/
theorem peak_rel {u v : (starTree L).Dbl} (e₁ : u ⟶ v) (e₂ : v ⟶ u) (hv : isR e₁) :
    LinearPaths.path (k := k) (e₁.toPath.comp e₂.toPath) ∈ ((starTree L).preproj k).ideal _ _ ∨
      ∃ (w : (starTree L).Dbl) (d₁ : u ⟶ w) (d₂ : w ⟶ u) (c : k), ¬ isR d₁ ∧ isR d₂ ∧
        LinearPaths.path (k := k) (e₁.toPath.comp e₂.toPath) -
          c • LinearPaths.path (d₁.toPath.comp d₂.toPath) ∈ ((starTree L).preproj k).ideal _ _ := by
  classical
  have hrel := rel_mem k u
  unfold OrientedTree.preprojRel at hrel
  have hsv : (((starTree L).sgn k (u : StarV L) (v : StarV L) : kˣ) : k) ≠ 0 := Units.ne_zero _
  by_cases h0 : dep u = 0
  · left
    rw [Fintype.sum_eq_single (⟨v, e₁⟩ : (Σ y : (starTree L).Dbl, u ⟶ y))] at hrel
    · have := Submodule.smul_mem _ (((starTree L).sgn k (u : StarV L) (v : StarV L) : kˣ) : k)⁻¹ hrel
      rwa [smul_smul, inv_mul_cancel₀ hsv, one_smul, ← bt, bt_eq e₁ e₂] at this
    · intro x hx
      exfalso
      apply hx
      apply out_eq
      show dep x.1 = dep v
      rcases out_cases u x with h | h
      · unfold isR at hv; omega
      · omega
  · right
    have hw : dep u - 1 ≤ L 0 + 1 := by
      have h1 : dep u ≤ L 0 + 1 := depth_le (L := L) (u : StarV L)
      omega
    set w : (starTree L).Dbl := (starTree L).toDbl (ofDep L (dep u - 1) hw)
    have hwd : dep w = dep u - 1 := starDepth_ofDep _ _
    have hadj : (starTree L).G.Adj (u : StarV L) (w : StarV L) :=
      (ReRoot.adj_one _ _).2 (Or.inr (show dep u = dep w + 1 by rw [hwd]; omega))
    let d₁ : u ⟶ w := ⟨hadj⟩
    let d₂ : w ⟶ u := ⟨hadj.symm⟩
    have hsw : (((starTree L).sgn k (u : StarV L) (w : StarV L) : kˣ) : k) ≠ 0 := Units.ne_zero _
    refine ⟨w, d₁, d₂, -((((starTree L).sgn k (u : StarV L) (v : StarV L) : kˣ) : k)⁻¹ *
      (((starTree L).sgn k (u : StarV L) (w : StarV L) : kˣ) : k)), ?_, ?_, ?_⟩
    · unfold isR; omega
    · unfold isR; change dep u = dep w + 1; omega
    · rw [Fintype.sum_eq_add (⟨v, e₁⟩ : (Σ y : (starTree L).Dbl, u ⟶ y)) ⟨w, d₁⟩
        (fun h ↦ by
          have := congrArg (fun x : (Σ y : (starTree L).Dbl, u ⟶ y) ↦ dep x.1) h
          change dep v = dep w at this
          unfold isR at hv; rw [hwd] at this; omega)] at hrel
      · have := Submodule.smul_mem _ (((starTree L).sgn k (u : StarV L) (v : StarV L) : kˣ) : k)⁻¹
          hrel
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hsv, one_smul, ← bt, ← bt, bt_eq e₁ e₂,
          bt_eq d₁ d₂] at this
        rw [neg_smul, sub_neg_eq_add]
        exact this
      · intro x ⟨hx1, hx2⟩
        exfalso
        rcases out_cases u x with h | h
        · exact hx1 (out_eq _ _ (show dep x.1 = dep v by unfold isR at hv; omega))
        · exact hx2 (out_eq _ _ (show dep x.1 = dep w by rw [hwd]; omega))

/-! ### Sorting -/

theorem rc_toPath {u v : (starTree L).Dbl} (e : u ⟶ v) : rc e.toPath = if isR e then 1 else 0 := by
  change rc (Quiver.Path.cons Quiver.Path.nil e) = _
  simp only [rc, zero_add]

theorem lc_toPath {u v : (starTree L).Dbl} (e : u ⟶ v) : lc e.toPath = if isR e then 0 else 1 := by
  change lc (Quiver.Path.cons Quiver.Path.nil e) = _
  simp only [lc, zero_add]

theorem inv_toPath {u v : (starTree L).Dbl} (e : u ⟶ v) : inv e.toPath = 0 := by
  change inv (Quiver.Path.cons Quiver.Path.nil e) = _
  simp only [inv, rc]; split_ifs <;> rfl

/-- **A path with more left steps than its start depth lies in the ideal.** -/
theorem left_overflow : ∀ (n : ℕ) {a b : (starTree L).Dbl} (p : Quiver.Path a b), inv p = n →
    dep a < lc p → LinearPaths.path (k := k) p ∈ ((starTree L).preproj k).ideal _ _ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b p hn hlc
  rcases Nat.eq_zero_or_pos (inv p) with h0 | hpos
  · exact absurd (sorted_lc p h0) (by omega)
  obtain ⟨u, v, q, e₁, e₂, r, hR, rfl⟩ := exists_peak p hpos
  have he₂ : ¬ isR e₂ := by unfold isR at hR ⊢; omega
  rw [show q.comp (e₁.toPath.comp (e₂.toPath.comp r)) = q.comp ((e₁.toPath.comp e₂.toPath).comp r)
      from congrArg q.comp (Quiver.Path.comp_assoc _ _ _).symm, ← LinearPaths.path_comp_path,
    ← LinearPaths.path_comp_path]
  rcases peak_rel k e₁ e₂ hR with hI | ⟨w, d₁, d₂, c, hd₁, hd₂, hmem⟩
  · exact ((starTree L).preproj k).comp_mem_ideal _ (((starTree L).preproj k).mem_ideal_comp hI _)
  · set p' := q.comp (d₁.toPath.comp (d₂.toPath.comp r))
    have hinv : inv p' + 1 = inv (q.comp (e₁.toPath.comp (e₂.toPath.comp r))) := by
      simp only [p', inv_comp, rc_comp, lc_comp, inv_toPath, rc_toPath, lc_toPath, if_pos hR,
        if_neg he₂, if_neg hd₁, if_pos hd₂]
      ring
    have hlc' : lc p' = lc (q.comp (e₁.toPath.comp (e₂.toPath.comp r))) := by
      simp only [p', lc_comp, lc_toPath, if_pos hR, if_neg he₂, if_neg hd₁, if_pos hd₂]
      omega
    have hp' := ih (inv p') (by omega) p' rfl (by rw [hlc']; exact hlc)
    have e : LinearPaths.path (k := k) q ≫ LinearPaths.path (e₁.toPath.comp e₂.toPath) ≫
        LinearPaths.path r = c • LinearPaths.path (k := k) p' +
          LinearPaths.path q ≫ (LinearPaths.path (e₁.toPath.comp e₂.toPath) -
            c • LinearPaths.path (d₁.toPath.comp d₂.toPath)) ≫ LinearPaths.path r := by
      simp only [p', Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
        Linear.comp_smul, ← LinearPaths.path_comp_path]
      simp only [Category.assoc]
      abel
    rw [e]
    exact add_mem (Submodule.smul_mem _ c hp')
      (((starTree L).preproj k).comp_mem_ideal _ (((starTree L).preproj k).mem_ideal_comp hmem _))

/-! ### The mirror image: right steps -/

/-- The number of pairs (left step, later right step). -/
def inv2 : ∀ {a b : (starTree L).Dbl}, Quiver.Path a b → ℕ
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p e => inv2 p + if isR e then lc p else 0

theorem inv2_comp {a b : (starTree L).Dbl} (p : Quiver.Path a b) :
    ∀ {c : (starTree L).Dbl} (q : Quiver.Path b c), inv2 (p.comp q) = inv2 p + inv2 q + lc p * rc q
  | _, Quiver.Path.nil => by simp [inv2, rc]
  | _, Quiver.Path.cons q e => by
      rw [Quiver.Path.comp_cons]
      simp only [inv2, rc]
      rw [inv2_comp p q, lc_comp]
      split_ifs <;> ring

theorem inv2_toPath {u v : (starTree L).Dbl} (e : u ⟶ v) : inv2 e.toPath = 0 := by
  change inv2 (Quiver.Path.cons Quiver.Path.nil e) = _
  simp only [inv2, lc]; split_ifs <;> rfl

theorem dep_le_of_arrow {u v : (starTree L).Dbl} (_ : u ⟶ v) : dep v ≤ L 0 + 1 :=
  depth_le (L := L) (v : StarV L)

theorem sorted_rc {a : (starTree L).Dbl} : ∀ {b : (starTree L).Dbl} (p : Quiver.Path a b),
    inv2 p = 0 → dep a + rc p ≤ L 0 + 1
  | _, Quiver.Path.nil, _ => by simp [rc]; exact depth_le (L := L) (a : StarV L)
  | _, Quiver.Path.cons p e, h => by
      simp only [inv2] at h
      have h1 : inv2 p = 0 := by omega
      have ih := sorted_rc p h1
      simp only [rc]
      split_ifs with he
      · rw [if_pos he] at h
        have hl : lc p = 0 := by omega
        have hd := dep_end p
        have hb' := dep_le_of_arrow e
        unfold isR at he
        omega
      · omega

theorem fwd_eq {u w x : (starTree L).Dbl} (e₁ : u ⟶ w) (e₂ : w ⟶ x) (h1 : ¬ isR e₁)
    (h2 : isR e₂) : x = u := by
  apply dep_injective
  have := arrow_dep e₁
  unfold isR at h1 h2
  omega

theorem exists_dip {a : (starTree L).Dbl} : ∀ {b : (starTree L).Dbl} (p : Quiver.Path a b),
    0 < inv2 p → ∃ (u w : (starTree L).Dbl) (q : Quiver.Path a u) (e₁ : u ⟶ w) (e₂ : w ⟶ u)
      (r : Quiver.Path u b), ¬ isR e₁ ∧ p = q.comp (e₁.toPath.comp (e₂.toPath.comp r))
  | _, Quiver.Path.nil, h => by simp [inv2] at h
  | _, Quiver.Path.cons Quiver.Path.nil e, h => by simp [inv2, lc] at h
  | _, Quiver.Path.cons (Quiver.Path.cons p' e') e, h => by
      by_cases hp : 0 < inv2 (p'.cons e')
      · obtain ⟨u, w, q, e₁, e₂, r, hv, hpq⟩ := exists_dip (p'.cons e') hp
        refine ⟨u, w, q, e₁, e₂, r.cons e, hv, ?_⟩
        rw [hpq]; simp [Quiver.Path.comp_cons]
      · simp only [inv2] at h hp
        by_cases he : isR e
        · rw [if_pos he] at h
          have he' : ¬ isR e' := by
            intro hne
            rw [if_pos hne] at hp h
            simp only [lc, if_pos hne] at h
            omega
          obtain rfl := fwd_eq e' e he' he
          exact ⟨_, _, p', e', e, Quiver.Path.nil, he', by simp⟩
        · rw [if_neg he] at h; omega

/-- **The relation at a vertex, mirrored**: the dip lies in the ideal at the far end, and
is a multiple of the peak modulo the ideal otherwise. -/
theorem dip_rel {u w : (starTree L).Dbl} (e₁ : u ⟶ w) (e₂ : w ⟶ u) (hw : ¬ isR e₁) :
    LinearPaths.path (k := k) (e₁.toPath.comp e₂.toPath) ∈ ((starTree L).preproj k).ideal _ _ ∨
      ∃ (v : (starTree L).Dbl) (d₁ : u ⟶ v) (d₂ : v ⟶ u) (c : k), isR d₁ ∧ ¬ isR d₂ ∧
        LinearPaths.path (k := k) (e₁.toPath.comp e₂.toPath) -
          c • LinearPaths.path (d₁.toPath.comp d₂.toPath) ∈ ((starTree L).preproj k).ideal _ _ := by
  classical
  have hrel := rel_mem k u
  unfold OrientedTree.preprojRel at hrel
  have hwd : dep u = dep w + 1 := by
    rcases arrow_dep e₁ with h | h
    · exact absurd h hw
    · exact h
  have hsw : (((starTree L).sgn k (u : StarV L) (w : StarV L) : kˣ) : k) ≠ 0 := Units.ne_zero _
  have hu : dep u ≤ L 0 + 1 := depth_le (L := L) (u : StarV L)
  by_cases h0 : dep u = L 0 + 1
  · left
    rw [Fintype.sum_eq_single (⟨w, e₁⟩ : (Σ y : (starTree L).Dbl, u ⟶ y))] at hrel
    · have := Submodule.smul_mem _ (((starTree L).sgn k (u : StarV L) (w : StarV L) : kˣ) : k)⁻¹ hrel
      rwa [smul_smul, inv_mul_cancel₀ hsw, one_smul, ← bt, bt_eq e₁ e₂] at this
    · intro x hx
      exfalso
      apply hx
      apply out_eq
      show dep x.1 = dep w
      have hxb : dep x.1 ≤ L 0 + 1 := depth_le (L := L) (x.1 : StarV L)
      rcases out_cases u x with h | h <;> omega
  · right
    have hv : dep u + 1 ≤ L 0 + 1 := by omega
    set v : (starTree L).Dbl := (starTree L).toDbl (ofDep L (dep u + 1) hv)
    have hvd : dep v = dep u + 1 := starDepth_ofDep _ _
    have hadj : (starTree L).G.Adj (u : StarV L) (v : StarV L) :=
      (ReRoot.adj_one _ _).2 (Or.inl (show dep v = dep u + 1 from hvd))
    let d₁ : u ⟶ v := ⟨hadj⟩
    let d₂ : v ⟶ u := ⟨hadj.symm⟩
    refine ⟨v, d₁, d₂, -((((starTree L).sgn k (u : StarV L) (w : StarV L) : kˣ) : k)⁻¹ *
      (((starTree L).sgn k (u : StarV L) (v : StarV L) : kˣ) : k)), ?_, ?_, ?_⟩
    · unfold isR; exact hvd
    · unfold isR; omega
    · rw [Fintype.sum_eq_add (⟨w, e₁⟩ : (Σ y : (starTree L).Dbl, u ⟶ y)) ⟨v, d₁⟩
        (fun h ↦ by
          have := congrArg (fun x : (Σ y : (starTree L).Dbl, u ⟶ y) ↦ dep x.1) h
          change dep w = dep v at this
          omega)] at hrel
      · have := Submodule.smul_mem _ (((starTree L).sgn k (u : StarV L) (w : StarV L) : kˣ) : k)⁻¹
          hrel
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hsw, one_smul, ← bt, ← bt, bt_eq e₁ e₂,
          bt_eq d₁ d₂] at this
        rw [neg_smul, sub_neg_eq_add]
        exact this
      · intro x ⟨hx1, hx2⟩
        exfalso
        rcases out_cases u x with h | h
        · exact hx2 (out_eq _ _ (show dep x.1 = dep v by omega))
        · exact hx1 (out_eq _ _ (show dep x.1 = dep w by omega))

/-- **A path with more right steps than room lies in the ideal.** -/
theorem right_overflow : ∀ (n : ℕ) {a b : (starTree L).Dbl} (p : Quiver.Path a b), inv2 p = n →
    L 0 + 1 < dep a + rc p → LinearPaths.path (k := k) p ∈ ((starTree L).preproj k).ideal _ _ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b p hn hrc
  rcases Nat.eq_zero_or_pos (inv2 p) with h0 | hpos
  · exact absurd (sorted_rc p h0) (by omega)
  obtain ⟨u, w, q, e₁, e₂, r, hL, rfl⟩ := exists_dip p hpos
  have he₂ : isR e₂ := by
    rcases arrow_dep e₂ with h | h
    · exact h
    · have := arrow_dep e₁; unfold isR at hL; omega
  rw [show q.comp (e₁.toPath.comp (e₂.toPath.comp r)) = q.comp ((e₁.toPath.comp e₂.toPath).comp r)
      from congrArg q.comp (Quiver.Path.comp_assoc _ _ _).symm, ← LinearPaths.path_comp_path,
    ← LinearPaths.path_comp_path]
  rcases dip_rel k e₁ e₂ hL with hI | ⟨v, d₁, d₂, c, hd₁, hd₂, hmem⟩
  · exact ((starTree L).preproj k).comp_mem_ideal _ (((starTree L).preproj k).mem_ideal_comp hI _)
  · set p' := q.comp (d₁.toPath.comp (d₂.toPath.comp r))
    have hinv : inv2 p' + 1 = inv2 (q.comp (e₁.toPath.comp (e₂.toPath.comp r))) := by
      simp only [p', inv2_comp, rc_comp, lc_comp, inv2_toPath, rc_toPath, lc_toPath, if_neg hL,
        if_pos he₂, if_pos hd₁, if_neg hd₂]
      ring
    have hrc' : rc p' = rc (q.comp (e₁.toPath.comp (e₂.toPath.comp r))) := by
      simp only [p', rc_comp, rc_toPath, if_neg hL, if_pos he₂, if_pos hd₁, if_neg hd₂]
      omega
    have hp' := ih (inv2 p') (by omega) p' rfl (by rw [hrc']; exact hrc)
    have e : LinearPaths.path (k := k) q ≫ LinearPaths.path (e₁.toPath.comp e₂.toPath) ≫
        LinearPaths.path r = c • LinearPaths.path (k := k) p' +
          LinearPaths.path q ≫ (LinearPaths.path (e₁.toPath.comp e₂.toPath) -
            c • LinearPaths.path (d₁.toPath.comp d₂.toPath)) ≫ LinearPaths.path r := by
      simp only [p', Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
        Linear.comp_smul, ← LinearPaths.path_comp_path]
      simp only [Category.assoc]
      abel
    rw [e]
    exact add_mem (Submodule.smul_mem _ c hp')
      (((starTree L).preproj k).comp_mem_ideal _ (((starTree L).preproj k).mem_ideal_comp hmem _))

/-- **All paths of degree at least `N` vanish in `Π(A_N)`**, `N = L 0 + 2`. -/
theorem long_mem {a b : (starTree L).Dbl} (p : Quiver.Path a b) (hp : L 0 + 2 ≤ p.length) :
    LinearPaths.path (k := k) p ∈ ((starTree L).preproj k).ideal _ _ := by
  rw [length_eq] at hp
  by_cases h : dep a < lc p
  · exact left_overflow k _ p rfl h
  · exact right_overflow k _ p rfl (by omega)

end ASort

end MultiplicativeBasisDeformations
