module

public import MultiplicativeBasisDeformations.Foundations.PeriodicGauge

/-!
# The gauge on odd quotients of even `A` (Lemma A.1(2))

`lem:periodic-scalar-gauges` (2), `periodic-mesh-calculations.tex`:
"For the odd even-`A` quotient, first keep the scales of the arrows `ε_j` equal
to one and choose the root mesh scales to normalize the coefficients of
`ε_{j-2} ε_{j-1}`. The recurrence on each arm edge advances `j` by two. … Its
product equation determines the next vertex's mesh-scaling product, and the same
recursion finishes the normalization."

Vertices of `A_{2h}` are indexed by their depth `d ∈ [0, 2h)` from one end; the
middle edge is `{h - 1, h}`, and the deck generator is
`(d, s) ↦ (2h - 1 - d, s + c₀)` with `c₀` odd. The coefficients are recorded by
`C a b s` (the coefficient at `(a, s + 2)` of the arrow from `(b, s + 1)`). We
solve the equations on the half `d ≥ h` and fold the other half onto it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace OddGauge

variable {k : Type u} [Field k] (h : ℕ) (C : ℕ → ℕ → ℤ → kˣ) (c0 : ℕ)

/-- The products prescribed on the edge `{e, e + 1}` of the right half (`e ≥ h`),
given the parent's relation scales `Np`. -/
def lineS (e : ℕ) (Np : ℤ → kˣ) (s : ℤ) : kˣ :=
  if (s : ZMod 2) = ((e + 1 : ℕ) : ZMod 2) then (C (e + 1) e s)⁻¹
  else (Np (s + 2) * C e (e + 1) s)⁻¹

open Classical in
/-- One step down the right half. -/
def step (e : ℕ) (Np : ℤ → kˣ) : (ℤ → kˣ) × (ℤ → kˣ) :=
  if hP : 0 < 2 * c0 ∧ ∀ s, lineS C e Np (s + (2 * c0 : ℕ)) = lineS C e Np s then
    ((exists_periodic_line_vertex (2 * c0) hP.1 (even_two_mul c0) _ hP.2
        ((e + 1 : ℕ) : ZMod 2)).choose,
      (exists_periodic_line_vertex (2 * c0) hP.1 (even_two_mul c0) _ hP.2
        ((e + 1 : ℕ) : ZMod 2)).choose_spec.choose)
  else (fun _ ↦ 1, fun _ ↦ 1)

/-- The relation scales of the middle vertex `h`. -/
def Nmid (s : ℤ) : kˣ := (C h (h - 1) (s - 2))⁻¹

/-- The relation scales (`.1`, of the child `h + 1 + j`) and arrow scales (`.2`, of
the edge `{h + j, h + j + 1}`) on the right half. -/
def right : ℕ → (ℤ → kˣ) × (ℤ → kˣ)
  | 0 => step C c0 h (Nmid h C)
  | j + 1 => step C c0 (h + j + 1) (right j).1

/-- The parent relation scales of the edge `{h + j, h + j + 1}`. -/
def parN (j : ℕ) : ℤ → kˣ := if j = 0 then Nmid h C else (right h C c0 (j - 1)).1

theorem right_eq (j : ℕ) : right h C c0 j = step C c0 (h + j) (parN h C c0 j) := by
  rcases j with _ | j
  · rfl
  · simp [right, parN]; rfl

variable (hc0 : 0 < c0)
  (hper : ∀ a b s, C a b (s + (2 * c0 : ℕ)) = C a b s)

include hper in
theorem lineS_periodic (e : ℕ) (Np : ℤ → kˣ) (hNp : ∀ s, Np (s + (2 * c0 : ℕ)) = Np s) (s : ℤ) :
    lineS C e Np (s + (2 * c0 : ℕ)) = lineS C e Np s := by
  have hP2 : ((s + (2 * c0 : ℕ) : ℤ) : ZMod 2) = (s : ZMod 2) := by
    push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  unfold lineS
  rw [hP2, hper, hper, show s + (2 * c0 : ℕ) + 2 = (s + 2) + (2 * c0 : ℕ) by ring, hNp]

include hc0 hper in
theorem step_spec (e : ℕ) (Np : ℤ → kˣ) (hNp : ∀ s, Np (s + (2 * c0 : ℕ)) = Np s) :
    (∀ s, (step C c0 e Np).1 (s + (2 * c0 : ℕ)) = (step C c0 e Np).1 s) ∧
    (∀ s, (step C c0 e Np).2 (s + (2 * c0 : ℕ)) = (step C c0 e Np).2 s) ∧
    ∀ s, (step C c0 e Np).2 s * (step C c0 e Np).2 (s + 1) *
      (if (s : ZMod 2) = ((e + 1 : ℕ) : ZMod 2) then (step C c0 e Np).1 (s + 2) else 1) =
        lineS C e Np s := by
  have hP : 0 < 2 * c0 := by omega
  have hS := lineS_periodic C c0 hper e Np hNp
  unfold step
  rw [dif_pos ⟨hP, hS⟩]
  exact (exists_periodic_line_vertex (2 * c0) hP (even_two_mul c0) _ hS _).choose_spec.choose_spec

include hc0 hper in
theorem right_spec (j : ℕ) :
    (∀ s, (right h C c0 j).1 (s + (2 * c0 : ℕ)) = (right h C c0 j).1 s) ∧
    (∀ s, (right h C c0 j).2 (s + (2 * c0 : ℕ)) = (right h C c0 j).2 s) ∧
    ∀ s, (right h C c0 j).2 s * (right h C c0 j).2 (s + 1) *
      (if (s : ZMod 2) = ((h + j + 1 : ℕ) : ZMod 2) then (right h C c0 j).1 (s + 2) else 1) =
        lineS C (h + j) (parN h C c0 j) s := by
  have hpar : ∀ j, ∀ s, parN h C c0 j (s + (2 * c0 : ℕ)) = parN h C c0 j s := by
    intro j
    induction j with
    | zero =>
        intro s
        simp only [parN, if_true, Nmid]
        rw [show s + (2 * c0 : ℕ) - 2 = (s - 2) + (2 * c0 : ℕ) by ring, hper]
    | succ j ih =>
        intro s
        simp only [parN, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [right_eq]
        exact (step_spec C c0 hc0 hper _ _ ih).1 s
  rw [right_eq]
  exact step_spec C c0 hc0 hper _ _ (hpar j)

/-- The relation scales on the right half `d ≥ h`. -/
def NR (d : ℕ) (s : ℤ) : kˣ := if d = h then Nmid h C s else (right h C c0 (d - h - 1)).1 s

/-- The arrow scales on the edges `{e, e + 1}` with `e ≥ h - 1`. -/
def MR (e : ℕ) (s : ℤ) : kˣ := if e + 1 = h then 1 else (right h C c0 (e - h)).2 s

/-- **The relation scales**, folding the left half onto the right half. -/
def Nd (d : ℕ) (s : ℤ) : kˣ := if h ≤ d then NR h C c0 d s else NR h C c0 (2 * h - 1 - d) (s + c0)

/-- **The arrow scales** of the edges `{e, e + 1}`. -/
def Md (e : ℕ) (s : ℤ) : kˣ :=
  if h ≤ e + 1 then MR h C c0 e s else MR h C c0 (2 * h - 2 - e) (s + c0)

include hc0 hper in
theorem NR_periodic (d : ℕ) (s : ℤ) : NR h C c0 d (s + (2 * c0 : ℕ)) = NR h C c0 d s := by
  unfold NR
  split_ifs
  · simp only [Nmid]; rw [show s + (2 * c0 : ℕ) - 2 = (s - 2) + (2 * c0 : ℕ) by ring, hper]
  · exact (right_spec h C c0 hc0 hper _).1 s

include hc0 hper in
theorem MR_periodic (e : ℕ) (s : ℤ) : MR h C c0 e (s + (2 * c0 : ℕ)) = MR h C c0 e s := by
  unfold MR
  split_ifs
  · rfl
  · exact (right_spec h C c0 hc0 hper _).2.1 s

variable (hh : 1 ≤ h)

include hc0 hper in
/-- **The relation scales are invariant** under `(d, s) ↦ (2h - 1 - d, s + c₀)`. -/
theorem Nd_inv (d : ℕ) (hd : d < 2 * h) (s : ℤ) :
    Nd h C c0 (2 * h - 1 - d) (s + c0) = Nd h C c0 d s := by
  unfold Nd
  by_cases hdh : h ≤ d
  · rw [if_neg (by omega), if_pos hdh, show 2 * h - 1 - (2 * h - 1 - d) = d by omega,
      show s + c0 + c0 = s + (2 * c0 : ℕ) by push_cast; ring, NR_periodic h C c0 hc0 hper]
  · rw [if_pos (by omega), if_neg hdh]

include hc0 hper in
theorem Md_inv (e : ℕ) (he : e + 1 < 2 * h) (s : ℤ) :
    Md h C c0 (2 * h - 2 - e) (s + c0) = Md h C c0 e s := by
  unfold Md
  by_cases heh : h ≤ e + 1
  · by_cases hmid : e + 1 = h
    · -- the middle edge
      rw [if_pos (by omega), if_pos heh, show 2 * h - 2 - e = e by omega]
      simp [MR, hmid]
    · rw [if_neg (by omega), if_pos heh, show 2 * h - 2 - (2 * h - 2 - e) = e by omega,
        show s + c0 + c0 = s + (2 * c0 : ℕ) by push_cast; ring, MR_periodic h C c0 hc0 hper]
  · rw [if_pos (by omega), if_neg heh]

include hc0 hper in
/-- The equations on the right half. -/
theorem right_eqn (e : ℕ) (he : h ≤ e) (s : ℤ) :
    ((s : ZMod 2) = ((e + 1 : ℕ) : ZMod 2) →
      Nd h C c0 (e + 1) (s + 2) * C (e + 1) e s * Md h C c0 e s * Md h C c0 e (s + 1) = 1) ∧
    ((s : ZMod 2) = ((e : ℕ) : ZMod 2) →
      Nd h C c0 e (s + 2) * C e (e + 1) s * Md h C c0 e s * Md h C c0 e (s + 1) = 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, e = h + j := ⟨e - h, by omega⟩
  have hM : ∀ s, Md h C c0 (h + j) s = (right h C c0 j).2 s := by
    intro s; simp only [Md, MR, if_pos (show h ≤ h + j + 1 by omega),
      if_neg (show h + j + 1 ≠ h by omega), Nat.add_sub_cancel_left]
  have hNc : ∀ s, Nd h C c0 (h + j + 1) s = (right h C c0 j).1 s := by
    intro s; simp only [Nd, NR, if_pos (show h ≤ h + j + 1 by omega),
      if_neg (show h + j + 1 ≠ h by omega), show h + j + 1 - h - 1 = j by omega]
  have hNp : ∀ s, Nd h C c0 (h + j) s = parN h C c0 j s := by
    intro s
    simp only [Nd, NR, if_pos (show h ≤ h + j by omega), parN]
    rcases j with _ | j
    · simp
    · simp only [show h + (j + 1) ≠ h by omega, if_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
      rw [show h + (j + 1) - h - 1 = j by omega]
  obtain ⟨-, -, hspec⟩ := right_spec h C c0 hc0 hper j
  have hs := hspec s
  constructor
  · intro hpar
    rw [if_pos (by rw [hpar])] at hs
    rw [hM, hM, hNc]
    simp only [lineS, if_pos hpar] at hs
    rw [eq_inv_iff_mul_eq_one] at hs
    rw [← hs]; ac_rfl
  · intro hpar
    have hne : ¬ (s : ZMod 2) = ((h + j + 1 : ℕ) : ZMod 2) := by
      rw [hpar]; push_cast; intro h'
      exact absurd (add_left_cancel (h'.symm.trans (add_zero _).symm)) (by decide)
    rw [if_neg hne] at hs
    rw [hM, hM, hNp]
    simp only [lineS, if_neg hne, mul_one] at hs
    rw [eq_inv_iff_mul_eq_one] at hs
    rw [← hs]; ac_rfl

variable (hC : ∀ a b s, a < 2 * h → b < 2 * h → C (2 * h - 1 - a) (2 * h - 1 - b) (s + c0) = C a b s)

include hh hC in
/-- The equations on the middle edge (all arrow scales one). -/
theorem mid_eqn (s : ℤ) :
    ((s : ZMod 2) = ((h : ℕ) : ZMod 2) →
      Nd h C c0 h (s + 2) * C h (h - 1) s * Md h C c0 (h - 1) s * Md h C c0 (h - 1) (s + 1) = 1) ∧
    ((s : ZMod 2) = ((h - 1 : ℕ) : ZMod 2) →
      Nd h C c0 (h - 1) (s + 2) * C (h - 1) h s * Md h C c0 (h - 1) s *
        Md h C c0 (h - 1) (s + 1) = 1) := by
  have hM : ∀ s, Md h C c0 (h - 1) s = 1 := by
    intro s; simp [Md, MR, show h - 1 + 1 = h by omega]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rw [hM, hM]
    simp only [Nd, le_refl, if_true, NR, Nmid, show s + 2 - 2 = s by ring]
    simp
  · rw [hM, hM]
    simp only [Nd, show ¬ h ≤ h - 1 by omega, if_false, NR, show 2 * h - 1 - (h - 1) = h by omega,
      if_true, Nmid, show s + 2 + c0 - 2 = s + c0 by ring]
    have := hC (h - 1) h s (by omega) (by omega)
    rw [show 2 * h - 1 - (h - 1) = h by omega, show 2 * h - 1 - h = h - 1 by omega] at this
    rw [this]; simp

theorem par_fold (hodd : Odd c0) {a : ℕ} (ha : a < 2 * h) (s : ℤ)
    (hs : (s : ZMod 2) = ((a : ℕ) : ZMod 2)) :
    ((s + c0 : ℤ) : ZMod 2) = ((2 * h - 1 - a : ℕ) : ZMod 2) := by
  obtain ⟨r, hr⟩ := hodd
  have e1 : ((2 * h - 1 - a : ℕ) : ZMod 2) = ((a : ℕ) : ZMod 2) + 1 := by
    have h1 : (2 * h - 1 - a) + a + 1 = 2 * h := by omega
    have := congrArg (fun n : ℕ ↦ (n : ZMod 2)) h1
    push_cast at this
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul] at this
    have key : ∀ x y : ZMod 2, x + y + 1 = 0 → x = y + 1 := by decide
    exact key _ _ this
  push_cast; rw [hs, e1, hr]; push_cast
  rw [show (2 : ZMod 2) = 0 from rfl]; ring

include hc0 hper hh hC in
/-- **The gauge equations** on all edges. -/
theorem eqn (hodd : Odd c0) (a b : ℕ) (ha : a < 2 * h) (hb : b < 2 * h)
    (hab : b = a + 1 ∨ a = b + 1) (s : ℤ) (hs : (s : ZMod 2) = ((a : ℕ) : ZMod 2)) :
    Nd h C c0 a (s + 2) * C a b s * Md h C c0 (min a b) s * Md h C c0 (min a b) (s + 1) = 1 := by
  by_cases hmid : (a = h ∧ b = h - 1) ∨ (a = h - 1 ∧ b = h)
  · rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, min_eq_right (by omega)]; rw [h1] at hs; exact (mid_eqn h C c0 hh hC s).1 hs
    · rw [h1, h2, min_eq_left (by omega)]; rw [h1] at hs; exact (mid_eqn h C c0 hh hC s).2 hs
  by_cases hright : h ≤ min a b
  · rcases hab with h1 | h1
    · rw [h1, min_eq_left (by omega)]
      exact (right_eqn h C c0 hc0 hper a (by rw [h1] at hright; omega) s).2 hs
    · rw [h1, min_eq_right (by omega)]; rw [h1] at hs
      exact (right_eqn h C c0 hc0 hper b (by rw [h1] at hright; omega) s).1 hs
  -- fold the left half onto the right half
  have hs' := par_fold h c0 hodd ha s hs
  have hNinv := Nd_inv h C c0 hc0 hper a ha (s + 2)
  have hCinv := hC a b s ha hb
  rcases hab with h1 | h1
  · -- `a < b`: the folded vertex `2h - 1 - a` is the child of the edge `2h - 2 - a`
    subst h1
    rw [min_eq_left (by omega)] at hright ⊢
    have hMinv := Md_inv h C c0 hc0 hper a (by omega) s
    have hMinv' := Md_inv h C c0 hc0 hper a (by omega) (s + 1)
    have key := (right_eqn h C c0 hc0 hper (2 * h - 2 - a) (by omega) (s + c0)).1
      (by rw [show 2 * h - 2 - a + 1 = 2 * h - 1 - a by omega]; exact hs')
    rw [show 2 * h - 2 - a + 1 = 2 * h - 1 - a by omega, show s + c0 + 2 = s + 2 + c0 by ring,
      hNinv, show 2 * h - 2 - a = 2 * h - 1 - (a + 1) by omega, hCinv,
      show 2 * h - 1 - (a + 1) = 2 * h - 2 - a by omega, hMinv,
      show s + c0 + 1 = s + 1 + c0 by ring, hMinv'] at key
    exact key
  · -- `a > b`: the folded vertex `2h - 1 - a` is the parent of the edge `2h - 1 - a`
    subst h1
    rw [min_eq_right (by omega)] at hright ⊢
    have hMinv := Md_inv h C c0 hc0 hper b (by omega) s
    have hMinv' := Md_inv h C c0 hc0 hper b (by omega) (s + 1)
    have key := (right_eqn h C c0 hc0 hper (2 * h - 2 - b) (by omega) (s + c0)).2
      (by rw [show 2 * h - 2 - b = 2 * h - 1 - (b + 1) by omega]; exact hs')
    rw [show 2 * h - 2 - b + 1 = 2 * h - 1 - b by omega, show s + c0 + 2 = s + 2 + c0 by ring,
      show 2 * h - 2 - b = 2 * h - 1 - (b + 1) by omega, hNinv, hCinv,
      show 2 * h - 1 - (b + 1) = 2 * h - 2 - b by omega, hMinv,
      show s + c0 + 1 = s + 1 + c0 by ring, hMinv'] at key
    exact key

end OddGauge

end MultiplicativeBasisDeformations
