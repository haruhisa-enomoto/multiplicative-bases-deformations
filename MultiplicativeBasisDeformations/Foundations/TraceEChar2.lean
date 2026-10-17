import MultiplicativeBasisDeformations.Foundations.TraceE78Char2

/-!
# Exceptional twisted traces in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex:278–330`. For a star of type `E` with short
arm `a` (`L a = 0`), medium arm `b` (`L b = 1`) and long arm `c`, write `x, y` for the
closed paths along `c, b`; then `x^m = y³ = (x + y)² = 0` with `m = L c + 2`.

* Ordinary traces (`trace_E_c2`): in word degree `n`, every trace is a multiple of the
  candidate `yx, yx³, (yx³)², (yx³)(yx⁴)²` for `n = 2, 4, 8, 14`, and zero otherwise.
* The reflection of `E₆` (`L b = L c = 1`, twist exchanging `b, c`):
  "Twisted cuts are `xw = wy` and `yw = wx`. … In degree three, use `xw = wy` with
  `w = x², xy` to obtain `[ξ₁] = [ξ₂] = 0`, and use `yw = wx` with `w = x²` to obtain
  `[ξ₃] = 0`. In degree four, the first relation with `w = ξ₁` gives `[ξ₄] = 0`, and the
  second with `w = ξ₃` gives `[ξ₅] = 0`. Degree five is already spanned by `ξ₆`."
  (`trace_E6_twist_c2`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

open TraceData

variable {M : Type*} [AddCommGroup M] {L : Fin 3 → ℕ} (D : TraceData L M)
  (h2 : ∀ m : M, m + m = 0) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hLa : L a = 0) (hLb : L b = 1)

theorem neg_c (r : Rc L) : -r = r := by
  refine neg_eq_of_add_eq_zero_left ?_
  rw [← two_mul, two_eq_zero, zero_mul]

include hab hac hbc in
theorem z_a_eq : z L a = z L c + z L b := by
  have hs := sum_z L
  rw [sum_fin_three _ hab hac hbc] at hs
  have e : z L a = -(z L c + z L b) := by rw [eq_neg_iff_add_eq_zero, ← hs]; abel
  rw [e, neg_c]

include hab hac hbc hLa hLb in
/-- The relations of the centre corner in `Rc`. -/
theorem r5hyp (hLc : L c = 1 ∨ L c = 2 ∨ L c = 3) : R5.Hyp (z L c) (z L b) where
  x5 := by
    have := z_pow L c
    rcases hLc with h | h | h <;> rw [h] at this
    · rw [show 5 = 3 + 2 from rfl, pow_add, this, zero_mul]
    · rw [show 5 = 4 + 1 from rfl, pow_add, this, zero_mul]
    · exact this
  y3 := by have := z_pow L b; rwa [hLb] at this
  d1 := by
    have := z_pow L a
    rw [hLa, zero_add, z_a_eq hab hac hbc, sq] at this
    rw [← this]; noncomm_ring
  two := two_eq_zero L

include hab hac hbc in
theorem word_mem_span (w : List (Fin 3)) :
    (w.map (z L)).prod ∈ E78.span (z L c) (z L b) w.length := by
  induction w with
  | nil => exact AddSubgroup.subset_closure ⟨0, [], rfl, by simp [E78.blk]⟩
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons]
      rcases fin_three_cases hab hac hbc i with rfl | rfl | rfl
      · rw [z_a_eq hab hac hbc, add_mul]
        exact add_mem (E78.x_mul_mem _ ih) (E78.y_mul_mem _ ih)
      · exact E78.y_mul_mem _ ih
      · exact E78.x_mul_mem _ ih

/-! ### Ordinary traces -/

/-- The candidate words of degrees `2, 4, 8, 14`. -/
def candE (b c : Fin 3) : ℕ → List (Fin 3)
  | 2 => [b, c]
  | 4 => [b, c, c, c]
  | 8 => [b, c, c, c, b, c, c, c]
  | 14 => [b, c, c, c, b, c, c, c, c, b, c, c, c, c]
  | _ => []

theorem length_candE_2 : (candE b c 2).length = 2 := rfl
theorem length_candE_4 : (candE b c 4).length = 4 := rfl
theorem length_candE_8 : (candE b c 8).length = 8 := rfl
theorem length_candE_14 : (candE b c 14).length = 14 := rfl

include h2 hab hac hbc hLa hLb in
/-- **Ordinary traces of the types `E` in characteristic two.** -/
theorem trace_E_c2 (hLc : L c = 1 ∨ L c = 2 ∨ L c = 3) (hθ : ∀ i, D.θ i = i)
    (w : List (Fin 3)) (hw : 1 ≤ w.length) :
    ∃ z : ℤ, D.tr w = z • (if w.length = 2 ∨ w.length = 4 ∨ w.length = 8 ∨ w.length = 14 then
      D.tr (candE b c w.length) else 0) := by
  set X := z L c
  set Y := z L b
  have R := r5hyp hab hac hbc hLa hLb hLc
  have H : E78c.Hyp X Y (D.trc h2) :=
    { x5 := R.x5, y3 := R.y3, d1 := R.d1, two := R.two
      rot := fun p q ↦ by rw [D.trc_rotate h2, D.twc_id hθ]
      xp := fun q hq ↦ D.trc_fixed h2 c (hθ c) q hq
      ty := by have := D.trc_fixed h2 b (hθ b) 1 le_rfl; rwa [pow_one] at this
      ty2 := by have := D.trc_fixed h2 b (hθ b) 2 (by norm_num); rwa [sq] at this }
  have hc2 : D.trc h2 (E78.blk X Y [1]) = D.tr (candE b c 2) := by
    rw [← D.trc_word h2]; simp [candE, E78.blk, X, Y]
  have hc4 : D.trc h2 (E78.blk X Y [3]) = D.tr (candE b c 4) := by
    rw [← D.trc_word h2]; simp [candE, E78.blk, X, Y, pow_succ, mul_assoc]
  have hc8 : D.trc h2 (E78.blk X Y [3, 3]) = D.tr (candE b c 8) := by
    rw [← D.trc_word h2]; simp [candE, E78.blk, X, Y, pow_succ, mul_assoc]
  have hc14 : D.trc h2 (E78.blk X Y [3, 4, 4]) = D.tr (candE b c 14) := by
    rw [← D.trc_word h2]; simp [candE, E78.blk, X, Y, pow_succ, mul_assoc]
  set A : AddSubgroup M := if w.length = 2 ∨ w.length = 4 ∨ w.length = 8 ∨ w.length = 14 then
    AddSubgroup.zmultiples (D.tr (candE b c w.length)) else ⊥ with hA
  have hmem : D.tr w ∈ A := by
    rw [← D.trc_word h2]
    refine E78c.span_mem H w.length hw (fun h ↦ ?_) (fun h ↦ ?_) (fun h ↦ ?_) (fun h ↦ ?_)
      (word_mem_span hab hac hbc w)
    all_goals
      rw [hA, if_pos (by omega), h]
      first
      | rw [hc2]; exact AddSubgroup.mem_zmultiples _
      | rw [hc4]; exact AddSubgroup.mem_zmultiples _
      | rw [hc8]; exact AddSubgroup.mem_zmultiples _
      | rw [hc14]; exact AddSubgroup.mem_zmultiples _
  by_cases hn : w.length = 2 ∨ w.length = 4 ∨ w.length = 8 ∨ w.length = 14
  · rw [hA, if_pos hn] at hmem
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
    exact ⟨z, by rw [if_pos hn, ← hz]⟩
  · rw [hA, if_neg hn, AddSubgroup.mem_bot] at hmem
    exact ⟨0, by rw [hmem, zero_smul]⟩

/-! ### The reflection of `E₆` -/

include h2 hab hac hbc hLa hLb in
/-- **Reflection-twisted traces of `E₆` in characteristic two**: they vanish in word
degrees three, four and at least six, and are multiples of `[x²yx²]` in degree five. -/
theorem trace_E6_twist_c2 (hLc : L c = 1) (hθb : D.θ b = c) (hθc : D.θ c = b)
    (w : List (Fin 3)) :
    (w.length = 3 ∨ w.length = 4 ∨ 6 ≤ w.length → D.tr w = 0) ∧
      (w.length = 5 → ∃ z : ℤ, D.tr w = z • D.tr [c, c, b, c, c]) := by
  set X := z L c
  set Y := z L b
  have R := r5hyp hab hac hbc hLa hLb (Or.inl hLc)
  have hX3 : X ^ 3 = 0 := by have := z_pow L c; rwa [hLc] at this
  have hXk : ∀ k, 3 ≤ k → X ^ k = 0 := fun k hk ↦ by
    rw [show k = 3 + (k - 3) by omega, pow_add, hX3, zero_mul]
  set T := D.trc h2
  have tX : D.twc X = Y := by rw [D.twc_z, hθc]
  have tY : D.twc Y = X := by rw [D.twc_z, hθb]
  have rot := D.trc_rotate h2
  have tself : ∀ r, T r + T r = 0 := fun r ↦ h2 _
  -- the twisted cuts
  have T1 : T (X ^ 2 * Y) = 0 := by
    have := rot X (X ^ 2); rw [tX, ← pow_succ', hX3, map_zero] at this; exact this.symm
  have T2 : T (X * Y * X) = 0 := by
    have h := rot X (X * Y)
    rw [tX, ← mul_assoc, ← sq, T1, mul_assoc, R5.Ry0 R, mul_add, mul_add, map_add, map_add,
      ← mul_assoc, ← mul_assoc, ← sq, T1, ← pow_succ', hX3, map_zero, add_zero, add_zero] at h
    exact h.symm
  have T3 : T (Y * X ^ 2) = 0 := by
    have := rot Y (X ^ 2); rw [tY, ← pow_succ, hX3, map_zero] at this; exact this
  have T4 : T (X ^ 2 * Y * X) = 0 := by
    have h := rot X (X ^ 2 * Y)
    rw [tX, ← mul_assoc, ← pow_succ', hX3, zero_mul, map_zero, mul_assoc, R5.Ry0 R, mul_add,
      mul_add, map_add, map_add, ← mul_assoc, ← mul_assoc, ← pow_succ, hX3, zero_mul, map_zero,
      add_zero, ← pow_add, hXk 4 (by norm_num), map_zero, add_zero] at h
    exact h.symm
  have T5 : T (X * Y * X ^ 2) = 0 := by
    have h := rot Y (Y * X ^ 2)
    rw [tY, mul_assoc, ← pow_succ, hX3, mul_zero, map_zero, ← mul_assoc, R5.Ry0 R, add_mul,
      add_mul, map_add, map_add, mul_assoc, ← pow_succ', hX3, mul_zero, map_zero, zero_add,
      ← pow_add, hXk 4 (by norm_num), map_zero, add_zero] at h
    exact h
  have hcand : T (X ^ 2 * Y * X ^ 2) = D.tr [c, c, b, c, c] := by
    rw [← D.trc_word h2]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, sq, mul_assoc,
      X, Y]
    rfl
  -- the generators
  have gen : ∀ n (r : Rc L), r ∈ R5.Gen X Y n →
      (n = 3 ∨ n = 4 ∨ 6 ≤ n → T r = 0) ∧ (n = 5 → r = 0 ∨ r = X ^ 2 * Y * X ^ 2) := by
    intro n r hr
    have ω3z : R5.ω3 X Y = 0 := by simp [R5.ω3, hX3]
    have ω4z : R5.ω4 X Y = 0 := by simp [R5.ω4, hXk 4 (by norm_num)]
    have ω5z : R5.ω5 X Y = 0 := by simp [R5.ω5, hXk 4 (by norm_num)]
    rcases hr with rfl | ⟨i, j, hj, hn, rfl⟩ | ⟨i, hn, rfl⟩ | ⟨i, j, hj, hn, rfl⟩ | ⟨i, hn, rfl⟩
    · refine ⟨fun h ↦ by rw [hXk n (by omega), map_zero], fun h ↦ Or.inl (hXk n (by omega))⟩
    · by_cases hij : 3 ≤ i ∨ 3 ≤ j
      · have : X ^ i * Y * X ^ j = 0 := by
          rcases hij with h | h
          · rw [hXk i h, zero_mul, zero_mul]
          · rw [hXk j h, mul_zero]
        rw [this, map_zero]; exact ⟨fun _ ↦ rfl, fun _ ↦ Or.inl rfl⟩
      · push Not at hij
        obtain ⟨hi, hj'⟩ := hij
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · interval_cases i <;> interval_cases j <;> simp_all [sq] <;> omega
        · interval_cases i <;> interval_cases j <;> first | omega | exact Or.inr rfl
    · rw [ω3z, mul_zero, map_zero]; exact ⟨fun _ ↦ rfl, fun _ ↦ Or.inl rfl⟩
    · rw [ω4z, mul_zero, zero_mul, map_zero]; exact ⟨fun _ ↦ rfl, fun _ ↦ Or.inl rfl⟩
    · rw [ω5z, mul_zero, map_zero]; exact ⟨fun _ ↦ rfl, fun _ ↦ Or.inl rfl⟩
  -- the word lies in the span of its degree
  have hw : (w.map (z L)).prod ∈ R5.spn X Y w.length := by
    have := R5.prod_mem R (w.map (z L)) (fun u hu ↦ by
      simp only [List.mem_map] at hu
      obtain ⟨i, -, rfl⟩ := hu
      rcases fin_three_cases hab hac hbc i with rfl | rfl | rfl
      · exact Or.inr (Or.inr (z_a_eq hab hac hbc))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl)
    rwa [List.length_map] at this
  rw [← D.trc_word h2]
  constructor
  · intro hn
    refine AddSubgroup.closure_induction (p := fun r _ ↦ T r = 0) (fun r hr ↦ (gen _ r hr).1 hn)
      (map_zero _) (fun a b _ _ ha hb ↦ by rw [map_add, ha, hb, add_zero])
      (fun a _ ha ↦ by rw [map_neg, ha, neg_zero]) hw
  · intro hn
    rw [← hcand]
    have : T (w.map (z L)).prod ∈ AddSubgroup.zmultiples (T (X ^ 2 * Y * X ^ 2)) := by
      refine AddSubgroup.closure_induction
        (p := fun r _ ↦ T r ∈ AddSubgroup.zmultiples (T (X ^ 2 * Y * X ^ 2)))
        (fun r hr ↦ ?_) (by rw [map_zero]; exact zero_mem _)
        (fun a b _ _ ha hb ↦ by rw [map_add]; exact add_mem ha hb)
        (fun a _ ha ↦ by rw [map_neg]; exact neg_mem ha) hw
      rcases (gen _ r hr).2 hn with rfl | rfl
      · rw [map_zero]; exact zero_mem _
      · exact AddSubgroup.mem_zmultiples _
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 this
    exact ⟨z, hz.symm⟩

end TraceAlg

end MultiplicativeBasisDeformations
