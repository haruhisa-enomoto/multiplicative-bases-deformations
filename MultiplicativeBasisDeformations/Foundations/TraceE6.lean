module

public import MultiplicativeBasisDeformations.Foundations.TraceAlgebraTwo
public import MultiplicativeBasisDeformations.Foundations.TraceTypesAD

/-!
# Twisted traces of type `E_6`

Appendix A, "Type `E_6` and the small-period exclusion"
(`periodic-mesh-calculations.tex`). The arms have one, two and two
vertices; `x` is the closed path along the short arm and `p, q` the others, so
`x + p + q = 0` and `x² = p³ = q³ = 0`. With `v = p - q = x + 2p`, "adding and
subtracting the cubic relations gives `x² = 0`, `v³ = -xvx`,
`v²x + vxv + xv² = 0`", and the words `x, v; xv, vx, v²; xvx, xv², vxv;
xvxv, vxv²; xvxv²` span the positive part, with all words of degree six zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

section Relations

variable {S : Type*} [Ring S] (x v : S) (hx : x * x = 0) (hv3 : v ^ 3 = -(x * v * x))
  (hrel : v ^ 2 * x + v * x * v + x * v ^ 2 = 0)

include hx hrel in
theorem e6_xv2x : x * v ^ 2 * x = -(x * v * x * v) := by
  have := congrArg (x * ·) hrel
  simp only [mul_add, mul_zero] at this
  have e : x * (x * v ^ 2) = 0 := by rw [← mul_assoc, hx, zero_mul]
  rw [e, add_zero] at this
  rw [eq_neg_iff_add_eq_zero, ← this]; noncomm_ring

include hx hrel in
theorem e6_vxvx : v * x * v * x = x * v * x * v := by
  have := congrArg (· * x) hrel
  simp only [add_mul, zero_mul] at this
  have e : v ^ 2 * x * x = 0 := by rw [mul_assoc, hx, mul_zero]
  rw [e, zero_add, e6_xv2x x v hx hrel] at this
  rw [← sub_eq_zero, ← this]; noncomm_ring

include hx hv3 in
theorem e6_xv3 : x * v ^ 3 = 0 := by
  rw [hv3, mul_neg, ← mul_assoc, ← mul_assoc, hx, zero_mul, zero_mul, neg_zero]

include hx hv3 in
theorem e6_v3x : v ^ 3 * x = 0 := by
  rw [hv3, neg_mul, mul_assoc, hx, mul_zero, neg_zero]

/-- The spanning words of the corner, by word degree. -/
def e6Table : ℕ → Set S
  | 0 => {1}
  | 1 => {x, v}
  | 2 => {x * v, v * x, v ^ 2}
  | 3 => {x * v * x, x * v ^ 2, v * x * v}
  | 4 => {x * v * x * v, v * x * v ^ 2}
  | 5 => {x * v * x * v ^ 2}
  | _ + 6 => ∅

/-- Their additive span. -/
abbrev e6Span (n : ℕ) : AddSubgroup S := AddSubgroup.closure (e6Table x v n)

include hx hv3 hrel in
/-- **Closure under right multiplication** (`periodic-mesh-calculations.tex`). -/
theorem e6_closed (n : ℕ) (w : S) (hw : w ∈ e6Table x v n) :
    w * x ∈ e6Span x v (n + 1) ∧ w * v ∈ e6Span x v (n + 1) := by
  have mem : ∀ {m : ℕ} {u : S}, u ∈ e6Table x v m → u ∈ e6Span x v m :=
    fun h ↦ AddSubgroup.subset_closure h
  have xv2x := e6_xv2x x v hx hrel
  have vxvx := e6_vxvx x v hx hrel
  have xv3 := e6_xv3 x v hx hv3
  have v3x := e6_v3x x v hx hv3
  match n, hw with
  | 0, hw =>
      obtain rfl : w = 1 := hw
      exact ⟨mem (by simp [e6Table]), mem (by simp [e6Table])⟩
  | 1, hw =>
      rcases hw with rfl | rfl
      · exact ⟨by rw [hx]; exact zero_mem _, mem (by simp [e6Table])⟩
      · exact ⟨mem (by simp [e6Table]), mem (by simp [e6Table, sq])⟩
  | 2, hw =>
      rcases hw with rfl | rfl | rfl
      · exact ⟨mem (by simp [e6Table]), mem (by simp [e6Table, sq, mul_assoc])⟩
      · exact ⟨by rw [mul_assoc, hx, mul_zero]; exact zero_mem _, mem (by simp [e6Table])⟩
      · refine ⟨?_, ?_⟩
        · have : v ^ 2 * x = -(v * x * v) + -(x * v ^ 2) := by
            rw [← sub_eq_zero, ← hrel]; noncomm_ring
          rw [this]
          exact add_mem (neg_mem (mem (by simp [e6Table]))) (neg_mem (mem (by simp [e6Table])))
        · rw [← pow_succ, hv3]; exact neg_mem (mem (by simp [e6Table]))
  | 3, hw =>
      rcases hw with rfl | rfl | rfl
      · refine ⟨by rw [mul_assoc, hx, mul_zero]; exact zero_mem _, mem (by simp [e6Table])⟩
      · refine ⟨by rw [xv2x]; exact neg_mem (mem (by simp [e6Table])), ?_⟩
        rw [mul_assoc, ← pow_succ, xv3]; exact zero_mem _
      · refine ⟨by rw [vxvx]; exact mem (by simp [e6Table]), ?_⟩
        rw [show v * x * v * v = v * x * v ^ 2 by noncomm_ring]; exact mem (by simp [e6Table])
  | 4, hw =>
      rcases hw with rfl | rfl
      · refine ⟨?_, ?_⟩
        · rw [show x * v * x * v * x = x * (v * x * v * x) by noncomm_ring, vxvx,
            show x * (x * v * x * v) = (x * x) * v * x * v by noncomm_ring, hx]
          simp
        · rw [show x * v * x * v * v = x * v * x * v ^ 2 by noncomm_ring]; exact mem (by simp [e6Table])
      · refine ⟨?_, ?_⟩
        · rw [show v * x * v ^ 2 * x = v * (x * v ^ 2 * x) by noncomm_ring, xv2x,
            show v * -(x * v * x * v) = -((v * x * v * x) * v) by noncomm_ring, vxvx,
            show x * v * x * v * v = x * v * x * v ^ 2 by noncomm_ring]
          exact neg_mem (mem (by simp [e6Table]))
        · rw [show v * x * v ^ 2 * v = v * (x * v ^ 3) by noncomm_ring, xv3, mul_zero]
          exact zero_mem _
  | 5, hw =>
      obtain rfl : w = x * v * x * v ^ 2 := hw
      refine ⟨?_, ?_⟩
      · have : v ^ 2 * x = -(v * x * v) + -(x * v ^ 2) := by
          rw [← sub_eq_zero, ← hrel]; noncomm_ring
        rw [show x * v * x * v ^ 2 * x = x * v * x * (v ^ 2 * x) by noncomm_ring, this]
        rw [show x * v * x * (-(v * x * v) + -(x * v ^ 2)) =
          -(x * (v * x * v * x) * v) - x * v * (x * x) * v ^ 2 by noncomm_ring, hx, vxvx,
          show x * (x * v * x * v) * v = (x * x) * v * x * v * v by noncomm_ring, hx]
        simp
      · rw [show x * v * x * v ^ 2 * v = x * v * (x * v ^ 3) by noncomm_ring, xv3, mul_zero]
        exact zero_mem _
  | n + 6, hw => exact absurd hw (by simp [e6Table])

include hx hv3 hrel in
theorem e6Span_mul (n : ℕ) {w : S} (hw : w ∈ e6Span x v n) :
    w * x ∈ e6Span x v (n + 1) ∧ w * v ∈ e6Span x v (n + 1) := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw => exact e6_closed x v hx hv3 hrel n w hw
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul, add_mul]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  | neg a _ ha => rw [neg_mul, neg_mul]; exact ⟨neg_mem ha.1, neg_mem ha.2⟩

include hx hv3 hrel in
/-- Right multiplication by an element of degree one. -/
theorem e6Span_mul_one (n : ℕ) {w u : S} (hw : w ∈ e6Span x v n) (hu : u ∈ e6Span x v 1) :
    w * u ∈ e6Span x v (n + 1) := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
      rcases hu with h | h
      · rw [h]; exact (e6Span_mul x v hx hv3 hrel n hw).1
      · rw [Set.mem_singleton_iff.1 h]; exact (e6Span_mul x v hx hv3 hrel n hw).2
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

include hx hv3 hrel in
/-- **Products of `n` elements of degree one lie in the span of degree `n`.** -/
theorem e6_prod_mem (l : List S) (hl : ∀ u ∈ l, u ∈ e6Span x v 1) :
    l.reverse.prod ∈ e6Span x v l.length := by
  induction l with
  | nil => exact AddSubgroup.subset_closure (by simp [e6Table])
  | cons u l ih =>
      rw [List.reverse_cons, List.prod_append, List.prod_singleton, List.length_cons]
      exact e6Span_mul_one x v hx hv3 hrel _ (ih fun u hu ↦ hl u (List.mem_cons_of_mem _ hu))
        (hl u List.mem_cons_self)

include hx hrel in
theorem e6_psi4'x : v * x * v ^ 2 * x = -(x * v * x * v ^ 2) := by
  rw [show v * x * v ^ 2 * x = v * (x * v ^ 2 * x) by noncomm_ring, e6_xv2x x v hx hrel,
    show v * -(x * v * x * v) = -((v * x * v * x) * v) by noncomm_ring, e6_vxvx x v hx hrel]
  noncomm_ring

/-- **Adding and subtracting the cubic relations** (`periodic-mesh-calculations.tex`). -/
theorem e6_derive (p q : S) (hp : p ^ 3 = 0) (hq : q ^ 3 = 0) (hs : x + p + q = 0)
    (c2 : ∀ r : S, 2 * r = 0 → r = 0) (hx' : x * x = 0) :
    (p - q) ^ 3 = -(x * (p - q) * x) ∧
      (p - q) ^ 2 * x + (p - q) * x * (p - q) + x * (p - q) ^ 2 = 0 := by
  have hq' : q = -x - p := by rw [← sub_eq_zero, ← hs]; abel
  have h1 : (p - q - x) ^ 3 = 0 := by
    rw [show p - q - x = 2 * p by rw [hq']; noncomm_ring, (Commute.ofNat_left 2 p).mul_pow, hp,
      mul_zero]
  have h3 : (p - q + x) ^ 3 = 0 := by
    rw [show p - q + x = -(2 * q) by rw [hq']; noncomm_ring, neg_pow,
      (Commute.ofNat_left 2 q).mul_pow, hq, mul_zero, mul_zero]
  constructor
  · apply eq_neg_of_add_eq_zero_left
    apply c2
    have e : 2 * ((p - q) ^ 3 + x * (p - q) * x) = (p - q + x) ^ 3 + (p - q - x) ^ 3 -
        2 * ((p - q) * (x * x) + (x * x) * (p - q)) := by noncomm_ring
    rw [e, h1, h3, hx']; simp
  · apply c2
    have e : 2 * ((p - q) ^ 2 * x + (p - q) * x * (p - q) + x * (p - q) ^ 2) =
        (p - q + x) ^ 3 - (p - q - x) ^ 3 - 2 * ((x * x) * x) := by noncomm_ring
    rw [e, h1, h3, hx']; simp

end Relations

theorem pow_mul_prod_map {S α : Type*} [Ring S] (t : S) (ht : ∀ r, Commute t r) (l : List α)
    (f : α → S) : t ^ l.length * (l.map f).prod = (l.map (fun i ↦ t * f i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, List.length_cons, ← ih,
        pow_succ', mul_assoc, ← mul_assoc (t ^ l.length), ((ht (f i)).pow_left l.length).eq,
        mul_assoc, mul_assoc]

section E6

variable {M : Type*} [AddCommGroup M] {L : Fin 3 → ℕ} (D : TraceData L M)
  (h2 : ∀ m : M, m + m = 0 → m = 0) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hLa : L a = 0) (hLb : L b = 1) (hLc : L c = 1)

/-- The corner element `v = p - q`. -/
abbrev vE6 (b c : Fin 3) : R2 L := y L b - y L c

include hab hac hbc in
theorem e6_sum : y L a + y L b + y L c = 0 := by
  have := sum_y L
  rwa [sum_fin_three _ hab hac hbc] at this

include hLa in
theorem e6_hx : y L a * y L a = 0 := by
  have := y_pow L a; rwa [hLa, zero_add, sq] at this

include hab hac hbc hLa hLb hLc in
/-- **The corner relations** `v³ = -xvx` and `v²x + vxv + xv² = 0`. -/
theorem e6_rels : vE6 (L := L) b c ^ 3 = -(y L a * vE6 b c * y L a) ∧
    vE6 (L := L) b c ^ 2 * y L a + vE6 b c * y L a * vE6 b c + y L a * vE6 b c ^ 2 = 0 := by
  have hp3 : y L b ^ 3 = 0 := by have := y_pow L b; rwa [hLb] at this
  have hq3 : y L c ^ 3 = 0 := by have := y_pow L c; rwa [hLc] at this
  exact e6_derive (y L a) (y L b) (y L c) hp3 hq3 (e6_sum hab hac hbc)
    (fun r hr ↦ cancel_two L hr) (e6_hx hLa)

include hab hac hbc in
theorem e6_two_mem (hLa : L a = 0) (hLb : L b = 1) (hLc : L c = 1) (i : Fin 3) :
    2 * y L i ∈ e6Span (y L a) (vE6 (L := L) b c) 1 := by
  have hs := e6_sum (L := L) hab hac hbc
  have mx : y L a ∈ e6Span (y L a) (vE6 (L := L) b c) 1 :=
    AddSubgroup.subset_closure (by simp [e6Table])
  have mv : vE6 (L := L) b c ∈ e6Span (y L a) (vE6 (L := L) b c) 1 :=
    AddSubgroup.subset_closure (by simp [e6Table])
  rcases fin_three_cases hab hac hbc i with h | h | h <;> rw [h]
  · rw [two_mul]; exact add_mem mx mx
  · rw [show 2 * y L b = vE6 b c - y L a by
      simp only [vE6]; rw [← sub_eq_zero, ← hs]; noncomm_ring]
    exact sub_mem mv mx
  · rw [show 2 * y L c = -(vE6 b c + y L a) by
      simp only [vE6]; rw [← sub_eq_zero, ← hs]; noncomm_ring]
    exact neg_mem (add_mem mv mx)

include hab hac hbc hLa hLb hLc in
/-- `2^n` times a word of length `n` lies in the span of degree `n`. -/
theorem e6_word_mem (w : List (Fin 3)) :
    (2 : R2 L) ^ w.length * (w.map (y L)).prod ∈ e6Span (y L a) (vE6 (L := L) b c) w.length := by
  have hx := e6_hx (L := L) hLa
  obtain ⟨hv3, hrel⟩ := e6_rels (L := L) hab hac hbc hLa hLb hLc
  rw [pow_mul_prod_map 2 (fun r ↦ Commute.ofNat_left 2 r) w (y L)]
  have := e6_prod_mem (y L a) (vE6 (L := L) b c) hx hv3 hrel
    (w.map (fun i ↦ 2 * y L i)).reverse (fun u hu ↦ by
      rw [List.mem_reverse, List.mem_map] at hu
      obtain ⟨i, -, rfl⟩ := hu
      exact e6_two_mem hab hac hbc hLa hLb hLc i)
  rwa [List.reverse_reverse, List.length_reverse, List.length_map] at this

include h2 in
theorem tr2_self (r : R2 L) : D.tr2 h2 r = D.tr2 h2 (D.tw2 r) := by
  have := D.tr2_rotate h2 r 1
  rwa [mul_one, one_mul] at this

include h2 in
theorem tr2_nsmul_two_pow (n : ℕ) (r : R2 L) :
    D.tr2 h2 ((2 : R2 L) ^ n * r) = (2 ^ n : ℕ) • D.tr2 h2 r := by
  rw [← map_nsmul, nsmul_eq_mul]; push_cast; rfl

include h2 in
theorem cancel_two_pow (n : ℕ) {m : M} (hm : (2 ^ n : ℕ) • m = 0) : m = 0 := by
  induction n generalizing m with
  | zero => simpa using hm
  | succ n ih =>
      apply h2
      apply ih
      rw [← two_nsmul, ← mul_nsmul, ← pow_succ']
      exact hm

include h2 hab hac hbc hLa hLb hLc in
/-- Traces of words are determined by traces on the spanning set. -/
theorem e6_tr_of_span (P : M → Prop) (hsmul : ∀ (n : ℕ) (m : M), P ((2 ^ n : ℕ) • m) → P m)
    (w : List (Fin 3)) (hspan : ∀ r ∈ e6Span (y L a) (vE6 (L := L) b c) w.length, P (D.tr2 h2 r)) :
    P (D.tr w) := by
  apply hsmul w.length
  rw [← D.tr2_word h2, ← tr2_nsmul_two_pow D h2]
  exact hspan _ (e6_word_mem hab hac hbc hLa hLb hLc w)

include h2 in
theorem tr2_zero_of_tw_neg {r : R2 L} (hr : D.tw2 r = -r) : D.tr2 h2 r = 0 := by
  have e := tr2_self D h2 r
  rw [hr, map_neg] at e
  apply h2
  nth_rewrite 1 [e]
  exact neg_add_cancel _

include h2 in
theorem tr2_zero_of_eq_neg {r : R2 L} (e : D.tr2 h2 r = -D.tr2 h2 r) : D.tr2 h2 r = 0 := by
  apply h2
  nth_rewrite 1 [e]
  exact neg_add_cancel _

include h2 in
theorem tr2_span_zero {X V : R2 L} (n : ℕ)
    (hgen : ∀ w ∈ e6Table X V n, D.tr2 h2 w = 0) {r : R2 L} (hr : r ∈ e6Span X V n) :
    D.tr2 h2 r = 0 := by
  induction hr using AddSubgroup.closure_induction with
  | mem w hw => exact hgen w hw
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | neg a _ ha => rw [map_neg, ha, neg_zero]

include h2 hab hac hbc hLa hLb hLc in
/-- **The reflection-twisted traces of `E_6` vanish** (`periodic-mesh-calculations.tex`). -/
theorem trace_E6_swap (hθa : D.θ a = a) (hθb : D.θ b = c) (hθc : D.θ c = b)
    (w : List (Fin 3)) (hw : 1 ≤ w.length) : D.tr w = 0 := by
  have hx := e6_hx (L := L) hLa
  obtain ⟨hv3, hrel⟩ := e6_rels (L := L) hab hac hbc hLa hLb hLc
  set X := y L a
  set V := vE6 (L := L) b c
  have tX : D.tw2 X = X := by rw [D.tw2_y, hθa]
  have tV : D.tw2 V = -V := by
    simp only [V, vE6, map_sub, D.tw2_y, hθb, hθc]; abel
  have rot : ∀ p q : R2 L, D.tr2 h2 (p * q) = D.tr2 h2 (q * D.tw2 p) := D.tr2_rotate h2
  have hgen : ∀ n, 1 ≤ n → ∀ u ∈ e6Table X V n, D.tr2 h2 u = 0 := by
    intro n hn u hu
    match n, hn, hu with
    | 1, _, hu =>
        rcases hu with h | h
        · rw [h]; have := D.tr2_fixed h2 a hθa 1 le_rfl; rwa [pow_one] at this
        · rw [Set.mem_singleton_iff.1 h]; exact tr2_zero_of_tw_neg D h2 tV
    | 2, _, hu =>
        rcases hu with h | h | h
        · rw [h]; exact tr2_zero_of_tw_neg D h2 (by rw [map_mul D.tw2, tX, tV, mul_neg])
        · rw [h]; exact tr2_zero_of_tw_neg D h2 (by rw [map_mul D.tw2, tX, tV, neg_mul])
        · rw [Set.mem_singleton_iff.1 h, sq]
          apply tr2_zero_of_eq_neg D h2
          conv_lhs => rw [rot, tV, mul_neg, map_neg]
    | 3, _, hu =>
        have h1 : D.tr2 h2 (V ^ 2 * X) = D.tr2 h2 (X * V ^ 2) := by
          rw [rot, map_pow, tV, neg_sq]
        have h3 : D.tr2 h2 (V * X * V) = -D.tr2 h2 (X * V ^ 2) := by
          rw [mul_assoc, rot, tV, mul_neg, map_neg, mul_assoc, ← sq]
        have h4 : D.tr2 h2 (X * V ^ 2) = 0 := by
          have := congrArg (D.tr2 h2) hrel
          rw [map_add, map_add, h1, h3, map_zero] at this
          rw [← this]; abel
        rcases hu with h | h | h
        · rw [h]; exact tr2_zero_of_tw_neg D h2 (by rw [map_mul D.tw2, map_mul D.tw2, tX, tV]; noncomm_ring)
        · rw [h]; exact h4
        · rw [Set.mem_singleton_iff.1 h, h3, h4, neg_zero]
    | 4, _, hu =>
        rcases hu with h | h
        · rw [h, show X * V * X * V = (X * V) * (X * V) by noncomm_ring]
          apply tr2_zero_of_eq_neg D h2
          conv_lhs => rw [rot, map_mul D.tw2, tX, tV,
            show X * V * (X * -V) = -((X * V) * (X * V)) by noncomm_ring, map_neg]
        · rw [Set.mem_singleton_iff.1 h]
          exact tr2_zero_of_tw_neg D h2 (by rw [map_mul D.tw2, map_mul D.tw2, map_pow, tX, tV]; noncomm_ring)
    | 5, _, hu =>
        rw [Set.mem_singleton_iff.1 hu]
        exact tr2_zero_of_tw_neg D h2 (by
          rw [map_mul D.tw2, map_mul D.tw2, map_mul D.tw2, map_pow, tX, tV]; noncomm_ring)
    | n + 6, _, hu => exact absurd hu (by simp [e6Table])
  exact e6_tr_of_span D h2 hab hac hbc hLa hLb hLc (· = 0)
    (fun n m hm ↦ cancel_two_pow h2 n hm) w (fun r hr ↦ tr2_span_zero D h2 _ (hgen _ hw) hr)

include h2 hab hac hbc hLa hLb hLc in
/-- **The ordinary traces of `E_6`** (`periodic-mesh-calculations.tex`): all
positive traces vanish except possibly in word degree three, where they are
killed by `3`. -/
theorem trace_E6_id (hθa : D.θ a = a) (hθb : D.θ b = b) (hθc : D.θ c = c)
    (w : List (Fin 3)) (hw : 1 ≤ w.length) :
    (w.length ≠ 3 → D.tr w = 0) ∧ 3 • D.tr w = 0 := by
  have hx := e6_hx (L := L) hLa
  obtain ⟨hv3, hrel⟩ := e6_rels (L := L) hab hac hbc hLa hLb hLc
  have hs := e6_sum (L := L) hab hac hbc
  set X := y L a
  set V := vE6 (L := L) b c
  have tX : D.tw2 X = X := by rw [D.tw2_y, hθa]
  have tV : D.tw2 V = V := by simp only [V, vE6, map_sub, D.tw2_y, hθb, hθc]
  have rot : ∀ p q : R2 L, D.tr2 h2 (p * q) = D.tr2 h2 (q * D.tw2 p) := D.tr2_rotate h2
  have fixb : ∀ q, 1 ≤ q → D.tr2 h2 (y L b ^ q) = 0 := D.tr2_fixed h2 b hθb
  have fixc : ∀ q, 1 ≤ q → D.tr2 h2 (y L c ^ q) = 0 := D.tr2_fixed h2 c hθc
  -- degree two
  have hXV2 : D.tr2 h2 (V * V) = 0 ∧ D.tr2 h2 (X * V) = 0 := by
    have rVX : D.tr2 h2 (V * X) = D.tr2 h2 (X * V) := by rw [rot, tV]
    have hc : y L c = -(X + y L b) := eq_neg_of_add_eq_zero_right hs
    have e1 : V - X = 2 * y L b := by simp only [V, vE6]; rw [hc]; noncomm_ring
    have e2 : V + X = -(2 * y L c) := by simp only [V, vE6]; rw [hc]; noncomm_ring
    have t1 : D.tr2 h2 ((V - X) * (V - X)) = 0 := by
      rw [e1, show 2 * y L b * (2 * y L b) = (2 ^ 2 : R2 L) * y L b ^ 2 by
        rw [sq, sq]; noncomm_ring, tr2_nsmul_two_pow D h2, fixb 2 (by norm_num), smul_zero]
    have t2 : D.tr2 h2 ((V + X) * (V + X)) = 0 := by
      rw [e2, show -(2 * y L c) * -(2 * y L c) = (2 ^ 2 : R2 L) * y L c ^ 2 by
        rw [sq, sq]; noncomm_ring, tr2_nsmul_two_pow D h2, fixc 2 (by norm_num), smul_zero]
    rw [show (V - X) * (V - X) = V * V - V * X - X * V + X * X by noncomm_ring, hx, add_zero,
      map_sub, map_sub, rVX] at t1
    rw [show (V + X) * (V + X) = V * V + V * X + X * V + X * X by noncomm_ring, hx, add_zero,
      map_add, map_add, rVX] at t2
    set A := D.tr2 h2 (V * V)
    set B := D.tr2 h2 (X * V)
    have hA : A = 0 := h2 A (calc A + A = (A - B - B) + (A + B + B) := by abel
      _ = 0 := by rw [t1, t2, add_zero])
    refine ⟨hA, h2 B ?_⟩
    calc B + B = (A + B + B) - A := by abel
      _ = 0 := by rw [t2, hA, sub_zero]
  have hV2 : D.tr2 h2 (V ^ 2) = 0 := by rw [sq]; exact hXV2.1
  have hgen : ∀ n, 1 ≤ n → n ≠ 3 → ∀ u ∈ e6Table X V n, D.tr2 h2 u = 0 := by
    intro n hn h3 u hu
    match n, hn, h3, hu with
    | 1, _, _, hu =>
        rcases hu with h | h
        · rw [h]; have := D.tr2_fixed h2 a hθa 1 le_rfl; rwa [pow_one] at this
        · rw [Set.mem_singleton_iff.1 h]
          have e1 := fixb 1 le_rfl
          have e2 := fixc 1 le_rfl
          rw [pow_one] at e1 e2
          simp only [V, vE6, map_sub, e1, e2, sub_zero]
    | 2, _, _, hu =>
        rcases hu with h | h | h
        · rw [h]; exact hXV2.2
        · rw [h, rot, tV]; exact hXV2.2
        · rw [Set.mem_singleton_iff.1 h]; exact hV2
    | 4, _, _, hu =>
        rcases hu with h | h
        · rw [h, ← neg_neg (X * V * X * V), ← e6_xv2x X V hx hrel, map_neg,
            show X * V ^ 2 * X = X * (V ^ 2 * X) by noncomm_ring, rot, tX, mul_assoc, hx, mul_zero,
            map_zero, neg_zero]
        · rw [Set.mem_singleton_iff.1 h, show V * X * V ^ 2 = V * (X * V ^ 2) by noncomm_ring, rot, tV,
            show X * V ^ 2 * V = X * V ^ 3 by noncomm_ring, e6_xv3 X V hx hv3, map_zero]
    | 5, _, _, hu =>
        rw [Set.mem_singleton_iff.1 hu]
        apply tr2_zero_of_eq_neg D h2
        have hp : D.tw2 (V * X * V ^ 2) = V * X * V ^ 2 := by
          rw [map_mul D.tw2, map_mul D.tw2, map_pow, tV, tX]
        calc D.tr2 h2 (X * V * X * V ^ 2) = -D.tr2 h2 (V * X * V ^ 2 * X) := by
              rw [e6_psi4'x X V hx hrel, map_neg, neg_neg]
          _ = -D.tr2 h2 (X * V * X * V ^ 2) := by
              rw [rot, hp, show X * (V * X * V ^ 2) = X * V * X * V ^ 2 by noncomm_ring]
    | n + 6, _, _, hu => exact absurd hu (by simp [e6Table])
  have hgen3 : ∀ u ∈ e6Table X V 3, 3 • D.tr2 h2 u = 0 := by
    have h1 : D.tr2 h2 (V ^ 2 * X) = D.tr2 h2 (X * V ^ 2) := by rw [rot, map_pow, tV]
    have h3 : D.tr2 h2 (V * X * V) = D.tr2 h2 (X * V ^ 2) := by
      rw [mul_assoc, rot, tV, mul_assoc, ← sq]
    have h4 : 3 • D.tr2 h2 (X * V ^ 2) = 0 := by
      have := congrArg (D.tr2 h2) hrel
      rw [map_add, map_add, h1, h3, map_zero] at this
      rw [← this]; abel
    intro u hu
    rcases hu with h | h | h
    · rw [h, show X * V * X = X * (V * X) by noncomm_ring, rot, tX, mul_assoc, hx, mul_zero,
        map_zero, smul_zero]
    · rw [h]; exact h4
    · rw [Set.mem_singleton_iff.1 h, h3]; exact h4
  have hP : ∀ m : M, (∀ n : ℕ, (2 ^ n : ℕ) • m = 0 → m = 0) := fun m n hm ↦ cancel_two_pow h2 n hm
  refine ⟨fun h3 ↦ e6_tr_of_span D h2 hab hac hbc hLa hLb hLc (· = 0) (fun n m hm ↦ hP m n hm) w
    (fun r hr ↦ tr2_span_zero D h2 _ (hgen _ hw h3) hr), ?_⟩
  by_cases h3 : w.length = 3
  · refine e6_tr_of_span D h2 hab hac hbc hLa hLb hLc (fun m ↦ 3 • m = 0)
      (fun n m hm ↦ hP _ n (by rw [smul_comm]; exact hm)) w (fun r hr ↦ ?_)
    rw [h3] at hr
    induction hr using AddSubgroup.closure_induction with
    | mem u hu => exact hgen3 u hu
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, smul_add, ha, hb, add_zero]
    | neg a _ ha => rw [map_neg, smul_neg, ha, neg_zero]
  · rw [e6_tr_of_span D h2 hab hac hbc hLa hLb hLc (· = 0) (fun n m hm ↦ hP m n hm) w
      (fun r hr ↦ tr2_span_zero D h2 _ (hgen _ hw h3) hr), smul_zero]

end E6

end TraceAlg

end MultiplicativeBasisDeformations
