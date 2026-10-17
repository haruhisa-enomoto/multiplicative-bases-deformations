import MultiplicativeBasisDeformations.Foundations.E7Return
import MultiplicativeBasisDeformations.Foundations.TraceTypesAD

/-!
# Lemma B.1: top paths of `Π(D_n)`

`lem:d-top-paths` (`characteristic-two-mesh-calculations.tex:128–203`): "Let `Π(D_n)`
be the preprojective algebra of type `D_n`, and put `N = n − 2`. Let `ν` be the
identity if `N` is even and the short-arm interchange if `N` is odd. At every
vertex `x`, there is a nonzero path of degree `2N` from `x` to `ν x`. This holds over
every field."

The proof computes the recurrence matrices `U_d` of `eq:preprojective-lower-bound`
through the line formula: on the line `−N, …, N`,
`(V_d)_{ij} = 1` exactly when `|i − j| ≤ d ≤ 2N − |i + j|` and `d ≡ i − j (mod 2)`,
and for `D_n`
`(U_d)_{rt} = (V_d)_{r,t} + (V_d)_{r,−t}`, `(U_d)_{ar} = (U_d)_{br} = (V_d)_{0,r}`,
with the short-leaf block `½[[1 + (−1)^q, 1 − (−1)^q], [1 − (−1)^q, 1 + (−1)^q]]` in
degree `d = 2q` and zero in odd degree. We check that this closed form satisfies the
recurrence for `d ≤ 2N` (`F_rec`), so it equals `U_d` (`U_eq_F`); it is nonnegative,
and `U_{2N}` is the permutation matrix of `ν`: the identity for `N` even (`d_return`, the case
used in Appendix B) and the short-arm interchange `nu` for `N` odd (`d_return_odd`); both
together are `dTopPaths`.

Labels: the star has short arms `a, b` with one vertex each and the long arm `c`;
the spine vertex at depth `j` of the long arm has line position `j + 1` and the
centre has position `1`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace DTop

/-! ### The line formula -/

/-- `V_d(i, j)` on the line `−N, …, N`. -/
def V (N : ℕ) (d : ℕ) (i j : ℤ) : ℤ :=
  if i - j ≤ d ∧ j - i ≤ d ∧ (d : ℤ) + i + j ≤ 2 * N ∧ (d : ℤ) - i - j ≤ 2 * N ∧
    ((d : ℤ) - (i - j)) % 2 = 0 then 1 else 0

theorem V_nonneg (N d : ℕ) (i j : ℤ) : 0 ≤ V N d i j := by unfold V; split_ifs <;> norm_num

theorem V_symm (N d : ℕ) (i j : ℤ) : V N d i j = V N d j i := by
  unfold V; split_ifs <;> omega

theorem V_neg (N d : ℕ) (i j : ℤ) : V N d (-i) (-j) = V N d i j := by
  unfold V; split_ifs <;> omega

/-- **The line recurrence** `V_{d+2} = A V_{d+1} − V_d`. -/
theorem V_rec (N d : ℕ) (hd : d + 2 ≤ 2 * N) (i j : ℤ) (hi : -N ≤ i ∧ i ≤ N) (hj : -N ≤ j ∧ j ≤ N) :
    V N (d + 2) i j = V N (d + 1) (i - 1) j + V N (d + 1) (i + 1) j - V N d i j := by
  unfold V
  push_cast
  split_ifs <;> omega

/-! ### Sums over neighbours -/

section Nb

variable {t : ℕ} {L : Fin t → ℕ}


/-- The sum of a function over the neighbours of a vertex of the star. -/
def nb (g : StarV L → ℤ) : StarV L → ℤ
  | none => ∑ i, g (some ⟨i, 0⟩)
  | some ⟨i, j⟩ =>
      (if h : (j : ℕ) = 0 then g none else g (some ⟨i, ⟨j - 1, by omega⟩⟩)) +
        (if h : (j : ℕ) < L i then g (some ⟨i, ⟨j + 1, by omega⟩⟩) else 0)

theorem ite_adj {x z : StarV L} (g : ℤ) (P : Prop) [Decidable P] [Decidable (starAdj x z)]
    (h : starAdj x z ↔ P) : (if starAdj x z then (1 : ℤ) else 0) * g = if P then g else 0 := by
  by_cases hP : P
  · rw [if_pos (h.2 hP), if_pos hP, one_mul]
  · rw [if_neg (fun h' ↦ hP (h.1 h')), if_neg hP, zero_mul]

open Classical in
theorem sum_adjM (x : StarV L) (g : StarV L → ℤ) :
    ∑ z : (starTree L).Dbl, (starTree L).adjM x z * g z = nb g x := by
  change ∑ z : StarV L, (if starAdj x z then (1 : ℤ) else 0) * g z = nb g x
  rw [Fintype.sum_option, Fintype.sum_sigma]
  rcases x with _ | ⟨i, ⟨j, hj⟩⟩
  · rw [ite_adj _ False Iff.rfl, if_neg not_false, zero_add, nb]
    refine Finset.sum_congr rfl fun i' _ ↦ ?_
    rw [Finset.sum_congr rfl fun j' _ ↦ ite_adj (x := none) (z := some ⟨i', j'⟩) _
      ((j' : ℕ) = 0) Iff.rfl]
    rw [Finset.sum_eq_single (0 : Fin (L i' + 1))]
    · simp
    · intro j' _ hj'
      rw [if_neg]
      intro h; exact hj' (Fin.ext h)
    · simp
  · rw [ite_adj _ (j = 0) Iff.rfl, nb]
    rw [Finset.sum_eq_single i]
    · -- the arm of `x`
      have e : ∀ j' : Fin (L i + 1),
          (if starAdj (some ⟨i, ⟨j, hj⟩⟩) (some ⟨i, j'⟩) then (1 : ℤ) else 0) * g (some ⟨i, j'⟩) =
            (if (j' : ℕ) = j + 1 then g (some ⟨i, j'⟩) else 0) +
              (if (j' : ℕ) + 1 = j then g (some ⟨i, j'⟩) else 0) := by
        intro j'
        rw [ite_adj _ (i = i ∧ ((j' : ℕ) = j + 1 ∨ j = j' + 1)) Iff.rfl]
        by_cases h1 : (j' : ℕ) = j + 1
        · rw [if_pos ⟨rfl, Or.inl h1⟩, if_pos h1, if_neg (by omega), add_zero]
        · by_cases h2 : (j' : ℕ) + 1 = j
          · rw [if_pos ⟨rfl, Or.inr h2.symm⟩, if_neg h1, if_pos h2, zero_add]
          · rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]
      rw [Finset.sum_congr rfl fun j' _ ↦ e j', Finset.sum_add_distrib]
      have s1 : ∑ j' : Fin (L i + 1), (if (j' : ℕ) = j + 1 then g (some ⟨i, j'⟩) else 0) =
          if h : j < L i then g (some ⟨i, ⟨j + 1, by omega⟩⟩) else 0 := by
        split_ifs with h
        · rw [Finset.sum_eq_single (⟨j + 1, by omega⟩ : Fin (L i + 1))]
          · simp
          · intro j' _ hj'; rw [if_neg]; intro h'; exact hj' (Fin.ext h')
          · simp
        · refine Finset.sum_eq_zero fun j' _ ↦ ?_
          rw [if_neg]; have := j'.2; omega
      have s2 : ∑ j' : Fin (L i + 1), (if (j' : ℕ) + 1 = j then g (some ⟨i, j'⟩) else 0) =
          if h : j = 0 then 0 else g (some ⟨i, ⟨j - 1, by omega⟩⟩) := by
        split_ifs with h
        · refine Finset.sum_eq_zero fun j' _ ↦ ?_
          rw [if_neg]; omega
        · rw [Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin (L i + 1))]
          · simp only [if_pos (show j - 1 + 1 = j by omega)]
          · intro j' _ hj'; rw [if_neg]; intro h'; exact hj' (Fin.ext (by simp; omega))
          · simp
      rw [s1, s2]
      by_cases h0 : j = 0
      · subst h0
        simp
      · rw [if_neg h0, dif_neg h0, dif_neg h0, zero_add]
        ring
    · intro i' _ hi'
      refine Finset.sum_eq_zero fun j' _ ↦ ?_
      rw [ite_adj _ (i = i' ∧ ((j' : ℕ) = j + 1 ∨ j = j' + 1)) Iff.rfl, if_neg]
      rintro ⟨h, -⟩; exact hi' h.symm
    · simp

end Nb

/-! ### The star of type `D` -/

variable {L : Fin 3 → ℕ} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hLa : L a = 0) (hLb : L b = 0)

/-- The line position of a spine vertex (the centre and the long arm). -/
def spos (c : Fin 3) : StarV L → Option ℤ
  | none => some 1
  | some x => if x.1 = c then some ((x.2 : ℕ) + 2) else none

open Classical in
/-- **The closed form of `U_d`.** -/
def F (c : Fin 3) (N d : ℕ) (x y : StarV L) : ℤ :=
  match spos c x, spos c y with
  | some r, some t => V N d r t + V N d r (-t)
  | none, some t => V N d 0 t
  | some r, none => V N d r 0
  | none, none => if d % 2 = 1 then 0 else if (x = y ↔ d / 2 % 2 = 0) then 1 else 0

theorem F_nonneg (c : Fin 3) (N d : ℕ) (x y : StarV L) : 0 ≤ F c N d x y := by
  unfold F
  split
  · exact add_nonneg (V_nonneg _ _ _ _) (V_nonneg _ _ _ _)
  · exact V_nonneg _ _ _ _
  · exact V_nonneg _ _ _ _
  · split_ifs <;> norm_num

/-! ### The recurrence -/

/-- The short-leaf block: `[q even]` on the diagonal and `[q odd]` off it, in degree `2q`. -/
def LL (d : ℕ) (same : Prop) [Decidable same] : ℤ :=
  if d % 2 = 1 then 0 else if (same ↔ d / 2 % 2 = 0) then 1 else 0

section Identities

variable (N d : ℕ) (hd : d + 2 ≤ 2 * N)

theorem V_out (d : ℕ) (j : ℤ) (hj : -N ≤ j ∧ j ≤ N) : V N d (N + 1) j = 0 := by
  unfold V; split_ifs <;> omega

theorem V_zero_neg (d : ℕ) (t : ℤ) : V N d 0 (-t) = V N d 0 t := by
  unfold V; split_ifs <;> omega

theorem V_neg_one (d : ℕ) (t : ℤ) : V N d (-1) t = V N d 1 (-t) := by
  unfold V; split_ifs <;> omega

include hd

theorem I1 (r t : ℤ) (hr : 2 ≤ r ∧ r ≤ N) (ht : 1 ≤ t ∧ t ≤ N) :
    V N (d + 2) r t + V N (d + 2) r (-t) =
      (V N (d + 1) (r - 1) t + V N (d + 1) (r - 1) (-t)) +
        (if r < N then V N (d + 1) (r + 1) t + V N (d + 1) (r + 1) (-t) else 0) -
          (V N d r t + V N d r (-t)) := by
  rw [V_rec N d hd r t (by omega) (by omega), V_rec N d hd r (-t) (by omega) (by omega)]
  split_ifs with h
  · ring
  · obtain rfl : r = N := by omega
    rw [V_out N (d + 1) t (by omega), V_out N (d + 1) (-t) (by omega)]
    ring

theorem I2 (r : ℤ) (hr : 2 ≤ r ∧ r ≤ N) :
    V N (d + 2) r 0 = V N (d + 1) (r - 1) 0 + (if r < N then V N (d + 1) (r + 1) 0 else 0) -
      V N d r 0 := by
  rw [V_rec N d hd r 0 (by omega) (by omega)]
  split_ifs with h
  · ring
  · obtain rfl : r = N := by omega
    rw [V_out N (d + 1) 0 (by omega), add_zero]

theorem I3 (t : ℤ) (ht : 1 ≤ t ∧ t ≤ N) :
    V N (d + 2) 1 t + V N (d + 2) 1 (-t) =
      V N (d + 1) 0 t + V N (d + 1) 0 t + (V N (d + 1) 2 t + V N (d + 1) 2 (-t)) -
        (V N d 1 t + V N d 1 (-t)) := by
  rw [V_rec N d hd 1 t (by omega) (by omega), V_rec N d hd 1 (-t) (by omega) (by omega),
    show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, V_zero_neg]
  ring

theorem V00 : V N (d + 1) 0 0 = LL (d + 1) True + LL (d + 1) False := by
  unfold V LL; push_cast; simp only [true_iff, false_iff]; split_ifs <;> omega

theorem I4 : V N (d + 2) 1 0 = LL (d + 1) True + LL (d + 1) False + V N (d + 1) 2 0 - V N d 1 0 := by
  rw [V_rec N d hd 1 0 (by omega) (by omega), show (1 : ℤ) - 1 = 0 by norm_num,
    show (1 : ℤ) + 1 = 2 by norm_num, V00 N d hd]

theorem I5 (t : ℤ) (ht : 1 ≤ t ∧ t ≤ N) :
    V N (d + 2) 0 t = V N (d + 1) 1 t + V N (d + 1) 1 (-t) - V N d 0 t := by
  rw [V_rec N d hd 0 t (by omega) (by omega), show (0 : ℤ) - 1 = -1 by norm_num,
    show (0 : ℤ) + 1 = 1 by norm_num, V_neg_one]
  ring

theorem I6 (same : Prop) [Decidable same] :
    LL (d + 2) same = V N (d + 1) 1 0 - LL d same := by
  unfold V LL
  push_cast
  by_cases hs : same <;> simp only [hs, true_iff, false_iff] <;> split_ifs <;> omega

end Identities

/-! ### Values of the closed form by vertex kind -/

section Kinds

variable (c : Fin 3) (N d : ℕ)

theorem F_ss {x y : StarV L} {r t : ℤ} (hx : spos c x = some r) (hy : spos c y = some t) :
    F c N d x y = V N d r t + V N d r (-t) := by
  unfold F; rw [hx, hy]

theorem F_ls {x y : StarV L} {t : ℤ} (hx : spos c x = none) (hy : spos c y = some t) :
    F c N d x y = V N d 0 t := by
  unfold F; rw [hx, hy]

theorem F_sl {x y : StarV L} {r : ℤ} (hx : spos c x = some r) (hy : spos c y = none) :
    F c N d x y = V N d r 0 := by
  unfold F; rw [hx, hy]

open Classical in
theorem F_ll {x y : StarV L} (hx : spos c x = none) (hy : spos c y = none) :
    F c N d x y = LL d (x = y) := by
  unfold F LL; rw [hx, hy]

theorem spos_none : spos (L := L) c none = some 1 := rfl

theorem spos_c (j : Fin (L c + 1)) : spos (L := L) c (some ⟨c, j⟩) = some (((j : ℕ) : ℤ) + 2) := by
  simp [spos]

theorem spos_leaf {i : Fin 3} (hi : i ≠ c) (j : Fin (L i + 1)) :
    spos (L := L) c (some ⟨i, j⟩) = none := by
  simp [spos, hi]

end Kinds

theorem LL_congr (d : ℕ) {P P' : Prop} [Decidable P] [Decidable P'] (h : P ↔ P') :
    LL d P = LL d P' := by
  unfold LL; simp only [h]

include hab hac hbc hLa hLb in
theorem F_rec (d : ℕ) (hd : d + 2 ≤ 2 * (L c + 2)) (x y : StarV L) :
    F c (L c + 2) (d + 2) x y =
      nb (fun z ↦ F c (L c + 2) (d + 1) z y) x - F c (L c + 2) d x y := by
  classical
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  have hba : b ≠ a := Ne.symm hab
  set N := L c + 2 with hN
  -- the kind of `y`
  have hy : (∃ t : ℤ, spos c y = some t ∧ 1 ≤ t ∧ t ≤ N) ∨
      (spos c y = none ∧ ∃ i ≠ c, ∃ j : Fin (L i + 1), y = some ⟨i, j⟩) := by
    rcases y with _ | ⟨i, j⟩
    · exact Or.inl ⟨1, rfl, le_rfl, by omega⟩
    · rcases TraceAlg.fin_three_cases hab hac hbc i with h | h | h <;> subst i
      · exact Or.inr ⟨spos_leaf c hac j, a, hac, j, rfl⟩
      · exact Or.inr ⟨spos_leaf c hbc j, b, hbc, j, rfl⟩
      · refine Or.inl ⟨(j : ℕ) + 2, spos_c c j, by omega, ?_⟩
        have := j.2; omega
  have hL0 : ∀ i, i ≠ c → L i = 0 := by
    intro i hi
    rcases TraceAlg.fin_three_cases hab hac hbc i with h | h | h <;> subst i
    · exact hLa
    · exact hLb
    · exact absurd rfl hi
  have leafE : ∀ (i : Fin 3) (hi : i ≠ c) (j : Fin (L i + 1)),
      nb (fun z ↦ F c N (d + 1) z y) (some ⟨i, j⟩) = F c N (d + 1) none y := by
    intro i hi j
    obtain ⟨j, hj⟩ := j
    obtain rfl : j = 0 := by have := hL0 i hi; omega
    simp only [nb, dif_pos, hL0 i hi, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero]
  -- two leaves are equal iff they lie on the same arm
  have leafEq : ∀ (i i' : Fin 3) (hi : i ≠ c) (hi' : i' ≠ c) (j : Fin (L i + 1))
      (j' : Fin (L i' + 1)), (some ⟨i, j⟩ : StarV L) = some ⟨i', j'⟩ ↔ i = i' := by
    intro i i' hi hi' j j'
    constructor
    · intro h; simp only [Option.some.injEq, Sigma.mk.inj_iff] at h; exact h.1
    · rintro rfl
      have hj : j = j' := Fin.ext (by have := j.2; have := j'.2; have := hL0 i hi; omega)
      rw [hj]
  rcases x with _ | ⟨i, ⟨j, hj⟩⟩
  · -- the centre: neighbours `a₀`, `b₀`, `c₀`
    rw [nb, TraceAlg.sum_fin_three _ hab hac hbc]
    rcases hy with ⟨t, hyt, ht⟩ | ⟨hyn, i', hi', j', rfl⟩
    · rw [F_ss c N _ (spos_none c) hyt, F_ss c N _ (spos_none c) hyt,
        F_ls c N _ (spos_leaf c hac _) hyt, F_ls c N _ (spos_leaf c hbc _) hyt,
        F_ss c N _ (spos_c c _) hyt]
      simp only [Fin.val_zero, Nat.cast_zero, zero_add]
      exact I3 N d hd t ht
    · rw [F_sl c N _ (spos_none c) hyn, F_sl c N _ (spos_none c) hyn,
        F_ll c N _ (spos_leaf c hac _) hyn, F_ll c N _ (spos_leaf c hbc _) hyn,
        F_sl c N _ (spos_c c _) hyn]
      simp only [Fin.val_zero, Nat.cast_zero, zero_add]
      rw [I4 N d hd, LL_congr (d + 1) (leafEq _ _ hac hi' _ _),
        LL_congr (d + 1) (leafEq _ _ hbc hi' _ _)]
      rcases TraceAlg.fin_three_cases hab hac hbc i' with h | h | h <;> subst i'
      · rw [LL_congr (d + 1) (iff_true_intro rfl), LL_congr (d + 1) (iff_false_intro hba)]
      · rw [LL_congr (d + 1) (iff_false_intro hab), LL_congr (d + 1) (iff_true_intro rfl)]
        ring
      · exact absurd rfl hi'
  · rcases TraceAlg.fin_three_cases hab hac hbc i with h | h | h <;> subst i
    · rw [leafE a hac]
      rcases hy with ⟨t, hyt, ht⟩ | ⟨hyn, -⟩
      · rw [F_ls c N _ (spos_leaf c hac _) hyt, F_ss c N _ (spos_none c) hyt,
          F_ls c N _ (spos_leaf c hac _) hyt]
        exact I5 N d hd t ht
      · rw [F_ll c N _ (spos_leaf c hac _) hyn, F_sl c N _ (spos_none c) hyn,
          F_ll c N _ (spos_leaf c hac _) hyn]
        exact I6 N d hd _
    · rw [leafE b hbc]
      rcases hy with ⟨t, hyt, ht⟩ | ⟨hyn, -⟩
      · rw [F_ls c N _ (spos_leaf c hbc _) hyt, F_ss c N _ (spos_none c) hyt,
          F_ls c N _ (spos_leaf c hbc _) hyt]
        exact I5 N d hd t ht
      · rw [F_ll c N _ (spos_leaf c hbc _) hyn, F_sl c N _ (spos_none c) hyn,
          F_ll c N _ (spos_leaf c hbc _) hyn]
        exact I6 N d hd _
    · -- the long arm, at line position `r = j + 2`
      have hx : spos c (some ⟨c, ⟨j, hj⟩⟩ : StarV L) = some ((j : ℤ) + 2) := spos_c c ⟨j, hj⟩
      have nbE : ∀ G : ℤ → ℤ, (∀ (r : ℤ) (z : StarV L), spos c z = some r →
          F c N (d + 1) z y = G r) →
          nb (fun z ↦ F c N (d + 1) z y) (some ⟨c, ⟨j, hj⟩⟩) =
            G ((j : ℤ) + 2 - 1) + (if (j : ℤ) + 2 < N then G ((j : ℤ) + 2 + 1) else 0) := by
        intro G hG
        simp only [nb]
        congr 1
        · split_ifs with h0
          · rw [hG 1 none rfl]; congr 1; omega
          · rw [hG _ _ (spos_c c _)]; congr 1; simp only; omega
        · split_ifs with h1 h2 h2
          · rw [hG _ _ (spos_c c _)]; congr 1
          · omega
          · omega
          · rfl
      rcases hy with ⟨t, hyt, ht⟩ | ⟨hyn, -⟩
      · rw [nbE (fun r ↦ V N (d + 1) r t + V N (d + 1) r (-t))
          (fun r z hz ↦ F_ss c N _ hz hyt), F_ss c N _ hx hyt, F_ss c N _ hx hyt]
        exact I1 N d hd _ t ⟨by omega, by omega⟩ ht
      · rw [nbE (fun r ↦ V N (d + 1) r 0) (fun r z hz ↦ F_sl c N _ hz hyn), F_sl c N _ hx hyn,
          F_sl c N _ hx hyn]
        exact I2 N d hd _ ⟨by omega, by omega⟩

/-! ### Initial values and the identification with `U_d` -/

theorem adjM_eq {t : ℕ} {L : Fin t → ℕ} (x y : StarV L) (P : Prop) [Decidable P]
    (h : starAdj x y ↔ P) : (starTree L).adjM x y = if P then 1 else 0 := by
  classical
  change (if starAdj x y then (1 : ℤ) else 0) = _
  by_cases hP : P
  · rw [if_pos (h.2 hP), if_pos hP]
  · rw [if_neg (fun h' ↦ hP (h.1 h')), if_neg hP]

include hab hac hbc hLa hLb in
theorem F_init (x y : StarV L) :
    F c (L c + 2) 0 x y = (if x = y then 1 else 0) ∧
      F c (L c + 2) 1 x y = (starTree L).adjM x y := by
  classical
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  have hba : b ≠ a := Ne.symm hab
  rcases x with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases y with _ | ⟨i', ⟨j', hj'⟩⟩
  · rw [F_ss c _ _ (spos_none c) (spos_none c), F_ss c _ _ (spos_none c) (spos_none c),
      adjM_eq _ _ False Iff.rfl]
    unfold V; simp only [if_true, if_false]; constructor <;> split_ifs <;> omega
  · rcases TraceAlg.fin_three_cases hab hac hbc i' with h | h | h <;> subst i'
    · obtain rfl : j' = 0 := by omega
      rw [F_sl c _ _ (spos_none c) (spos_leaf c hac _), F_sl c _ _ (spos_none c) (spos_leaf c hac _),
        adjM_eq none (some ⟨a, ⟨0, hj'⟩⟩) True (by simp [starAdj])]
      unfold V; simp only [if_true, if_false, reduceCtorEq]; constructor <;> split_ifs <;> omega
    · obtain rfl : j' = 0 := by omega
      rw [F_sl c _ _ (spos_none c) (spos_leaf c hbc _), F_sl c _ _ (spos_none c) (spos_leaf c hbc _),
        adjM_eq none (some ⟨b, ⟨0, hj'⟩⟩) True (by simp [starAdj])]
      unfold V; simp only [if_true, if_false, reduceCtorEq]; constructor <;> split_ifs <;> omega
    · rw [F_ss c _ _ (spos_none c) (spos_c c _), F_ss c _ _ (spos_none c) (spos_c c _),
        adjM_eq _ _ (j' = 0) Iff.rfl]
      unfold V; simp only [reduceCtorEq, if_false]; constructor <;> split_ifs <;> omega
  · rcases TraceAlg.fin_three_cases hab hac hbc i with h | h | h <;> subst i
    · obtain rfl : j = 0 := by omega
      rw [F_ls c _ _ (spos_leaf c hac _) (spos_none c), F_ls c _ _ (spos_leaf c hac _) (spos_none c),
        adjM_eq (some ⟨a, ⟨0, hj⟩⟩) none True (by simp [starAdj])]
      unfold V; simp only [if_true, if_false, reduceCtorEq]; constructor <;> split_ifs <;> omega
    · obtain rfl : j = 0 := by omega
      rw [F_ls c _ _ (spos_leaf c hbc _) (spos_none c), F_ls c _ _ (spos_leaf c hbc _) (spos_none c),
        adjM_eq (some ⟨b, ⟨0, hj⟩⟩) none True (by simp [starAdj])]
      unfold V; simp only [if_true, if_false, reduceCtorEq]; constructor <;> split_ifs <;> omega
    · rw [F_ss c _ _ (spos_c c _) (spos_none c), F_ss c _ _ (spos_c c _) (spos_none c),
        adjM_eq _ _ (j = 0) Iff.rfl]
      unfold V; simp only [reduceCtorEq, if_false]; constructor <;> split_ifs <;> omega
  · have hsome : ∀ (i i' : Fin 3) (j : Fin (L i + 1)) (j' : Fin (L i' + 1)),
        ((some ⟨i, j⟩ : StarV L) = some ⟨i', j'⟩ ↔ i = i' ∧ (j : ℕ) = j') := by
      intro i i' j j'
      constructor
      · intro h
        simp only [Option.some.injEq, Sigma.mk.inj_iff] at h
        obtain ⟨rfl, h⟩ := h
        exact ⟨rfl, by rw [eq_of_heq h]⟩
      · rintro ⟨rfl, h⟩
        rw [Fin.ext h]
    rcases TraceAlg.fin_three_cases hab hac hbc i with h | h | h <;> subst i <;>
      rcases TraceAlg.fin_three_cases hab hac hbc i' with h' | h' | h' <;> subst i'
    · obtain rfl : j = 0 := by omega
      obtain rfl : j' = 0 := by omega
      rw [F_ll c _ _ (spos_leaf c hac _) (spos_leaf c hac _),
        F_ll c _ _ (spos_leaf c hac _) (spos_leaf c hac _),
        adjM_eq (some ⟨a, ⟨0, hj⟩⟩) (some ⟨a, ⟨0, hj'⟩⟩) False (by simp [starAdj])]
      simp [LL]
    · obtain rfl : j = 0 := by omega
      obtain rfl : j' = 0 := by omega
      rw [F_ll c _ _ (spos_leaf c hac _) (spos_leaf c hbc _),
        F_ll c _ _ (spos_leaf c hac _) (spos_leaf c hbc _),
        adjM_eq (some ⟨a, ⟨0, hj⟩⟩) (some ⟨b, ⟨0, hj'⟩⟩) False (by simp [starAdj, hab])]
      simp [LL, hab]
    · obtain rfl : j = 0 := by omega
      rw [F_ls c _ _ (spos_leaf c hac _) (spos_c c _), F_ls c _ _ (spos_leaf c hac _) (spos_c c _),
        adjM_eq (some ⟨a, ⟨0, hj⟩⟩) (some ⟨c, ⟨j', hj'⟩⟩) False (by simp [starAdj, hac])]
      unfold V; simp only [hsome, hac, false_and, if_false]; constructor <;> split_ifs <;> omega
    · obtain rfl : j = 0 := by omega
      obtain rfl : j' = 0 := by omega
      rw [F_ll c _ _ (spos_leaf c hbc _) (spos_leaf c hac _),
        F_ll c _ _ (spos_leaf c hbc _) (spos_leaf c hac _),
        adjM_eq (some ⟨b, ⟨0, hj⟩⟩) (some ⟨a, ⟨0, hj'⟩⟩) False (by simp [starAdj, hba])]
      simp [LL, hba]
    · obtain rfl : j = 0 := by omega
      obtain rfl : j' = 0 := by omega
      rw [F_ll c _ _ (spos_leaf c hbc _) (spos_leaf c hbc _),
        F_ll c _ _ (spos_leaf c hbc _) (spos_leaf c hbc _),
        adjM_eq (some ⟨b, ⟨0, hj⟩⟩) (some ⟨b, ⟨0, hj'⟩⟩) False (by simp [starAdj])]
      simp [LL]
    · obtain rfl : j = 0 := by omega
      rw [F_ls c _ _ (spos_leaf c hbc _) (spos_c c _), F_ls c _ _ (spos_leaf c hbc _) (spos_c c _),
        adjM_eq (some ⟨b, ⟨0, hj⟩⟩) (some ⟨c, ⟨j', hj'⟩⟩) False (by simp [starAdj, hbc])]
      unfold V; simp only [hsome, hbc, false_and, if_false]; constructor <;> split_ifs <;> omega
    · obtain rfl : j' = 0 := by omega
      rw [F_sl c _ _ (spos_c c _) (spos_leaf c hac _), F_sl c _ _ (spos_c c _) (spos_leaf c hac _),
        adjM_eq (some ⟨c, ⟨j, hj⟩⟩) (some ⟨a, ⟨0, hj'⟩⟩) False (by simp [starAdj, hca])]
      unfold V; simp only [hsome, hca, false_and, if_false]; constructor <;> split_ifs <;> omega
    · obtain rfl : j' = 0 := by omega
      rw [F_sl c _ _ (spos_c c _) (spos_leaf c hbc _), F_sl c _ _ (spos_c c _) (spos_leaf c hbc _),
        adjM_eq (some ⟨c, ⟨j, hj⟩⟩) (some ⟨b, ⟨0, hj'⟩⟩) False (by simp [starAdj, hcb])]
      unfold V; simp only [hsome, hcb, false_and, if_false]; constructor <;> split_ifs <;> omega
    · rw [F_ss c _ _ (spos_c c _) (spos_c c _), F_ss c _ _ (spos_c c _) (spos_c c _),
        adjM_eq (some ⟨c, ⟨j, hj⟩⟩) (some ⟨c, ⟨j', hj'⟩⟩) (j' = j + 1 ∨ j = j' + 1)
          (by simp [starAdj])]
      unfold V; simp only [hsome, true_and]; constructor <;> split_ifs <;> omega

include hab hac hbc hLa hLb in
/-- **The closed form is the recurrence matrix** in degrees up to `2N`. -/
theorem U_eq_F : ∀ d, d ≤ 2 * (L c + 2) → ∀ x y : (starTree L).Dbl,
    UBound.U (starTree L).adjM d x y = F c (L c + 2) d x y := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd x y
    match d, ih, hd with
    | 0, _, _ =>
        rw [UBound.U, Matrix.one_apply, (F_init hab hac hbc hLa hLb x y).1]
        congr
    | 1, _, _ => rw [UBound.U, (F_init hab hac hbc hLa hLb x y).2]
    | d + 2, ih, hd =>
        rw [UBound.U, Matrix.sub_apply, Matrix.mul_apply]
        refine Eq.trans ?_ (F_rec hab hac hbc hLa hLb d hd x y).symm
        congr 1
        · refine Eq.trans ?_ (sum_adjM x _)
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          rw [ih (d + 1) (by omega) (by omega)]
        · exact ih d (by omega) (by omega) x y

include hab hac hbc hLa hLb in
/-- **Lemma B.1 for `N` even**: every vertex of `Π(D_n)`, `n = N + 2`, carries a closed
path of degree `2N` outside the ideal, over every field. -/
theorem d_return (hN : Even (L c)) {k : Type*} [Field k] (v : (starTree L).Dbl) :
    ∃ p : Quiver.Path v v, p.length = 2 * (L c + 2) ∧
      LinearPaths.path (k := k) p ∉ (starTree L).Id k v v := by
  classical
  have hU : ∀ d ≤ 2 * (L c + 2), ∀ x y : (starTree L).Dbl, 0 ≤ UBound.U (starTree L).adjM d x y := by
    intro d hd x y
    rw [U_eq_F hab hac hbc hLa hLb d hd]
    exact F_nonneg _ _ _ _ _
  have hdiag : UBound.U (starTree L).adjM (2 * (L c + 2)) v v = 1 := by
    rw [U_eq_F hab hac hbc hLa hLb _ le_rfl]
    obtain ⟨e, he⟩ := hN
    rcases (v : StarV L) with _ | ⟨i, ⟨j, hj⟩⟩
    · rw [F_ss c _ _ (spos_none c) (spos_none c)]
      unfold V; split_ifs <;> omega
    · by_cases hi : i = c
      · subst hi
        rw [F_ss i _ _ (spos_c i _) (spos_c i _)]
        unfold V; split_ifs <;> omega
      · rw [F_ll c _ _ (spos_leaf c hi _) (spos_leaf c hi _)]
        unfold LL
        simp only [true_iff]
        split_ifs <;> omega
  have := OrientedTree.U_le_finrank (T := starTree L) (k := k) v (2 * (L c + 2)) hU v
  rw [hdiag] at this
  exact OrientedTree.exists_path_of_finrank (by exact_mod_cast this)

/-- **The short-arm interchange** `ν`: it swaps the leaves of the short arms `a, b` and fixes
the other vertices. -/
def nu (a b : Fin 3) : StarV L → StarV L
  | none => none
  | some x => if x.1 = a then some ⟨b, ⟨0, Nat.succ_pos _⟩⟩
      else if x.1 = b then some ⟨a, ⟨0, Nat.succ_pos _⟩⟩ else some x

/-- `ν` on the vertices of the doubled quiver. -/
def nuD (a b : Fin 3) (v : (starTree L).Dbl) : (starTree L).Dbl := nu (L := L) a b v

include hab hac hbc hLa hLb in
/-- **Lemma B.1 for `N` odd**: every vertex `x` of `Π(D_n)`, `n = N + 2`, carries a path of
degree `2N` from `x` to `ν x` outside the ideal, over every field. -/
theorem d_return_odd (hN : Odd (L c)) {k : Type*} [Field k] (v : (starTree L).Dbl) :
    ∃ p : Quiver.Path v (nuD a b v), p.length = 2 * (L c + 2) ∧
      LinearPaths.path (k := k) p ∉ (starTree L).Id k v (nuD a b v) := by
  classical
  have hU : ∀ d ≤ 2 * (L c + 2), ∀ x y : (starTree L).Dbl, 0 ≤ UBound.U (starTree L).adjM d x y := by
    intro d hd x y
    rw [U_eq_F hab hac hbc hLa hLb d hd]
    exact F_nonneg _ _ _ _ _
  have hdiag : UBound.U (starTree L).adjM (2 * (L c + 2)) v (nuD a b v) = 1 := by
    rw [U_eq_F hab hac hbc hLa hLb _ le_rfl]
    obtain ⟨e, he⟩ := hN
    change F c (L c + 2) (2 * (L c + 2)) (v : StarV L) (nu a b (v : StarV L)) = 1
    generalize (v : StarV L) = x
    rcases x with _ | ⟨i, ⟨j, hj⟩⟩
    · change F c _ _ (none : StarV L) none = 1
      rw [F_ss c _ _ (spos_none c) (spos_none c)]
      unfold V; split_ifs <;> omega
    · by_cases hi : i = c
      · subst hi
        have hn : nu a b (some ⟨i, ⟨j, hj⟩⟩ : StarV L) = some ⟨i, ⟨j, hj⟩⟩ := by
          simp [nu, Ne.symm hac, Ne.symm hbc]
        rw [hn, F_ss i _ _ (spos_c i _) (spos_c i _)]
        unfold V; split_ifs <;> omega
      · have hab' : i = a ∨ i = b := by
          have key : ∀ i a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → i ≠ c → i = a ∨ i = b := by decide
          exact key i a b c hab hac hbc hi
        rcases hab' with rfl | rfl
        · have hn : nu i b (some ⟨i, ⟨j, hj⟩⟩ : StarV L) = some ⟨b, ⟨0, Nat.succ_pos _⟩⟩ := by
            simp [nu]
          rw [hn, F_ll c _ _ (spos_leaf c hi _) (spos_leaf c hbc _)]
          unfold LL
          have hne : ¬ ((some ⟨i, ⟨j, hj⟩⟩ : StarV L) = some ⟨b, ⟨0, Nat.succ_pos _⟩⟩) := by
            intro h; simp only [Option.some.injEq, Sigma.mk.injEq] at h; exact hab h.1
          simp only [hne, false_iff]
          split_ifs <;> omega
        · have hn : nu a i (some ⟨i, ⟨j, hj⟩⟩ : StarV L) = some ⟨a, ⟨0, Nat.succ_pos _⟩⟩ := by
            simp [nu, Ne.symm hab]
          rw [hn, F_ll c _ _ (spos_leaf c hi _) (spos_leaf c hac _)]
          unfold LL
          have hne : ¬ ((some ⟨i, ⟨j, hj⟩⟩ : StarV L) = some ⟨a, ⟨0, Nat.succ_pos _⟩⟩) := by
            intro h; simp only [Option.some.injEq, Sigma.mk.injEq] at h; exact hab h.1.symm
          simp only [hne, false_iff]
          split_ifs <;> omega
  have := OrientedTree.U_le_finrank (T := starTree L) (k := k) (nuD a b v)
    (2 * (L c + 2)) hU v
  rw [hdiag] at this
  exact OrientedTree.exists_path_of_finrank (by exact_mod_cast this)

include hab hac hbc hLa hLb in
/-- **Lemma B.1** (`lem:d-top-paths`): at every vertex `x` of `Π(D_n)`, `N = n − 2`, there is
a path of degree `2N` from `x` to `ν x` outside the ideal, where `ν` is the identity for `N`
even and the short-arm interchange for `N` odd; over every field. -/
theorem dTopPaths {k : Type*} [Field k] (v : (starTree L).Dbl) :
    ∃ w : (starTree L).Dbl, w = (if Even (L c) then v else nuD a b v) ∧
      ∃ p : Quiver.Path v w, p.length = 2 * (L c + 2) ∧
        LinearPaths.path (k := k) p ∉ (starTree L).Id k v w := by
  by_cases hN : Even (L c)
  · exact ⟨v, by rw [if_pos hN], d_return hab hac hbc hLa hLb hN v⟩
  · exact ⟨nuD a b v, by rw [if_neg hN],
      d_return_odd hab hac hbc hLa hLb (Nat.not_even_iff_odd.1 hN) v⟩

end DTop

end MultiplicativeBasisDeformations
