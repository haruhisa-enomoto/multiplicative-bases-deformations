module

public import Mathlib

/-!
# The bar cochain complex

The normalized relative bar complexes of Section 6 (`positive-deformations.tex`,
module bar complex) and Section 7 (Hochschild complex) are both cochains
`f(a_1, …, a_n)` with values in a bimodule `X` and differential
`df(a_1, …, a_{n+1}) = a_1 f(a_2, …) + Σ (-1)^i f(…, a_i a_{i+1}, …)
 + (-1)^{n+1} f(a_1, …, a_n) a_{n+1}`.
For a right module bar complex `Hom(M ⊗ Λ̄^{⊗n}, N)` take `X = Hom_k(M, N)` with
`(a·φ)(m) = φ(ma)`, `(φ·b)(m) = φ(m)b`.

Cochains are encoded as functions of sequences `ℕ → Λ` (only the first `n`
entries matter for the cochains used later); the coface maps then satisfy the
cosimplicial identities as identities of sequence operations (`coface_comm`),
and `d ∘ d = 0` (`d_d`) follows by the usual pairing of terms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace Bar

variable {Λ : Type*} [Ring Λ] {X : Type*} [AddCommGroup X]

variable (Λ X) in
/-- Bimodule actions on `X`: `l a x = a·x`, `r b x = x·b`. -/
structure Act where
  l : Λ → X →+ X
  r : Λ → X →+ X
  l_mul : ∀ a b x, l (a * b) x = l a (l b x)
  r_mul : ∀ a b x, r b (r a x) = r (a * b) x
  lr : ∀ a b x, l a (r b x) = r b (l a x)

/-- Shift a sequence. -/
def sh (a : ℕ → Λ) : ℕ → Λ := fun k ↦ a (k + 1)

/-- Multiply the entries `p, p+1`. -/
def ct (p : ℕ) (a : ℕ → Λ) : ℕ → Λ := fun k ↦
  if k < p then a k else if k = p then a p * a (p + 1) else a (k + 1)

/-- Truncate after `n` entries. -/
def tr (n : ℕ) (a : ℕ → Λ) : ℕ → Λ := fun k ↦ if k < n then a k else 0

theorem sh_ct_zero (a : ℕ → Λ) : sh (ct 0 a) = sh (sh a) := by
  funext k; simp [sh, ct]

theorem sh_ct {j : ℕ} (hj : 1 ≤ j) (a : ℕ → Λ) : sh (ct j a) = ct (j - 1) (sh a) := by
  funext k
  simp only [sh, ct]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> congr 1 <;> omega)

theorem ct_zero_apply {j : ℕ} (hj : 1 ≤ j) (a : ℕ → Λ) : ct j a 0 = a 0 := by
  simp [ct, show 0 < j by omega]

theorem sh_tr (n : ℕ) (a : ℕ → Λ) : sh (tr (n + 1) a) = tr n (sh a) := by
  funext k; simp [sh, tr]

theorem ct_ct {p j : ℕ} (h : p < j) (a : ℕ → Λ) : ct p (ct j a) = ct (j - 1) (ct p a) := by
  funext k
  simp only [ct]
  split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem ct_tr {p n : ℕ} (h : p < n) (a : ℕ → Λ) : ct p (tr (n + 1) a) = tr n (ct p a) := by
  funext k
  simp only [ct, tr]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem tr_tr (n : ℕ) (a : ℕ → Λ) : tr n (tr (n + 1) a) = tr n a := by
  funext k; simp only [tr]; split_ifs <;> first | rfl | (exfalso; omega)

theorem tr_ct (n : ℕ) (a : ℕ → Λ) : tr n (ct n a) = tr n a := by
  funext k; simp only [tr, ct]; split_ifs <;> first | rfl | (exfalso; omega)

theorem ct_apply_of_lt {p n : ℕ} (h : p < n) (a : ℕ → Λ) : ct p a n = a (n + 1) := by
  simp [ct, show ¬ n < p by omega, show n ≠ p by omega]

theorem ct_apply_self (n : ℕ) (a : ℕ → Λ) : ct n a n = a n * a (n + 1) := by
  simp [ct]

theorem tr_apply_lt {n k : ℕ} (h : k < n) (a : ℕ → Λ) : tr n a k = a k := by simp [tr, h]

/-! ### Sequence operations and updates -/

theorem sh_update_succ (a : ℕ → Λ) (i : ℕ) (x : Λ) :
    sh (Function.update a (i + 1) x) = Function.update (sh a) i x := by
  funext k; simp only [sh, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)

theorem sh_update_zero (a : ℕ → Λ) (x : Λ) : sh (Function.update a 0 x) = sh a := by
  funext k; simp [sh, Function.update_apply]

theorem ct_update_lt {p i : ℕ} (h : i < p) (a : ℕ → Λ) (x : Λ) :
    ct p (Function.update a i x) = Function.update (ct p a) i x := by
  funext k; simp only [ct, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem ct_update_gt {p i : ℕ} (h : p + 1 < i) (a : ℕ → Λ) (x : Λ) :
    ct p (Function.update a i x) = Function.update (ct p a) (i - 1) x := by
  funext k; simp only [ct, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem ct_update_left (p : ℕ) (a : ℕ → Λ) (x : Λ) :
    ct p (Function.update a p x) = Function.update (ct p a) p (x * a (p + 1)) := by
  funext k; simp only [ct, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem ct_update_right (p : ℕ) (a : ℕ → Λ) (x : Λ) :
    ct p (Function.update a (p + 1) x) = Function.update (ct p a) p (a p * x) := by
  funext k; simp only [ct, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem tr_update_lt {n i : ℕ} (h : i < n) (a : ℕ → Λ) (x : Λ) :
    tr n (Function.update a i x) = Function.update (tr n a) i x := by
  funext k; simp only [tr, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem tr_update_ge {n i : ℕ} (h : n ≤ i) (a : ℕ → Λ) (x : Λ) :
    tr n (Function.update a i x) = tr n a := by
  funext k; simp only [tr, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)

/-- Prepend an entry. -/
def cons (x : Λ) (a : ℕ → Λ) : ℕ → Λ := fun k ↦ if k = 0 then x else a (k - 1)

theorem cons_zero (x : Λ) (a : ℕ → Λ) : cons x a 0 = x := by simp [cons]

theorem sh_cons (x : Λ) (a : ℕ → Λ) : sh (cons x a) = a := by funext k; simp [sh, cons]

theorem ct_zero_cons (x : Λ) (a : ℕ → Λ) : ct 0 (cons x a) = cons (x * a 0) (sh a) := by
  funext k; simp only [ct, cons, sh]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem ct_succ_cons (p : ℕ) (x : Λ) (a : ℕ → Λ) : ct (p + 1) (cons x a) = cons x (ct p a) := by
  funext k; simp only [ct, cons]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem tr_cons (n : ℕ) (x : Λ) (a : ℕ → Λ) : tr (n + 1) (cons x a) = cons x (tr n a) := by
  funext k; simp only [tr, cons]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem cons_succ (x : Λ) (a : ℕ → Λ) (k : ℕ) : cons x a (k + 1) = a k := by simp [cons]

theorem update_cons_succ (x : Λ) (a : ℕ → Λ) (i : ℕ) (y : Λ) :
    Function.update (cons x a) (i + 1) y = cons x (Function.update a i y) := by
  funext k; simp only [cons, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | grind

theorem update_cons_zero (x : Λ) (a : ℕ → Λ) (y : Λ) :
    Function.update (cons x a) 0 y = cons y a := by
  funext k; simp only [cons, Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)

variable (Λ X) in
/-- Cochains: functions of sequences. -/
abbrev Cochain := (ℕ → Λ) → X

/-- The coface maps `δ_i : Cⁿ → Cⁿ⁺¹`. -/
def coface (A : Act Λ X) (n i : ℕ) : Cochain Λ X →+ Cochain Λ X where
  toFun F a := if i = 0 then A.l (a 0) (F (sh a))
    else if i ≤ n then F (ct (i - 1) a) else A.r (a n) (F (tr n a))
  map_zero' := by funext a; simp
  map_add' F G := by funext a; simp only [Pi.add_apply]; split_ifs <;> simp

theorem coface_zero (A : Act Λ X) (n : ℕ) (F : Cochain Λ X) (a : ℕ → Λ) :
    coface A n 0 F a = A.l (a 0) (F (sh a)) := by simp [coface]

theorem coface_mid (A : Act Λ X) {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) (F : Cochain Λ X)
    (a : ℕ → Λ) : coface A n i F a = F (ct (i - 1) a) := by
  simp [coface, show i ≠ 0 by omega, h2]

theorem coface_last (A : Act Λ X) (n : ℕ) (F : Cochain Λ X) (a : ℕ → Λ) :
    coface A n (n + 1) F a = A.r (a n) (F (tr n a)) := by
  simp [coface]

/-- **The cosimplicial identities** `δ_{j+1} δ_i = δ_i δ_j` for `i ≤ j`. -/
theorem coface_comm (A : Act Λ X) {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ n + 1) (F : Cochain Λ X) :
    coface A (n + 1) (j + 1) (coface A n i F) = coface A (n + 1) i (coface A n j F) := by
  funext a
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [coface_mid A (by omega) (by omega), coface_zero, coface_zero, coface_zero,
        sh_ct_zero, ← A.l_mul]
      simp [ct, sh]
    · rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
      · rw [coface_mid A (by omega) (by omega), coface_zero, coface_zero,
          coface_mid A (by omega) (by omega), ct_zero_apply (by omega), sh_ct (by omega),
          show j + 1 - 1 - 1 = j - 1 by omega]
      · obtain rfl : j = n + 1 := by omega
        rw [coface_last, coface_zero, coface_zero, coface_last, sh_tr]
        simp only [tr, show (0 : ℕ) < n + 1 from Nat.succ_pos n, if_true, sh]
        rw [A.lr]
  · rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · rw [coface_mid A (by omega) (by omega), coface_mid A (by omega) (by omega),
        coface_mid A (by omega) (by omega), coface_mid A (by omega) (by omega)]
      rw [ct_ct (by omega), show j + 1 - 1 - 1 = j - 1 by omega]
    · obtain rfl : j = n + 1 := by omega
      rcases Nat.lt_or_ge i (n + 1) with hin | hin
      · rw [coface_last, coface_mid A (by omega) (by omega), coface_mid A (by omega) (by omega),
          coface_last, ct_tr (by omega), ct_apply_of_lt (by omega)]
      · obtain rfl : i = n + 1 := by omega
        rw [coface_last, coface_last, coface_mid A (by omega) (by omega), coface_last,
          tr_apply_lt (by omega), A.r_mul, tr_tr]
        simp only [show n + 1 - 1 = n by omega, ct_apply_self, tr_ct]

/-- The differential `d = Σ (-1)^i δ_i`. -/
def d (A : Act Λ X) (n : ℕ) : Cochain Λ X →+ Cochain Λ X :=
  ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i • coface A n i

theorem d_apply (A : Act Λ X) (n : ℕ) (F : Cochain Λ X) :
    d A n F = ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i • coface A n i F := by
  simp [d, AddMonoidHom.finsetSum_apply]

/-- **`d ∘ d = 0`.** -/
theorem d_d (A : Act Λ X) (n : ℕ) (F : Cochain Λ X) : d A (n + 1) (d A n F) = 0 := by
  rw [d_apply, d_apply]
  simp only [map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  -- split the inner sum at `j = i + 1`
  have hsplit : ∀ i ∈ Finset.range (n + 2),
      ∑ j ∈ Finset.range (n + 1 + 2), ((-1 : ℤ) ^ j * (-1) ^ i) •
        coface A (n + 1) j (coface A n i F) =
      ∑ j ∈ Finset.range (i + 1), ((-1 : ℤ) ^ j * (-1) ^ i) • coface A (n + 1) j (coface A n i F) +
      ∑ j ∈ Finset.Ico i (n + 2), ((-1 : ℤ) ^ (j + 1) * (-1) ^ i) •
        coface A (n + 1) (j + 1) (coface A n i F) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ n + 1 + 2 by omega)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun j _ ↦ ?_
    rw [show i + 1 + j = i + j + 1 by omega]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the second double sum is minus the first after the cosimplicial identities
  have hsecond : ∑ i ∈ Finset.range (n + 2), ∑ j ∈ Finset.Ico i (n + 2),
      ((-1 : ℤ) ^ (j + 1) * (-1) ^ i) • coface A (n + 1) (j + 1) (coface A n i F) =
      -∑ j ∈ Finset.range (n + 2), ∑ i ∈ Finset.range (j + 1),
        ((-1 : ℤ) ^ i * (-1) ^ j) • coface A (n + 1) i (coface A n j F) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← Finset.sum_neg_distrib, show Finset.Ico 0 (j + 1) = Finset.range (j + 1) from
      (Finset.range_eq_Ico (j + 1)).symm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hj' := (Finset.mem_Ico.1 hj).2
    have hi' := Finset.mem_range.1 hi
    rw [coface_comm A (by omega) (by omega), ← neg_smul]
    congr 1
    rw [pow_succ]; ring
  rw [hsecond, add_neg_eq_zero]

/-! ### Low degrees -/

theorem d_zero_apply (A : Act Λ X) (F : Cochain Λ X) (a : ℕ → Λ) :
    d A 0 F a = A.l (a 0) (F (sh a)) - A.r (a 0) (F (tr 0 a)) := by
  rw [d_apply]
  simp only [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Pi.smul_apply, pow_zero, one_smul, pow_one, neg_smul, coface_zero]
  rw [show (1 : ℕ) = 0 + 1 from rfl, coface_last, sub_eq_add_neg]

theorem d_one_apply (A : Act Λ X) (F : Cochain Λ X) (a : ℕ → Λ) :
    d A 1 F a = A.l (a 0) (F (sh a)) - F (ct 0 a) + A.r (a 1) (F (tr 1 a)) := by
  rw [d_apply]
  simp only [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Pi.smul_apply, pow_zero, one_smul, pow_one, neg_smul, coface_zero]
  rw [coface_mid A (le_refl 1) (le_refl 1), coface_last]
  simp only [Nat.sub_self, show (-1 : ℤ) ^ (1 + 1) = 1 by norm_num, one_smul]
  abel

theorem d_two_apply (A : Act Λ X) (F : Cochain Λ X) (a : ℕ → Λ) :
    d A 2 F a = A.l (a 0) (F (sh a)) - F (ct 0 a) + F (ct 1 a) - A.r (a 2) (F (tr 2 a)) := by
  rw [d_apply]
  simp only [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Pi.smul_apply, pow_zero, one_smul, pow_one, neg_smul, coface_zero]
  rw [coface_mid A (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 2),
    coface_mid A (by norm_num : 1 ≤ 2) (le_refl 2), coface_last]
  simp only [show (-1 : ℤ) ^ 2 = 1 by norm_num, show (-1 : ℤ) ^ (2 + 1) = -1 by norm_num,
    one_smul, neg_smul, Nat.sub_self, show 2 - 1 = 1 from rfl]
  abel

end Bar

end MultiplicativeBasisDeformations
