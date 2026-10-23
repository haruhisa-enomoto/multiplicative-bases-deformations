module

public import MultiplicativeBasisDeformations.Foundations.TableConf

/-!
# Setting 8.4: local generators and endpoint chains of a ray table

`set:projective-companion`: `A₀ = kP` with its normed homogeneous ray basis; each local ring
is `R_x = k[q_x]/(q_x^{N_x})` with `q_x` a ray (or `q_x = 0` when `R_x = k`), and by
Lemma 3.1(3) the endpoint subbimodules of each Hom form a chain, each generated over one
endpoint ring (`lem:endpoint-chains`). In ray terms:

* `q x` is `0` or a nonidentity loop at `x`, and every loop at `x` is `q x ^ j e_x`;
* for each ray `r`, every ray `q^i r q^j` equals `q^i' r` for all such, or `r q^j'` for all
  such (one-sided generation);
* the rays of each Hom form a chain under `s ∈ U(r)`.

`Sys` bundles a ray table with this structure. Products are computed in the monoid with zero
`M P`; we write `⌜r⌝` for a ray in it.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace RaySys

/-- **Setting 8.4** for a ray table. -/
structure Sys (V R L : Type) [AddCommGroup L] where
  P : Tab V R L
  q : V → M P.toMult
  q_cases : ∀ x, q x = 0 ∨ ∃ g, q x = P.rr g ∧ P.src g = x ∧ P.tgt g = x ∧ g ≠ P.e x
  q_pow : ∀ r, P.src r = P.tgt r → ∃ j : ℕ, q (P.src r) ^ j * P.rr (P.e (P.src r)) = P.rr r
  cyc : ∀ r, (∀ i j : ℕ, q (P.src r) ^ i * P.rr r * q (P.tgt r) ^ j ≠ 0 →
      ∃ i' : ℕ, q (P.src r) ^ i * P.rr r * q (P.tgt r) ^ j = q (P.src r) ^ i' * P.rr r) ∨
    (∀ i j : ℕ, q (P.src r) ^ i * P.rr r * q (P.tgt r) ^ j ≠ 0 →
      ∃ j' : ℕ, q (P.src r) ^ i * P.rr r * q (P.tgt r) ^ j = P.rr r * q (P.tgt r) ^ j')
  chain : ∀ r s, P.src r = P.src s → P.tgt r = P.tgt s →
    (∃ i j : ℕ, P.rr r = q (P.src r) ^ i * P.rr s * q (P.tgt r) ^ j) ∨
      (∃ i j : ℕ, P.rr s = q (P.src r) ^ i * P.rr r * q (P.tgt r) ^ j)

namespace Sys

variable {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  (S : Sys V R L)

/-- A ray as an element of the monoid with zero. -/
abbrev rr (r : R) : M S.P.toMult := S.P.rr r

local notation:max "⌜" r "⌝" => Sys.rr S r

/-! ### Elements of the monoid with zero -/

/-- The weight of an element (zero on `0` and `1`). -/
def wtM : M S.P.toMult → L
  | Elt.one => 0
  | Elt.zero => 0
  | Elt.ray r => S.P.wt r

theorem wtM_rr (r : R) : S.wtM ⌜r⌝ = S.P.wt r := rfl

theorem wtM_one : S.wtM 1 = 0 := rfl

theorem rr_mul_rr_cases (r s : R) : ⌜r⌝ * ⌜s⌝ = 0 ∨ ∃ t, ⌜r⌝ * ⌜s⌝ = ⌜t⌝ := by
  by_cases h : ⌜r⌝ * ⌜s⌝ = 0
  · exact Or.inl h
  · obtain ⟨t, -, ht⟩ := S.P.rr_mul_rr_ne_zero h
    exact Or.inr ⟨t, ht⟩

theorem rr_ne (r : R) : ⌜r⌝ ≠ 0 := S.P.rr_ne_zero r

theorem rr_inj {r s : R} (h : ⌜r⌝ = ⌜s⌝) : r = s := S.P.rr_injective h

theorem ray_of_mul_ne {r s : R} (h : ⌜r⌝ * ⌜s⌝ ≠ 0) : ∃ t, ⌜r⌝ * ⌜s⌝ = ⌜t⌝ :=
  (S.rr_mul_rr_cases r s).resolve_left h

theorem mul_left_ray {r : R} {a : M S.P.toMult} (h : ⌜r⌝ * a ≠ 0) : ∃ t, ⌜r⌝ * a = ⌜t⌝ := by
  rcases S.P.cases_elt a with rfl | rfl | ⟨s, rfl⟩
  · exact ⟨r, mul_one _⟩
  · exact absurd (mul_zero _) h
  · exact S.ray_of_mul_ne h

theorem mul_right_ray {r : R} {a : M S.P.toMult} (h : a * ⌜r⌝ ≠ 0) : ∃ t, a * ⌜r⌝ = ⌜t⌝ := by
  rcases S.P.cases_elt a with rfl | rfl | ⟨s, rfl⟩
  · exact ⟨r, one_mul _⟩
  · exact absurd (zero_mul _) h
  · exact S.ray_of_mul_ne h

theorem elt_cases (a : M S.P.toMult) : a = 1 ∨ a = 0 ∨ ∃ r, a = ⌜r⌝ := S.P.cases_elt a

theorem e_mul_rr (r : R) : ⌜S.P.e (S.P.src r)⌝ * ⌜r⌝ = ⌜r⌝ := S.P.e_mul_rr r

theorem rr_mul_e (r : R) : ⌜r⌝ * ⌜S.P.e (S.P.tgt r)⌝ = ⌜r⌝ := S.P.rr_mul_e r

theorem e_mul_rr' (r : R) {x : V} (h : S.P.src r = x) : ⌜S.P.e x⌝ * ⌜r⌝ = ⌜r⌝ := by
  rw [← h]; exact S.e_mul_rr r

theorem e_mul_rr_of_ne {x : V} {r : R} (h : x ≠ S.P.src r) : ⌜S.P.e x⌝ * ⌜r⌝ = 0 :=
  S.P.rr_mul_rr_eq_zero_of_ne (by rwa [S.P.tgt_e])

theorem rr_mul_e_of_ne {x : V} {r : R} (h : x ≠ S.P.tgt r) : ⌜r⌝ * ⌜S.P.e x⌝ = 0 :=
  S.P.rr_mul_rr_eq_zero_of_ne (by rw [S.P.src_e]; exact Ne.symm h)

/-- A nonzero product of rays: endpoints and weight. -/
theorem prod_of {r s t : R} (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) :
    S.P.src t = S.P.src r ∧ S.P.tgt t = S.P.tgt s ∧ S.P.tgt r = S.P.src s ∧
      S.P.wt t = S.P.wt r + S.P.wt s :=
  ⟨(S.P.mul_eq_rr_of h).1, (S.P.mul_eq_rr_of h).2.1, (S.P.mul_eq_rr_of h).2.2, S.P.wt_of_mul h⟩

/-- **Left cancellation of nonzero products.** -/
theorem cancel_left {r s s' : R} (h : ⌜r⌝ * ⌜s⌝ = ⌜r⌝ * ⌜s'⌝) (h0 : ⌜r⌝ * ⌜s⌝ ≠ 0) : s = s' := by
  obtain ⟨t, -, ht⟩ := S.P.rr_mul_rr_ne_zero h0
  have ht' : ⌜r⌝ * ⌜s'⌝ = ⌜t⌝ := h ▸ ht
  obtain ⟨-, e2, e3, e4⟩ := S.prod_of ht
  obtain ⟨-, e2', e3', e4'⟩ := S.prod_of ht'
  exact S.P.sep _ _ (by rw [← e3, ← e3']) (by rw [← e2, ← e2']) (by rw [e4] at e4'; exact
    (add_left_cancel e4'.symm).symm ▸ rfl)

/-- **Right cancellation of nonzero products.** -/
theorem cancel_right {r r' s : R} (h : ⌜r⌝ * ⌜s⌝ = ⌜r'⌝ * ⌜s⌝) (h0 : ⌜r⌝ * ⌜s⌝ ≠ 0) : r = r' := by
  obtain ⟨t, -, ht⟩ := S.P.rr_mul_rr_ne_zero h0
  have ht' : ⌜r'⌝ * ⌜s⌝ = ⌜t⌝ := h ▸ ht
  obtain ⟨e1, -, e3, e4⟩ := S.prod_of ht
  obtain ⟨e1', -, e3', e4'⟩ := S.prod_of ht'
  exact S.P.sep _ _ (by rw [← e1, ← e1']) (by rw [e3, e3']) (by rw [e4] at e4'; exact
    (add_right_cancel e4'.symm).symm ▸ rfl)

/-! ### Local generators -/

/-- The weight of the local generator (`0` when `R_x = k`). -/
def χ (x : V) : L := S.wtM (S.q x)

theorem q_mul_e (x : V) : S.q x * ⌜S.P.e x⌝ = S.q x := by
  rcases S.q_cases x with h | ⟨g, hg, h1, h2, -⟩
  · rw [h, zero_mul]
  · rw [hg, ← h2]; exact S.rr_mul_e g

theorem e_mul_q (x : V) : ⌜S.P.e x⌝ * S.q x = S.q x := by
  rcases S.q_cases x with h | ⟨g, hg, h1, h2, -⟩
  · rw [h, mul_zero]
  · rw [hg, ← h1]; exact S.e_mul_rr g

theorem e_mul_qpow (x : V) (j : ℕ) : ⌜S.P.e x⌝ * S.q x ^ j * ⌜S.P.e x⌝ = S.q x ^ j * ⌜S.P.e x⌝ := by
  induction j with
  | zero =>
    simp only [pow_zero, mul_one, one_mul]
    have := S.e_mul_rr (S.P.e x); rwa [S.P.src_e] at this
  | succ n ih => rw [pow_succ', ← mul_assoc, S.e_mul_q, mul_assoc]

theorem qpow_comm_e (x : V) (j : ℕ) : S.q x ^ j * ⌜S.P.e x⌝ = ⌜S.P.e x⌝ * S.q x ^ j :=
  (Commute.pow_left (show Commute (S.q x) ⌜S.P.e x⌝ from (S.q_mul_e x).trans (S.e_mul_q x).symm)
    j).eq

/-- **Powers of the local generator** are zero or loops of weight `j χ_x`. -/
theorem qpow_cases (x : V) (j : ℕ) : S.q x ^ j * ⌜S.P.e x⌝ = 0 ∨ ∃ g, S.q x ^ j * ⌜S.P.e x⌝ = ⌜g⌝ ∧
    S.P.src g = x ∧ S.P.tgt g = x ∧ S.P.wt g = j • S.χ x := by
  induction j with
  | zero =>
    right
    exact ⟨S.P.e x, by simp, S.P.src_e x, S.P.tgt_e x, by rw [S.P.wt_e, zero_smul]⟩
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    rcases ih with h | ⟨g, hg, h1, h2, h3⟩
    · left; rw [h, mul_zero]
    · rw [hg]
      rcases S.q_cases x with hq | ⟨g', hg', h1', h2', -⟩
      · left; rw [hq, zero_mul]
      · rw [hg']
        rcases S.rr_mul_rr_cases g' g with h0 | ⟨t, ht⟩
        · left; exact h0
        · right
          obtain ⟨e1, e2, -, e4⟩ := S.prod_of ht
          refine ⟨t, ht, by rw [e1, h1'], by rw [e2, h2], ?_⟩
          rw [e4, h3, succ_nsmul', χ, hg', wtM_rr]

/-- The weight of a nonzero product of a ray with powers of the local generators. -/
theorem qpow_mul_rr_mul_qpow (r : R) (i j : ℕ) :
    S.q (S.P.src r) ^ i * ⌜r⌝ * S.q (S.P.tgt r) ^ j = 0 ∨
      ∃ t, S.q (S.P.src r) ^ i * ⌜r⌝ * S.q (S.P.tgt r) ^ j = ⌜t⌝ ∧ S.P.src t = S.P.src r ∧
        S.P.tgt t = S.P.tgt r ∧ S.P.wt t = i • S.χ (S.P.src r) + S.P.wt r + j • S.χ (S.P.tgt r) := by
  have hl : S.q (S.P.src r) ^ i * ⌜r⌝ = (S.q (S.P.src r) ^ i * ⌜S.P.e (S.P.src r)⌝) * ⌜r⌝ := by
    rw [mul_assoc, S.e_mul_rr]
  have hr : ⌜r⌝ * S.q (S.P.tgt r) ^ j = ⌜r⌝ * (S.q (S.P.tgt r) ^ j * ⌜S.P.e (S.P.tgt r)⌝) := by
    rw [S.qpow_comm_e, ← mul_assoc, S.rr_mul_e]
  have e1 : S.q (S.P.src r) ^ i * ⌜r⌝ * S.q (S.P.tgt r) ^ j =
      (S.q (S.P.src r) ^ i * ⌜S.P.e (S.P.src r)⌝) * ⌜r⌝ *
        (S.q (S.P.tgt r) ^ j * ⌜S.P.e (S.P.tgt r)⌝) := by
    rw [mul_assoc, hr, ← mul_assoc, hl]
  rw [e1]
  rcases S.qpow_cases (S.P.src r) i with h | ⟨g, hg, g1, g2, g3⟩
  · left; rw [h, zero_mul, zero_mul]
  · rcases S.qpow_cases (S.P.tgt r) j with h' | ⟨g', hg', g1', g2', g3'⟩
    · left; rw [h', mul_zero]
    · rw [hg, hg']
      rcases S.rr_mul_rr_cases g r with h0 | ⟨t, ht⟩
      · left; rw [h0, zero_mul]
      · rw [ht]
        rcases S.rr_mul_rr_cases t g' with h0 | ⟨t', ht'⟩
        · left; exact h0
        · right
          obtain ⟨a1, a2, -, a4⟩ := S.prod_of ht
          obtain ⟨b1, b2, -, b4⟩ := S.prod_of ht'
          refine ⟨t', ht', by rw [b1, a1, g1], by rw [b2, g2'], ?_⟩
          rw [b4, a4, g3, g3']

/-- **Local rays are powers of the local generator.** -/
theorem local_eq (r : R) (h : S.P.src r = S.P.tgt r) :
    ∃ j : ℕ, S.q (S.P.src r) ^ j * ⌜S.P.e (S.P.src r)⌝ = ⌜r⌝ ∧ S.P.wt r = j • S.χ (S.P.src r) := by
  obtain ⟨j, hj⟩ := S.q_pow r h
  refine ⟨j, hj, ?_⟩
  rcases S.qpow_cases (S.P.src r) j with h0 | ⟨g, hg, -, -, hw⟩
  · rw [h0] at hj; exact absurd hj.symm (S.P.rr_ne_zero r)
  · rw [hg] at hj
    obtain rfl := S.P.rr_injective hj
    exact hw

theorem χ_deg_pos (x : V) (hq : S.q x ≠ 0) : 0 < S.P.deg (S.χ x) := by
  rcases S.q_cases x with h | ⟨g, hg, h1, -, h3⟩
  · exact absurd h hq
  · rw [χ, hg, wtM_rr]
    exact S.P.deg_pos g (by rw [h1]; exact h3)

theorem χ_eq_zero (x : V) (hq : S.q x = 0) : S.χ x = 0 := by
  rw [χ, hq]; rfl

/-! ### Endpoint subbimodules and generating rays -/

/-- `s ∈ U(r)`: `s = q^i r q^j`. -/
def InU (s r : R) : Prop :=
  ∃ i j : ℕ, ⌜s⌝ = S.q (S.P.src r) ^ i * ⌜r⌝ * S.q (S.P.tgt r) ^ j

/-- **Generating rays** (`def:generating-rays`(1)): every ray of the Hom lies in `U(r)`. -/
def IsGen (r : R) : Prop := ∀ s, S.P.src s = S.P.src r → S.P.tgt s = S.P.tgt r → S.InU s r

/-- The Hom of a ray is cyclic at its source, generated by it. -/
def CycL (f : R) : Prop :=
  ∀ s, S.P.src s = S.P.src f → S.P.tgt s = S.P.tgt f → ∃ i : ℕ, ⌜s⌝ = S.q (S.P.src f) ^ i * ⌜f⌝

/-- The Hom of a ray is cyclic at its target, generated by it. -/
def CycR (f : R) : Prop :=
  ∀ s, S.P.src s = S.P.src f → S.P.tgt s = S.P.tgt f → ∃ j : ℕ, ⌜s⌝ = ⌜f⌝ * S.q (S.P.tgt f) ^ j

theorem inU_endpoints {s r : R} (h : S.InU s r) : S.P.src s = S.P.src r ∧ S.P.tgt s = S.P.tgt r ∧
    ∃ i j : ℕ, S.P.wt s = i • S.χ (S.P.src r) + S.P.wt r + j • S.χ (S.P.tgt r) ∧
      (0 < i → S.q (S.P.src r) ≠ 0) ∧ (0 < j → S.q (S.P.tgt r) ≠ 0) := by
  obtain ⟨i, j, hs⟩ := h
  rcases S.qpow_mul_rr_mul_qpow r i j with h0 | ⟨t, ht, t1, t2, t3⟩
  · rw [h0] at hs; exact absurd hs (S.P.rr_ne_zero s)
  · rw [ht] at hs
    obtain rfl := S.P.rr_injective hs
    refine ⟨t1, t2, i, j, t3, fun hi hq ↦ ?_, fun hj hq ↦ ?_⟩
    · rw [hq, zero_pow hi.ne', zero_mul, zero_mul] at ht; exact S.P.rr_ne_zero _ ht.symm
    · rw [hq, zero_pow hj.ne', mul_zero] at ht; exact S.P.rr_ne_zero _ ht.symm

theorem nsmul_χ_deg (x : V) (i : ℕ) (h : 0 < i → S.q x ≠ 0) : 0 ≤ S.P.deg (i • S.χ x) ∧
    (S.P.deg (i • S.χ x) = 0 → i = 0) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have := S.χ_deg_pos x (h hi)
    rw [map_nsmul, nsmul_eq_mul]
    constructor
    · positivity
    · intro h0; exfalso; have : 0 < (i : ℤ) * S.P.deg (S.χ x) := by positivity
      omega

/-- Elements of `U(r)` have degree at least that of `r`, with equality only for `r`. -/
theorem deg_le_of_inU {s r : R} (h : S.InU s r) : S.P.deg (S.P.wt r) ≤ S.P.deg (S.P.wt s) ∧
    (S.P.deg (S.P.wt s) = S.P.deg (S.P.wt r) → s = r) := by
  obtain ⟨e1, e2, i, j, hw, hi, hj⟩ := S.inU_endpoints h
  have a := S.nsmul_χ_deg _ i hi
  have b := S.nsmul_χ_deg _ j hj
  have hd : S.P.deg (S.P.wt s) = S.P.deg (i • S.χ (S.P.src r)) + S.P.deg (S.P.wt r) +
      S.P.deg (j • S.χ (S.P.tgt r)) := by rw [hw, map_add, map_add]
  refine ⟨by omega, fun hd' ↦ ?_⟩
  have hi0 : i = 0 := a.2 (by omega)
  have hj0 : j = 0 := b.2 (by omega)
  subst hi0 hj0
  exact S.P.sep _ _ e1 e2 (by rw [hw]; simp)

theorem inU_refl (r : R) : S.InU r r := ⟨0, 0, by simp⟩

theorem inU_trans {s r t : R} (h1 : S.InU s r) (h2 : S.InU r t) : S.InU s t := by
  obtain ⟨e1, e2, -⟩ := S.inU_endpoints h2
  obtain ⟨i, j, hs⟩ := h1
  obtain ⟨i', j', hr⟩ := h2
  refine ⟨i + i', j' + j, ?_⟩
  rw [hs, e1, e2, hr, pow_add, pow_add]
  simp only [mul_assoc]

theorem inU_antisymm {s r : R} (h1 : S.InU s r) (h2 : S.InU r s) : s = r := by
  have a := S.deg_le_of_inU h1
  have b := S.deg_le_of_inU h2
  exact a.2 (le_antisymm b.1 a.1)

theorem inU_total {s r : R} (h1 : S.P.src s = S.P.src r) (h2 : S.P.tgt s = S.P.tgt r) :
    S.InU s r ∨ S.InU r s := by
  rcases S.chain s r h1 h2 with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · left; exact ⟨i, j, by rw [← h1, ← h2]; exact h⟩
  · right; exact ⟨i, j, h⟩

/-- **Every nonzero Hom has a generating ray** (the top of the endpoint chain). -/
theorem exists_gen (r : R) : ∃ f, S.P.src f = S.P.src r ∧ S.P.tgt f = S.P.tgt r ∧ S.IsGen f := by
  classical
  let H : Finset R := Finset.univ.filter fun s ↦ S.P.src s = S.P.src r ∧ S.P.tgt s = S.P.tgt r
  have hH : H.Nonempty := ⟨r, by simp [H]⟩
  obtain ⟨f, hf, hmin⟩ := H.exists_min_image (fun s ↦ S.P.deg (S.P.wt s)) hH
  simp only [H, Finset.mem_filter, Finset.mem_univ, true_and] at hf hmin
  refine ⟨f, hf.1, hf.2, fun s hs1 hs2 ↦ ?_⟩
  rcases S.inU_total hs1 hs2 with h | h
  · exact h
  · have a := S.deg_le_of_inU h
    have := hmin s ⟨hs1.trans hf.1, hs2.trans hf.2⟩
    rw [a.2 (le_antisymm this a.1)]
    exact S.inU_refl s

theorem gen_unique {f f' : R} (hf : S.IsGen f) (hf' : S.IsGen f') (h1 : S.P.src f = S.P.src f')
    (h2 : S.P.tgt f = S.P.tgt f') : f = f' :=
  S.inU_antisymm (hf' f h1 h2) (hf f' h1.symm h2.symm)

/-- **A generating ray generates its Hom over one endpoint** (Lemma 3.1(3)). -/
theorem gen_cyc {f : R} (hf : S.IsGen f) : S.CycL f ∨ S.CycR f := by
  rcases S.cyc f with h | h
  · left
    intro s h1 h2
    obtain ⟨i, j, hs⟩ := hf s h1 h2
    obtain ⟨i', hi'⟩ := h i j (by rw [← hs]; exact S.P.rr_ne_zero s)
    exact ⟨i', hs.trans hi'⟩
  · right
    intro s h1 h2
    obtain ⟨i, j, hs⟩ := hf s h1 h2
    obtain ⟨j', hj'⟩ := h i j (by rw [← hs]; exact S.P.rr_ne_zero s)
    exact ⟨j', hs.trans hj'⟩

theorem isGen_of_cycL {f : R} (h : S.CycL f) : S.IsGen f := fun s h1 h2 ↦ by
  obtain ⟨i, hi⟩ := h s h1 h2
  exact ⟨i, 0, by rw [hi, pow_zero, mul_one]⟩

theorem isGen_of_cycR {f : R} (h : S.CycR f) : S.IsGen f := fun s h1 h2 ↦ by
  obtain ⟨j, hj⟩ := h s h1 h2
  exact ⟨0, j, by rw [hj, pow_zero, one_mul]⟩

/-! ### Weights of elements -/

theorem wtM_mul (a b : M S.P.toMult) (h : a * b ≠ 0) : S.wtM (a * b) = S.wtM a + S.wtM b := by
  rcases S.elt_cases a with rfl | rfl | ⟨r, rfl⟩
  · rw [one_mul, wtM_one, zero_add]
  · exact absurd (zero_mul b) h
  · rcases S.elt_cases b with rfl | rfl | ⟨s, rfl⟩
    · rw [mul_one, wtM_one, add_zero]
    · exact absurd (mul_zero _) h
    · obtain ⟨t, -, ht⟩ := S.P.rr_mul_rr_ne_zero h
      rw [ht, wtM_rr, wtM_rr, wtM_rr]
      exact S.P.wt_of_mul ht

theorem wtM_pow (a : M S.P.toMult) (n : ℕ) (h : a ^ n ≠ 0) : S.wtM (a ^ n) = n • S.wtM a := by
  induction n with
  | zero => rw [pow_zero, wtM_one, zero_smul]
  | succ n ih =>
    rw [pow_succ] at h ⊢
    rw [S.wtM_mul _ _ h, ih (fun h' ↦ h (by rw [h', zero_mul])), succ_nsmul]

theorem wtM_qpow (x : V) (n : ℕ) (h : S.q x ^ n ≠ 0) : S.wtM (S.q x ^ n) = n • S.χ x :=
  S.wtM_pow _ n h

theorem eq_rr_of_ne (a : M S.P.toMult) (h0 : a ≠ 0) (h1 : a ≠ 1) : ∃ r, a = ⌜r⌝ := by
  rcases S.elt_cases a with h | h | h
  · exact absurd h h1
  · exact absurd h h0
  · exact h

theorem rf_deg_le {r s : R} (h : S.P.RF r s) : S.P.deg (S.P.wt r) ≤ S.P.deg (S.P.wt s) := by
  obtain ⟨v, hv⟩ := h
  rw [S.P.wt_mul _ _ _ hv, map_add]
  have := S.P.deg_nonneg v
  omega

theorem lf_deg_le {r s : R} (h : S.P.LF r s) : S.P.deg (S.P.wt s) ≤ S.P.deg (S.P.wt r) := by
  obtain ⟨v, hv⟩ := h
  rw [S.P.wt_mul _ _ _ hv, map_add]
  have := S.P.deg_nonneg v
  omega

theorem rf_iff (r s : R) : S.P.RF r s ↔ ∃ v, ⌜r⌝ * ⌜v⌝ = ⌜s⌝ :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨v, S.P.rr_mul_rr_eq_rr.2 hv⟩, fun ⟨v, hv⟩ ↦ ⟨v, S.P.rr_mul_rr_eq_rr.1 hv⟩⟩

theorem lf_iff (r s : R) : S.P.LF r s ↔ ∃ v, ⌜v⌝ * ⌜s⌝ = ⌜r⌝ :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨v, S.P.rr_mul_rr_eq_rr.2 hv⟩, fun ⟨v, hv⟩ ↦ ⟨v, S.P.rr_mul_rr_eq_rr.1 hv⟩⟩

theorem src_of_mul_ne {r s : R} (h : ⌜r⌝ * ⌜s⌝ ≠ 0) : S.P.tgt r = S.P.src s := by
  obtain ⟨t, -, ht⟩ := S.P.rr_mul_rr_ne_zero h
  exact (S.prod_of ht).2.2.1

/-- A loop of degree zero is the identity. -/
theorem eq_e_of_deg_zero {r : R} (h : S.P.deg (S.P.wt r) = 0) : r = S.P.e (S.P.src r) :=
  S.P.eq_e_of_deg h

end Sys

end RaySys

end MultiplicativeBasisDeformations
