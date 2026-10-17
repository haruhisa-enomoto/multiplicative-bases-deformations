import MultiplicativeBasisDeformations.Foundations.StemProduct

/-!
# Corollary 8.13: active zero pairs

`cor:active-zero-pairs` (`local-ray-geometry.tex:518–542`): for rays `r : x → y`,
`s : y → z` with `rs = 0` and `r * s ≠ 0`, both are generating, `r * s = r q_y s`, and this
ray is annihilated by both endpoint radicals.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

/-- In a Hom cyclic at its source, the target action is a power of the source action. -/
theorem tgt_action_of_cycL {f r : R} (hf : S.CycL f) (h1 : S.P.src r = S.P.src f)
    (h2 : S.P.tgt r = S.P.tgt f) : ⌜r⌝ * S.q (S.P.tgt r) = 0 ∨
      ∃ a, 1 ≤ a ∧ ⌜r⌝ * S.q (S.P.tgt r) = S.q (S.P.src r) ^ a * ⌜r⌝ := by
  by_cases h0 : ⌜r⌝ * S.q (S.P.tgt r) = 0
  · exact Or.inl h0
  right
  obtain ⟨t, ht⟩ := S.mul_left_ray h0
  have hq : S.q (S.P.tgt r) ≠ 0 := fun h' ↦ h0 (by rw [h', mul_zero])
  have htU : S.InU t r := ⟨0, 1, by rw [← ht, pow_zero, one_mul, pow_one]⟩
  obtain ⟨e1, e2, -⟩ := S.inU_endpoints htU
  obtain ⟨i, hi⟩ := hf r h1 h2
  obtain ⟨c, hc⟩ := hf t (e1.trans h1) (e2.trans h2)
  have hdr := S.deg_wt_qpow_mul hi
  have hdt := S.deg_wt_qpow_mul hc
  have hdq := S.χ_deg_pos _ hq
  have hdtr : S.P.deg (S.P.wt t) = S.P.deg (S.P.wt r) + S.P.deg (S.χ (S.P.tgt r)) := by
    have := congrArg S.wtM ht
    rw [S.wtM_mul _ _ h0, wtM_rr, wtM_rr] at this
    rw [← this, map_add]; rfl
  have hdx := S.deg_χ_nonneg (S.P.src f)
  have hci : i < c := by
    by_contra hci
    have : (c : ℤ) * S.P.deg (S.χ (S.P.src f)) ≤ i * S.P.deg (S.χ (S.P.src f)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast not_lt.1 hci) hdx
    linarith
  refine ⟨c - i, by omega, ?_⟩
  rw [ht, hc, hi, h1, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hci.le]

/-- In a Hom cyclic at its target, the source action is a power of the target action. -/
theorem src_action_of_cycR {g s : R} (hg : S.CycR g) (h1 : S.P.src s = S.P.src g)
    (h2 : S.P.tgt s = S.P.tgt g) : S.q (S.P.src s) * ⌜s⌝ = 0 ∨
      ∃ a, 1 ≤ a ∧ S.q (S.P.src s) * ⌜s⌝ = ⌜s⌝ * S.q (S.P.tgt s) ^ a := by
  by_cases h0 : S.q (S.P.src s) * ⌜s⌝ = 0
  · exact Or.inl h0
  right
  obtain ⟨t, ht⟩ := S.mul_right_ray h0
  have hq : S.q (S.P.src s) ≠ 0 := fun h' ↦ h0 (by rw [h', zero_mul])
  have htU : S.InU t s := ⟨1, 0, by rw [← ht, pow_zero, mul_one, pow_one]⟩
  obtain ⟨e1, e2, -⟩ := S.inU_endpoints htU
  obtain ⟨i, hi⟩ := hg s h1 h2
  obtain ⟨c, hc⟩ := hg t (e1.trans h1) (e2.trans h2)
  have hds : S.P.deg (S.P.wt s) = S.P.deg (S.P.wt g) + i * S.P.deg (S.χ (S.P.tgt g)) := by
    have := congrArg S.wtM hi
    rw [S.wtM_mul _ _ (hi ▸ S.rr_ne s), wtM_rr, wtM_rr,
      S.wtM_qpow _ _ (fun h' ↦ S.rr_ne s (by rw [hi, h', mul_zero]))] at this
    rw [this, map_add, map_nsmul, nsmul_eq_mul]
  have hdt : S.P.deg (S.P.wt t) = S.P.deg (S.P.wt g) + c * S.P.deg (S.χ (S.P.tgt g)) := by
    have := congrArg S.wtM hc
    rw [S.wtM_mul _ _ (hc ▸ S.rr_ne t), wtM_rr, wtM_rr,
      S.wtM_qpow _ _ (fun h' ↦ S.rr_ne t (by rw [hc, h', mul_zero]))] at this
    rw [this, map_add, map_nsmul, nsmul_eq_mul]
  have hdq := S.χ_deg_pos _ hq
  have hdts : S.P.deg (S.P.wt t) = S.P.deg (S.χ (S.P.src s)) + S.P.deg (S.P.wt s) := by
    have := congrArg S.wtM ht
    rw [S.wtM_mul _ _ h0, wtM_rr, wtM_rr] at this
    rw [← this, map_add]; rfl
  have hdz := S.deg_χ_nonneg (S.P.tgt g)
  have hci : i < c := by
    by_contra hci
    have : (c : ℤ) * S.P.deg (S.χ (S.P.tgt g)) ≤ i * S.P.deg (S.χ (S.P.tgt g)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast not_lt.1 hci) hdz
    linarith
  refine ⟨c - i, by omega, ?_⟩
  rw [ht, hc, hi, h2, mul_assoc, ← pow_add, Nat.add_sub_cancel' hci.le]

theorem pow_action {r : R} {a : ℕ} (h : ⌜r⌝ * S.q (S.P.tgt r) = S.q (S.P.src r) ^ a * ⌜r⌝)
    (n : ℕ) : ⌜r⌝ * S.q (S.P.tgt r) ^ n = S.q (S.P.src r) ^ (a * n) * ⌜r⌝ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_add,
      Nat.mul_succ]

theorem pow_action' {s : R} {a : ℕ} (h : S.q (S.P.src s) * ⌜s⌝ = ⌜s⌝ * S.q (S.P.tgt s) ^ a)
    (n : ℕ) : S.q (S.P.src s) ^ n * ⌜s⌝ = ⌜s⌝ * S.q (S.P.tgt s) ^ (a * n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_add,
      Nat.mul_succ, add_comm]

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Corollary 8.13** (`cor:active-zero-pairs`). -/
theorem active_zero (hfin : IsRepresentationFinite k (S.P.Lin k)) {r s : R}
    (hrs0 : ⌜r⌝ * ⌜s⌝ = 0) (hst : S.stem r s ≠ 0) :
    S.IsGen r ∧ S.IsGen s ∧ S.stem r s = ⌜r⌝ * S.q (S.P.tgt r) * ⌜s⌝ ∧
      S.q (S.P.src r) * (⌜r⌝ * S.q (S.P.tgt r) * ⌜s⌝) = 0 ∧
      ⌜r⌝ * S.q (S.P.tgt r) * ⌜s⌝ * S.q (S.P.tgt s) = 0 := by
  classical
  have hex : ∃ n : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ ≠ 0 := by
    by_contra h; exact hst (by rw [stem, dif_neg h])
  have hmid : S.P.tgt r = S.P.src s := by
    obtain ⟨n, hn⟩ := hex
    have h1 : ⌜r⌝ * S.q (S.P.tgt r) ^ n ≠ 0 := fun h0 ↦ hn (by rw [h0, zero_mul])
    obtain ⟨u, hu⟩ := S.mul_left_ray h1
    have hU : S.InU u r := ⟨0, n, by rw [← hu, pow_zero, one_mul]⟩
    rw [← (S.inU_endpoints hU).2.1]
    exact S.src_of_mul_ne (show ⌜u⌝ * ⌜s⌝ ≠ 0 by rw [← hu]; exact hn)
  -- the Hom of `r` is generated only at `y`
  obtain ⟨f, f1, f2, hfg⟩ := S.exists_gen r
  have hnotL : ¬ S.CycL f := by
    intro hL
    obtain ⟨n, hn⟩ := hex
    rcases S.tgt_action_of_cycL hL f1.symm f2.symm with h | ⟨a, -, h⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · exact hn (by simpa using hrs0)
      · exact hn (by rw [show n = (n - 1) + 1 by omega, pow_succ', ← mul_assoc, h, zero_mul,
          zero_mul])
    · exact hn (by rw [S.pow_action h n, mul_assoc, hrs0, mul_zero])
  have hfR : S.CycR f := (S.gen_cyc hfg).resolve_left hnotL
  -- the Hom of `s` is generated only at `y`
  obtain ⟨g, g1, g2, hgg⟩ := S.exists_gen s
  have hnotR : ¬ S.CycR g := by
    intro hR
    obtain ⟨n, hn⟩ := hex
    rcases S.src_action_of_cycR hR g1.symm g2.symm with h | ⟨a, -, h⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · exact hn (by simpa using hrs0)
      · exact hn (by rw [hmid, show n = (n - 1) + 1 by omega, pow_succ, mul_assoc, mul_assoc, h,
          mul_zero, mul_zero])
    · exact hn (by rw [hmid, mul_assoc, S.pow_action' h n, ← mul_assoc, hrs0, zero_mul])
  have hgL : S.CycL g := (S.gen_cyc hgg).resolve_right hnotR
  obtain ⟨i, hi⟩ := hfR r f1.symm f2.symm
  obtain ⟨j, hj⟩ := hgL s g1.symm g2.symm
  have hfg' : S.P.tgt f = S.P.src g := by rw [f2, hmid, ← g1]
  have key : ∀ n, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ =
      ⌜f⌝ * S.q (S.P.tgt f) ^ (i + n + j) * ⌜g⌝ := by
    intro n
    rw [hi, hj, ← f2, ← hfg', pow_add, pow_add]
    simp only [mul_assoc]
  have hhigh := S.opposite_controls_high k hfin hfR hnotL hgL hnotR hfg'
  obtain ⟨n, hn⟩ := hex
  rw [key] at hn
  have h1 : i + n + j ≤ 1 := by
    by_contra h; exact hn (hhigh _ (by omega))
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    apply hn
    rw [← key, pow_zero, mul_one, hrs0]
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  have hn' : n = 1 := by omega
  subst hi0 hj0 hn'
  have hrf : r = f := S.rr_inj (by rw [hi, pow_zero, mul_one])
  have hsg : s = g := S.rr_inj (by rw [hj, pow_zero, one_mul])
  subst hrf hsg
  refine ⟨hfg, hgg, ?_, ?_, ?_⟩
  · have hex' : ∃ n : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ ≠ 0 :=
      ⟨1, by rw [key]; exact hn⟩
    rw [stem, dif_pos hex']
    have : Nat.find hex' = 1 := by
      rw [Nat.find_eq_iff]
      refine ⟨by rw [key]; exact hn, fun m hm ↦ ?_⟩
      have : m = 0 := by omega
      subst this
      simpa using hrs0
    rw [this, pow_one]
  · have := S.opposite_controls_src k hfin hfR hnotL hgL hnotR hfg' 1
    rwa [pow_one] at this
  · have := S.opposite_controls_tgt k hfin hfR hnotL hgL hnotR hfg' 1
    rwa [pow_one] at this

end Sys

end RaySys

end MultiplicativeBasisDeformations
