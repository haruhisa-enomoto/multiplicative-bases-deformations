import MultiplicativeBasisDeformations.Foundations.OppositeControls2

/-!
# Lemma 8.11(2)

`lem:opposite-controls`(2): "The product space `f R_c g` has dimension at most one and is
annihilated by `rad R_b` on the left and `rad R_a` on the right." The source's proof: a radical
action at an outside endpoint moves at least two powers of `q` to the middle
(`eq:opposite-control-inclusions`: `rad_src_mul_of_cycR`, `rad_tgt_pow_mul_of_cycL`), and every
term `f q^n g` with `n ≥ 2` vanishes by (1) (`opposite_controls`); the endpoint Hom is uniserial
with a one-dimensional socle (`socle_unique`, from the endpoint chain), so the nonzero products
`f q^j g` all coincide (`opposite_controls_two`).
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

/-- **The endpoint socle is one-dimensional**: two rays with the same endpoints killed by both
endpoint radicals are equal. -/
theorem socle_unique {r s : R} (h1 : S.P.src r = S.P.src s) (h2 : S.P.tgt r = S.P.tgt s)
    (hrL : S.q (S.P.src r) * ⌜r⌝ = 0) (hrR : ⌜r⌝ * S.q (S.P.tgt r) = 0)
    (hsL : S.q (S.P.src s) * ⌜s⌝ = 0) (hsR : ⌜s⌝ * S.q (S.P.tgt s) = 0) : r = s := by
  have key : ∀ {a b : R}, S.P.src a = S.P.src b → S.P.tgt a = S.P.tgt b →
      S.q (S.P.src b) * ⌜b⌝ = 0 → ⌜b⌝ * S.q (S.P.tgt b) = 0 → ∀ i j : ℕ,
      ⌜a⌝ = S.q (S.P.src a) ^ i * ⌜b⌝ * S.q (S.P.tgt a) ^ j → a = b := by
    intro a b e1 e2 hbL hbR i j h
    rw [e1, e2] at h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [pow_zero, one_mul, mul_one] at h
        exact S.rr_inj h
      · exfalso
        obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_lt hj
        apply S.rr_ne a
        rw [h, pow_succ', zero_add, pow_zero, one_mul, ← mul_assoc, hbR, zero_mul]
    · exfalso
      obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_lt hi
      apply S.rr_ne a
      rw [h, zero_add, pow_succ, mul_assoc _ (S.q (S.P.src b)), hbL, mul_zero, zero_mul]
  rcases S.chain r s h1 h2 with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · exact key h1 h2 hsL hsR i j h
  · rw [h1, h2] at h
    exact (key h1.symm h2.symm hrL hrR i j h).symm

/-- A nonzero `f q^i g` is a ray from the source of `f` to the target of `g`. -/
theorem fqg_ray {f g : R} (hfg : S.P.tgt f = S.P.src g) (i : ℕ)
    (h0 : ⌜f⌝ * S.q (S.P.tgt f) ^ i * ⌜g⌝ ≠ 0) :
    ∃ w, ⌜f⌝ * S.q (S.P.tgt f) ^ i * ⌜g⌝ = ⌜w⌝ ∧ S.P.src w = S.P.src f ∧ S.P.tgt w = S.P.tgt g := by
  have e : ⌜f⌝ * S.q (S.P.tgt f) ^ i * ⌜g⌝ =
      ⌜f⌝ * (S.q (S.P.tgt f) ^ i * ⌜S.P.e (S.P.tgt f)⌝) * ⌜g⌝ := by
    rw [mul_assoc ⌜f⌝ (_ * _), mul_assoc _ ⌜S.P.e (S.P.tgt f)⌝, S.e_mul_rr' g hfg.symm,
      ← mul_assoc]
  rcases S.qpow_cases (S.P.tgt f) i with hz | ⟨h, hh, hs, ht, -⟩
  · exact absurd (by rw [e, hz, mul_zero, zero_mul]) h0
  rw [e, hh] at h0 ⊢
  have hfh : ⌜f⌝ * ⌜h⌝ ≠ 0 := fun h' ↦ h0 (by rw [h', zero_mul])
  obtain ⟨t, htt⟩ := S.ray_of_mul_ne hfh
  obtain ⟨t1, t2, -, -⟩ := S.prod_of htt
  rw [htt] at h0 ⊢
  obtain ⟨w, hw⟩ := S.ray_of_mul_ne h0
  obtain ⟨w1, w2, -, -⟩ := S.prod_of hw
  exact ⟨w, hw, by rw [w1, t1], w2⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.11(2)** (`lem:opposite-controls`): for generating `f : b → c`, `g : c → a` whose
Homs are cyclic at `c` but not at the other endpoints, the products `f q^j g` spanning `f R_c g`
are killed by `rad R_b = q_b R_b` on the left and by `rad R_a = R_a q_a` on the right, and any
two nonzero ones coincide, so `f R_c g` has dimension at most one. -/
theorem opposite_controls_two (hfin : IsRepresentationFinite k (S.P.Lin k)) {f g : R}
    (hfR : S.CycR f) (hfL : ¬ S.CycL f) (hgL : S.CycL g) (hgR : ¬ S.CycR g)
    (hfg : S.P.tgt f = S.P.src g) :
    (∀ j : ℕ, S.q (S.P.src f) * (⌜f⌝ * S.q (S.P.tgt f) ^ j * ⌜g⌝) = 0) ∧
    (∀ j : ℕ, ⌜f⌝ * S.q (S.P.tgt f) ^ j * ⌜g⌝ * S.q (S.P.tgt g) = 0) ∧
    ∀ i j : ℕ, ⌜f⌝ * S.q (S.P.tgt f) ^ i * ⌜g⌝ ≠ 0 → ⌜f⌝ * S.q (S.P.tgt f) ^ j * ⌜g⌝ ≠ 0 →
      ⌜f⌝ * S.q (S.P.tgt f) ^ i * ⌜g⌝ = ⌜f⌝ * S.q (S.P.tgt f) ^ j * ⌜g⌝ := by
  set q := S.q (S.P.tgt f)
  -- the terms with at least two powers of `q` vanish, by (1)
  have hz : ∀ n, 2 ≤ n → ⌜f⌝ * q ^ n * ⌜g⌝ = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rcases S.opposite_controls k hfin hfR hfL hgL hgR hfg with h | h
    · rw [pow_add, ← mul_assoc, h, zero_mul, zero_mul]
    · rw [add_comm, pow_add, ← mul_assoc, mul_assoc _ (q ^ 2), h, mul_zero]
  have hleft : ∀ j : ℕ, S.q (S.P.src f) * (⌜f⌝ * q ^ j * ⌜g⌝) = 0 := by
    intro j
    rw [← mul_assoc, ← mul_assoc]
    rcases S.rad_src_mul_of_cycR hfR hfL with h | ⟨m, hm, h⟩
    · rw [h, zero_mul, zero_mul]
    · rw [h, mul_assoc ⌜f⌝, ← pow_add]
      exact hz _ (by omega)
  have hright : ∀ j : ℕ, ⌜f⌝ * q ^ j * ⌜g⌝ * S.q (S.P.tgt g) = 0 := by
    intro j
    rw [mul_assoc]
    rcases S.rad_tgt_pow_mul_of_cycL hgL hgR 1 le_rfl with h | ⟨m, hm, h⟩
    · rw [pow_one] at h; rw [h, mul_zero]
    · rw [pow_one] at h
      rw [h, ← hfg, ← mul_assoc, mul_assoc ⌜f⌝, ← pow_add]
      exact hz _ (by omega)
  refine ⟨hleft, hright, fun i j hi hj ↦ ?_⟩
  obtain ⟨wi, hwi, si, ti⟩ := S.fqg_ray hfg i hi
  obtain ⟨wj, hwj, sj, tj⟩ := S.fqg_ray hfg j hj
  rw [hwi, hwj]
  congr 1
  refine S.socle_unique (si.trans sj.symm) (ti.trans tj.symm) ?_ ?_ ?_ ?_
  · rw [si, ← hwi]; exact hleft i
  · rw [ti, ← hwi]; exact hright i
  · rw [sj, ← hwj]; exact hleft j
  · rw [tj, ← hwj]; exact hright j

end Sys

end RaySys

end MultiplicativeBasisDeformations
