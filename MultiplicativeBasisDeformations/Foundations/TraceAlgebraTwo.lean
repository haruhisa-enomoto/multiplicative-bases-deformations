module

public import MultiplicativeBasisDeformations.Foundations.TraceAlgebra

/-!
# Twisted traces when two is invertible

Appendix A, `periodic-mesh-calculations.tex` ("Assume two is invertible
and put `v = y - z = x + 2y`"): when `m + m = 0` forces `m = 0` on the target,
a twisted trace kills every element `r` with `2^n r` in the ideal of relations.
It therefore factors through the quotient `R₂` of the free ring by the
`2`-saturation of the relations, where `2 r = 0` implies `r = 0`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

variable {t : ℕ} (L : Fin t → ℕ)

/-- The `2`-saturation of the relations. -/
def J2 : AddSubgroup (FreeRing (Fin t)) where
  carrier := {r | ∃ n : ℕ, (2 : FreeRing (Fin t)) ^ n * r ∈ J L}
  add_mem' {a b} ha hb := by
    obtain ⟨n, hn⟩ := ha
    obtain ⟨n', hn'⟩ := hb
    refine ⟨n + n', ?_⟩
    rw [mul_add, pow_add]
    have e1 : (2 : FreeRing (Fin t)) ^ n * 2 ^ n' * a = 2 ^ n' * (2 ^ n * a) := by
      rw [(Commute.pow_pow (Commute.refl (2 : FreeRing (Fin t))) n n').eq, mul_assoc]
    have e2 : (2 : FreeRing (Fin t)) ^ n * 2 ^ n' * b = 2 ^ n * (2 ^ n' * b) := mul_assoc _ _ _
    rw [e1, e2]
    exact add_mem (J_mul_left L _ hn) (J_mul_left L _ hn')
  zero_mem' := ⟨0, by simp⟩
  neg_mem' {a} ha := by
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, by rw [mul_neg]; exact neg_mem hn⟩

theorem J_le_J2 {r : FreeRing (Fin t)} (h : r ∈ J L) : r ∈ J2 L := ⟨0, by simpa using h⟩

theorem J2_mul_left (c : FreeRing (Fin t)) {r : FreeRing (Fin t)} (h : r ∈ J2 L) : c * r ∈ J2 L := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have e : (2 : FreeRing (Fin t)) ^ n * (c * r) = c * (2 ^ n * r) := by
    rw [← mul_assoc, ← mul_assoc, ((Commute.ofNat_left 2 c).pow_left n).eq]
  rw [e]; exact J_mul_left L c hn

theorem J2_mul_right (c : FreeRing (Fin t)) {r : FreeRing (Fin t)} (h : r ∈ J2 L) : r * c ∈ J2 L := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← mul_assoc]; exact J_mul_right L c hn⟩

/-- The congruence of the saturated relations. -/
def con2 : RingCon (FreeRing (Fin t)) where
  r a b := a - b ∈ J2 L
  iseqv := ⟨fun a ↦ by simp, fun h ↦ by rw [← neg_sub]; exact neg_mem h,
    fun h h' ↦ by rw [← sub_add_sub_cancel]; exact add_mem h h'⟩
  add' {a b c d} h h' := by
    rw [show a + c - (b + d) = (a - b) + (c - d) by abel]; exact add_mem h h'
  mul' {a b c d} h h' := by
    rw [show a * c - b * d = (a - b) * c + b * (c - d) by noncomm_ring]
    exact add_mem (J2_mul_right L c h) (J2_mul_left L b h')

/-- The ring of centre words with two cancelled. -/
abbrev R2 := (con2 L).Quotient

/-- The quotient map. -/
def mk2 : FreeRing (Fin t) →+* R2 L := (con2 L).mk'

theorem mk2_surjective : Function.Surjective (mk2 L) := (con2 L).mk'_surjective

/-- The closed path `x_i` in `R₂`. -/
def y (i : Fin t) : R2 L := mk2 L (FreeRing.of i)

theorem mk2_eq_zero {a : FreeRing (Fin t)} (h : a ∈ J2 L) : mk2 L a = 0 := by
  rw [← map_zero (mk2 L)]
  exact (RingCon.eq (con2 L)).2 (by simpa [con2] using h)

theorem sum_y : ∑ i, y L i = 0 := by
  simp only [y, ← map_sum]
  exact mk2_eq_zero L (J_le_J2 L (gen_mem L (Or.inl rfl)))

theorem y_pow (i : Fin t) : y L i ^ (L i + 2) = 0 := by
  rw [y, ← map_pow]
  exact mk2_eq_zero L (J_le_J2 L (gen_mem L (Or.inr ⟨i, rfl⟩)))

/-- **Two can be cancelled** in `R₂`. -/
theorem cancel_two {r : R2 L} (h : 2 * r = 0) : r = 0 := by
  obtain ⟨a, rfl⟩ := mk2_surjective L r
  have h' : mk2 L (2 * a) = mk2 L 0 := by rw [map_mul, map_ofNat, h, map_zero]
  have := (RingCon.eq (con2 L)).1 h'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : FreeRing (Fin t)) ^ n * (2 * a - 0) ∈ J L := this
  have : a ∈ J2 L := ⟨n + 1, by rw [sub_zero] at hn; rw [pow_succ, mul_assoc]; exact hn⟩
  exact mk2_eq_zero L this

namespace TraceData

variable {L} {M : Type*} [AddCommGroup M] (D : TraceData L M) (h2 : ∀ m : M, m + m = 0 → m = 0)

include h2 in
theorem trA_J2 {r : FreeRing (Fin t)} (hr : r ∈ J2 L) : D.trA r = 0 := by
  obtain ⟨n, hn⟩ := hr
  induction n generalizing r with
  | zero => simpa using D.trA_J hn
  | succ n ih =>
      have h := ih (r := 2 * r) (by rw [← mul_assoc, ← pow_succ]; exact hn)
      apply h2
      rw [← map_add, ← two_mul]
      exact h

/-- The trace on `R₂`. -/
def tr2 : R2 L →+ M :=
  (con2 L).toAddCon.lift D.trA fun a b hab ↦ by
    change D.trA a = D.trA b
    rw [← sub_eq_zero, ← map_sub]
    exact D.trA_J2 h2 hab

theorem tr2_mk (a : FreeRing (Fin t)) : D.tr2 h2 (mk2 L a) = D.trA a := rfl

theorem twist_J2 {r : FreeRing (Fin t)} (hr : r ∈ J2 L) : D.twist r ∈ J2 L := by
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, by have := D.twist_J hn; rwa [map_mul, map_pow, map_ofNat] at this⟩

/-- The twist on `R₂`. -/
def tw2 : R2 L →+* R2 L :=
  (con2 L).lift ((mk2 L).comp D.twist) fun a b h ↦ by
    rw [RingCon.ker_apply]
    change mk2 L (D.twist a) = mk2 L (D.twist b)
    exact (RingCon.eq (con2 L)).2 (by
      change D.twist a - D.twist b ∈ J2 L
      rw [← map_sub]; exact D.twist_J2 h)

theorem tw2_mk (a : FreeRing (Fin t)) : D.tw2 (mk2 L a) = mk2 L (D.twist a) := rfl

theorem tw2_y (i : Fin t) : D.tw2 (y L i) = y L (D.θ i) := by
  rw [y, tw2_mk, twist, FreeRing.map_of]; rfl

/-- **Twisted rotation** in `R₂`. -/
theorem tr2_rotate (p q : R2 L) : D.tr2 h2 (p * q) = D.tr2 h2 (q * D.tw2 p) := by
  obtain ⟨a, rfl⟩ := mk2_surjective L p
  obtain ⟨b, rfl⟩ := mk2_surjective L q
  rw [← map_mul, tw2_mk, ← map_mul, tr2_mk, tr2_mk, D.trA_rotate]

theorem mk2_word (w : List (Fin t)) : mk2 L (word w) = (w.map (y L)).prod := by
  simp [word, map_list_prod, List.map_map, Function.comp_def]; rfl

theorem tr2_word (w : List (Fin t)) : D.tr2 h2 ((w.map (y L)).prod) = D.tr w := by
  rw [← mk2_word, tr2_mk, trA_word]

theorem tr2_fixed (i : Fin t) (hi : D.θ i = i) (q : ℕ) (hq : 1 ≤ q) : D.tr2 h2 (y L i ^ q) = 0 := by
  have := D.tr2_word h2 (List.replicate q i)
  rw [List.map_replicate, List.prod_replicate] at this
  rw [this, D.fixed i hi q hq]

end TraceData

end TraceAlg

end MultiplicativeBasisDeformations
