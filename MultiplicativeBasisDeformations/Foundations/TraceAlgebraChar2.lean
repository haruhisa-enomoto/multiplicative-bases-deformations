import MultiplicativeBasisDeformations.Foundations.TraceAlgebra

/-!
# Twisted traces in characteristic two

Appendix B (`characteristic-two-mesh-calculations.tex:225–330`) works in the centre
corner over a field of characteristic two. When `m + m = 0` on the target, a twisted
trace kills `2 r` for every `r`, so it factors through the quotient `Rc` of the free
ring by the relations and by `2`; in `Rc` we have `2 = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

variable {t : ℕ} (L : Fin t → ℕ)

/-- The relations together with the multiples of two. -/
def Jc : AddSubgroup (FreeRing (Fin t)) where
  carrier := {r | ∃ s ∈ J L, ∃ u, r = s + 2 * u}
  add_mem' {a b} ha hb := by
    obtain ⟨s, hs, u, rfl⟩ := ha
    obtain ⟨s', hs', u', rfl⟩ := hb
    exact ⟨s + s', add_mem hs hs', u + u', by rw [mul_add]; abel⟩
  zero_mem' := ⟨0, zero_mem _, 0, by simp⟩
  neg_mem' {a} ha := by
    obtain ⟨s, hs, u, rfl⟩ := ha
    exact ⟨-s, neg_mem hs, -u, by rw [mul_neg, neg_add]⟩

theorem J_le_Jc {r : FreeRing (Fin t)} (h : r ∈ J L) : r ∈ Jc L := ⟨r, h, 0, by simp⟩

theorem two_mem_Jc (u : FreeRing (Fin t)) : 2 * u ∈ Jc L := ⟨0, zero_mem _, u, by simp⟩

theorem Jc_mul_left (c : FreeRing (Fin t)) {r : FreeRing (Fin t)} (h : r ∈ Jc L) : c * r ∈ Jc L := by
  obtain ⟨s, hs, u, rfl⟩ := h
  refine ⟨c * s, J_mul_left L c hs, c * u, ?_⟩
  rw [mul_add, ← mul_assoc, ← mul_assoc, (Commute.ofNat_left 2 c).eq]

theorem Jc_mul_right (c : FreeRing (Fin t)) {r : FreeRing (Fin t)} (h : r ∈ Jc L) : r * c ∈ Jc L := by
  obtain ⟨s, hs, u, rfl⟩ := h
  exact ⟨s * c, J_mul_right L c hs, u * c, by rw [add_mul, mul_assoc]⟩

/-- The congruence of the relations and two. -/
def conc : RingCon (FreeRing (Fin t)) where
  r a b := a - b ∈ Jc L
  iseqv := ⟨fun a ↦ by simp, fun h ↦ by rw [← neg_sub]; exact neg_mem h,
    fun h h' ↦ by rw [← sub_add_sub_cancel]; exact add_mem h h'⟩
  add' {a b c d} h h' := by
    rw [show a + c - (b + d) = (a - b) + (c - d) by abel]; exact add_mem h h'
  mul' {a b c d} h h' := by
    rw [show a * c - b * d = (a - b) * c + b * (c - d) by noncomm_ring]
    exact add_mem (Jc_mul_right L c h) (Jc_mul_left L b h')

/-- The ring of centre words in characteristic two. -/
abbrev Rc := (conc L).Quotient

/-- The quotient map. -/
def mkc : FreeRing (Fin t) →+* Rc L := (conc L).mk'

theorem mkc_surjective : Function.Surjective (mkc L) := (conc L).mk'_surjective

/-- The closed path `x_i` in `Rc`. -/
def z (i : Fin t) : Rc L := mkc L (FreeRing.of i)

theorem mkc_eq_zero {a : FreeRing (Fin t)} (h : a ∈ Jc L) : mkc L a = 0 := by
  rw [← map_zero (mkc L)]
  exact (RingCon.eq (conc L)).2 (by simpa [conc] using h)

theorem sum_z : ∑ i, z L i = 0 := by
  simp only [z, ← map_sum]
  exact mkc_eq_zero L (J_le_Jc L (gen_mem L (Or.inl rfl)))

theorem z_pow (i : Fin t) : z L i ^ (L i + 2) = 0 := by
  rw [z, ← map_pow]
  exact mkc_eq_zero L (J_le_Jc L (gen_mem L (Or.inr ⟨i, rfl⟩)))

/-- **Two is zero** in `Rc`. -/
theorem two_eq_zero : (2 : Rc L) = 0 := by
  have := mkc_eq_zero L (two_mem_Jc L 1)
  rwa [mul_one, map_ofNat] at this

namespace TraceData

variable {L} {M : Type*} [AddCommGroup M] (D : TraceData L M) (h2 : ∀ m : M, m + m = 0)

include h2 in
theorem trA_Jc {r : FreeRing (Fin t)} (hr : r ∈ Jc L) : D.trA r = 0 := by
  obtain ⟨s, hs, u, rfl⟩ := hr
  rw [map_add, D.trA_J hs, zero_add, two_mul, map_add]
  exact h2 _

/-- The trace on `Rc`. -/
def trc : Rc L →+ M :=
  (conc L).toAddCon.lift D.trA fun a b hab ↦ by
    change D.trA a = D.trA b
    rw [← sub_eq_zero, ← map_sub]
    exact D.trA_Jc h2 hab

theorem trc_mk (a : FreeRing (Fin t)) : D.trc h2 (mkc L a) = D.trA a := rfl

theorem twist_Jc {r : FreeRing (Fin t)} (hr : r ∈ Jc L) : D.twist r ∈ Jc L := by
  obtain ⟨s, hs, u, rfl⟩ := hr
  exact ⟨D.twist s, D.twist_J hs, D.twist u, by rw [map_add, map_mul, map_ofNat]⟩

/-- The twist on `Rc`. -/
def twc : Rc L →+* Rc L :=
  (conc L).lift ((mkc L).comp D.twist) fun a b h ↦ by
    rw [RingCon.ker_apply]
    change mkc L (D.twist a) = mkc L (D.twist b)
    exact (RingCon.eq (conc L)).2 (by
      change D.twist a - D.twist b ∈ Jc L
      rw [← map_sub]; exact D.twist_Jc h)

theorem twc_mk (a : FreeRing (Fin t)) : D.twc (mkc L a) = mkc L (D.twist a) := rfl

theorem twc_z (i : Fin t) : D.twc (z L i) = z L (D.θ i) := by
  rw [z, twc_mk, twist, FreeRing.map_of]; rfl

/-- **Twisted rotation** in `Rc`. -/
theorem trc_rotate (p q : Rc L) : D.trc h2 (p * q) = D.trc h2 (q * D.twc p) := by
  obtain ⟨a, rfl⟩ := mkc_surjective L p
  obtain ⟨b, rfl⟩ := mkc_surjective L q
  rw [← map_mul, twc_mk, ← map_mul, trc_mk, trc_mk, D.trA_rotate]

theorem mkc_word (w : List (Fin t)) : mkc L (word w) = (w.map (z L)).prod := by
  simp [word, map_list_prod, List.map_map, Function.comp_def]; rfl

theorem trc_word (w : List (Fin t)) : D.trc h2 ((w.map (z L)).prod) = D.tr w := by
  rw [← mkc_word, trc_mk, trA_word]

theorem trc_fixed (i : Fin t) (hi : D.θ i = i) (q : ℕ) (hq : 1 ≤ q) : D.trc h2 (z L i ^ q) = 0 := by
  have := D.trc_word h2 (List.replicate q i)
  rw [List.map_replicate, List.prod_replicate] at this
  rw [this, D.fixed i hi q hq]

theorem twc_id (hθ : ∀ i, D.θ i = i) (r : Rc L) : D.twc r = r := by
  have : D.twc.comp (mkc L) = mkc L := by
    ext i
    simp only [RingHom.comp_apply]
    change D.twc (z L i) = z L i
    rw [D.twc_z, hθ]
  obtain ⟨a, rfl⟩ := mkc_surjective L r
  exact congrArg (fun f : FreeRing (Fin t) →+* Rc L ↦ f a) this

end TraceData

end TraceAlg

end MultiplicativeBasisDeformations
