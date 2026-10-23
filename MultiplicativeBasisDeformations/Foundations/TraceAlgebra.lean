module

public import Mathlib.RingTheory.FreeRing
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NoncommRing

/-!
# The ring of centre words and its twisted traces

Proof of Lemmas A.3–A.4 in algebraic form (`periodic-mesh-calculations.tex`). The centre corner of `Π(Δ)` for a star with arms of `L i + 1`
vertices is a quotient of
`ℤ⟨x_1, …, x_t⟩ / (∑ x_i, x_i^{L i + 2})` (`eq:star-corner-presentation`; the
coefficients of all relations are integers). A *twisted trace* on words is an
additive function `tr` on words, compatible with these relations, with
`tr (u v) = tr (v θ(u))` and `tr (x_i^q) = 0` for arms fixed by `θ`. It descends
to an additive map on the quotient ring `R`, in which the calculations of
Appendix A are ring identities.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

variable {t : ℕ} (L : Fin t → ℕ)

/-- A word as an element of the free ring. -/
def word (w : List (Fin t)) : FreeRing (Fin t) := (w.map FreeRing.of).prod

theorem word_append (u v : List (Fin t)) : word (u ++ v) = word u * word v := by
  simp [word, List.prod_append]

theorem word_eq_of (w : List (Fin t)) :
    word w = (MonoidAlgebra.single (FreeMonoid.ofList w) (1 : ℤ) :
      MonoidAlgebra ℤ (FreeMonoid (Fin t))) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [word, List.map_cons, List.prod_cons, ← word, ih]
      exact (MonoidAlgebra.single_mul_single (FreeMonoid.of i) (FreeMonoid.ofList w)
        (1 : ℤ) 1).trans (by rw [one_mul]; rfl)

/-- The relations of the centre corner. -/
def gens : Set (FreeRing (Fin t)) :=
  {r | r = ∑ i, FreeRing.of i ∨ ∃ i, r = FreeRing.of i ^ (L i + 2)}

/-- The two-sided ideal they generate, as an additive subgroup. -/
def J : AddSubgroup (FreeRing (Fin t)) :=
  AddSubgroup.closure {x | ∃ a b r, r ∈ gens L ∧ x = a * r * b}

theorem J_mul_left (c : FreeRing (Fin t)) {x : FreeRing (Fin t)} (hx : x ∈ J L) : c * x ∈ J L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨a, b, r, hr, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨c * a, b, r, hr, by noncomm_ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem J_mul_right (c : FreeRing (Fin t)) {x : FreeRing (Fin t)} (hx : x ∈ J L) : x * c ∈ J L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨a, b, r, hr, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨a, b * c, r, hr, by noncomm_ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

/-- The congruence of the relations. -/
def con : RingCon (FreeRing (Fin t)) where
  r a b := a - b ∈ J L
  iseqv := ⟨fun a ↦ by simp, fun h ↦ by rw [← neg_sub]; exact neg_mem h,
    fun h h' ↦ by rw [← sub_add_sub_cancel]; exact add_mem h h'⟩
  add' {a b c d} h h' := by
    rw [show a + c - (b + d) = (a - b) + (c - d) by abel]; exact add_mem h h'
  mul' {a b c d} h h' := by
    rw [show a * c - b * d = (a - b) * c + b * (c - d) by noncomm_ring]
    exact add_mem (J_mul_right L c h) (J_mul_left L b h')

/-- The ring of centre words modulo the star relations. -/
abbrev R := (con L).Quotient

/-- The quotient map. -/
def mk : FreeRing (Fin t) →+* R L := (con L).mk'

/-- The closed path `x_i`. -/
def x (i : Fin t) : R L := mk L (FreeRing.of i)

theorem mk_eq_zero {a : FreeRing (Fin t)} (h : a ∈ J L) : mk L a = 0 := by
  rw [← map_zero (mk L)]
  exact (RingCon.eq (con L)).2 (by simpa [con] using h)

theorem gen_mem {r : FreeRing (Fin t)} (h : r ∈ gens L) : r ∈ J L :=
  AddSubgroup.subset_closure ⟨1, 1, r, h, by simp⟩

/-- **The centre relation** `∑ x_i = 0`. -/
theorem sum_x : ∑ i, x L i = 0 := by
  simp only [x, ← map_sum]
  exact mk_eq_zero L (gen_mem L (Or.inl rfl))

/-- **The arm relation** `x_i^{L i + 2} = 0`. -/
theorem x_pow (i : Fin t) : x L i ^ (L i + 2) = 0 := by
  rw [x, ← map_pow]
  exact mk_eq_zero L (gen_mem L (Or.inr ⟨i, rfl⟩))

theorem mk_surjective : Function.Surjective (mk L) := (con L).mk'_surjective

/-- A twisted trace on words for the star with arms of `L i + 1` vertices. -/
structure TraceData (M : Type*) [AddCommGroup M] where
  tr : List (Fin t) → M
  θ : Equiv.Perm (Fin t)
  hL : ∀ i, L (θ i) = L i
  rotate : ∀ u v, tr (u ++ v) = tr (v ++ u.map θ)
  centre : ∀ u v, ∑ i, tr (u ++ i :: v) = 0
  arm : ∀ u v i, tr (u ++ List.replicate (L i + 2) i ++ v) = 0
  fixed : ∀ i, θ i = i → ∀ q, 1 ≤ q → tr (List.replicate q i) = 0

namespace TraceData

variable {L} {M : Type*} [AddCommGroup M] (D : TraceData L M)

/-- The trace on the free ring. -/
def trA : FreeRing (Fin t) →+ M :=
  (Finsupp.liftAddHom fun w : FreeMonoid (Fin t) ↦ zmultiplesHom M (D.tr (FreeMonoid.toList w))).comp
    (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := FreeMonoid (Fin t))).toAddMonoidHom

theorem trA_word (w : List (Fin t)) : D.trA (word w) = D.tr w := by
  rw [word_eq_of]
  change (Finsupp.liftAddHom fun w : FreeMonoid (Fin t) ↦
    zmultiplesHom M (D.tr (FreeMonoid.toList w))) (Finsupp.single (FreeMonoid.ofList w) (1 : ℤ)) = _
  rw [Finsupp.liftAddHom_apply_single]
  simp

/-- The twist on the free ring. -/
def twist : FreeRing (Fin t) →+* FreeRing (Fin t) := FreeRing.map D.θ

theorem twist_word (w : List (Fin t)) : D.twist (word w) = word (w.map D.θ) := by
  simp [word, twist, map_list_prod, List.map_map, Function.comp_def]

/-- Induction over the free ring, through words. -/
theorem induction_word {C : FreeRing (Fin t) → Prop} (a : FreeRing (Fin t)) (h0 : C 0)
    (hw : ∀ w, C (word w)) (hneg : ∀ a, C a → C (-a)) (hadd : ∀ a b, C a → C b → C (a + b)) :
    C a := by
  refine MonoidAlgebra.induction_linear (motive := C) a h0 hadd (fun m r ↦ ?_)
  have hm : C (MonoidAlgebra.single m (1 : ℤ)) := by
    simpa [word_eq_of] using hw (FreeMonoid.toList m)
  induction r using Int.induction_on with
  | zero => rw [MonoidAlgebra.single_zero]; exact h0
  | succ n ih => rw [MonoidAlgebra.single_add]; exact hadd _ _ ih hm
  | pred n ih =>
      rw [sub_eq_add_neg, MonoidAlgebra.single_add]
      exact hadd _ _ ih (by rw [MonoidAlgebra.single_neg]; exact hneg _ hm)

/-- **Twisted rotation** on the free ring. -/
theorem trA_rotate (a b : FreeRing (Fin t)) : D.trA (a * b) = D.trA (b * D.twist a) := by
  induction a using induction_word with
  | h0 => simp
  | hw u =>
      induction b using induction_word with
      | h0 => simp
      | hw v => rw [← word_append, twist_word, ← word_append, trA_word, trA_word, D.rotate]
      | hneg b h => rw [mul_neg, neg_mul, map_neg, map_neg, h]
      | hadd b c hb hc => rw [mul_add, add_mul, map_add, map_add, hb, hc]
  | hneg a h => rw [neg_mul, map_neg, map_neg, mul_neg, map_neg, h]
  | hadd a a' ha ha' => rw [add_mul, map_add, map_add, mul_add, map_add, ha, ha']

theorem trA_gen {r : FreeRing (Fin t)} (hr : r ∈ gens L) (a b : FreeRing (Fin t)) :
    D.trA (a * r * b) = 0 := by
  induction a using induction_word with
  | h0 => simp
  | hw u =>
      induction b using induction_word with
      | h0 => simp
      | hw v =>
          rcases hr with rfl | ⟨i, rfl⟩
          · rw [Finset.mul_sum, Finset.sum_mul, map_sum]
            refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (D.centre u v)
            rw [← trA_word, show u ++ i :: v = u ++ [i] ++ v by simp, word_append, word_append]
            simp [word]
          · rw [← D.arm u v i, ← trA_word, word_append, word_append]
            congr 2
            simp [word, List.prod_replicate]
      | hneg b h => rw [mul_neg, map_neg, h, neg_zero]
      | hadd b c hb hc => rw [mul_add, map_add, hb, hc, add_zero]
  | hneg a h => rw [neg_mul, neg_mul, map_neg, h, neg_zero]
  | hadd a a' ha ha' => rw [add_mul, add_mul, map_add, ha, ha', add_zero]

theorem trA_J {y : FreeRing (Fin t)} (hy : y ∈ J L) : D.trA y = 0 := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨a, b, r, hr, rfl⟩ := hx; exact D.trA_gen hr a b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]

/-- The trace on the ring of centre words. -/
def trR : R L →+ M :=
  (con L).toAddCon.lift D.trA fun a b h ↦ by
    change D.trA a = D.trA b
    rw [← sub_eq_zero, ← map_sub]
    exact D.trA_J h

theorem trR_mk (a : FreeRing (Fin t)) : D.trR (TraceAlg.mk L a) = D.trA a := rfl

theorem twist_J {y : FreeRing (Fin t)} (hy : y ∈ J L) : D.twist y ∈ J L := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨a, b, r, hr, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨D.twist a, D.twist b, D.twist r, ?_, by simp⟩
      rcases hr with rfl | ⟨i, rfl⟩
      · left
        rw [map_sum]
        simp only [twist, FreeRing.map_of]
        exact Fintype.sum_equiv D.θ _ _ fun _ ↦ rfl
      · right
        refine ⟨D.θ i, ?_⟩
        rw [map_pow, twist, FreeRing.map_of, D.hL]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/-- The twist on the ring of centre words. -/
def twR : R L →+* R L :=
  (con L).lift ((TraceAlg.mk L).comp D.twist) fun a b h ↦ by
    rw [RingCon.ker_apply]
    change TraceAlg.mk L (D.twist a) = TraceAlg.mk L (D.twist b)
    exact (RingCon.eq (con L)).2 (by
      change D.twist a - D.twist b ∈ J L
      rw [← map_sub]; exact D.twist_J h)

theorem twR_mk (a : FreeRing (Fin t)) : D.twR (TraceAlg.mk L a) = TraceAlg.mk L (D.twist a) := rfl

theorem twR_x (i : Fin t) : D.twR (x L i) = x L (D.θ i) := by
  rw [x, twR_mk, twist, FreeRing.map_of]; rfl

/-- **Twisted rotation** in the ring of centre words: `[p q] = [q θ(p)]`. -/
theorem trR_rotate (p q : R L) : D.trR (p * q) = D.trR (q * D.twR p) := by
  obtain ⟨a, rfl⟩ := TraceAlg.mk_surjective L p
  obtain ⟨b, rfl⟩ := TraceAlg.mk_surjective L q
  rw [← map_mul, twR_mk, ← map_mul, trR_mk, trR_mk, D.trA_rotate]

/-- The closed path of a word. -/
theorem mk_word (w : List (Fin t)) : TraceAlg.mk L (word w) = (w.map (x L)).prod := by
  simp [word, map_list_prod, List.map_map, Function.comp_def]; rfl

theorem trR_word (w : List (Fin t)) : D.trR ((w.map (x L)).prod) = D.tr w := by
  rw [← mk_word, trR_mk, trA_word]

/-- **Powers of the closed path along a fixed arm have zero trace.** -/
theorem trR_fixed (i : Fin t) (hi : D.θ i = i) (q : ℕ) (hq : 1 ≤ q) : D.trR (x L i ^ q) = 0 := by
  have := D.trR_word (List.replicate q i)
  rw [List.map_replicate, List.prod_replicate] at this
  rw [this, D.fixed i hi q hq]

end TraceData

end TraceAlg

end MultiplicativeBasisDeformations
