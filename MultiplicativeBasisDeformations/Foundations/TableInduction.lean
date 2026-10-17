import MultiplicativeBasisDeformations.Foundations.RayPres
import MultiplicativeBasisDeformations.Foundations.CentralizerTable
import MultiplicativeBasisDeformations.Foundations.TabSys
import MultiplicativeBasisDeformations.Foundations.IndicatorRel

/-!
# Tables for the dimension induction

Support for the strong induction of Proposition 8.3 (`main-theorems.tex:7–11`: "disconnected
algebras reduce to their connected factors"; Lemma 9.2: "`W(Q_χ)` is free by the dimension
induction … applied to each connected factor"):

* a ray table splits along a union of components into two tables with fewer rays, each with
  representation-finite linearization (a quotient of `kT`), and weight lifting holds for `T`
  when it holds for both pieces (`lift2_of_split`);
* a representation-finite ray table presents its own linearization (`self_rayPres`), which is
  basic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  (P : Tab V R L)

/-- A set of vertices closed under rays (a union of components). -/
structure Closed (C : V → Prop) : Prop where
  fwd : ∀ r, C (P.src r) → C (P.tgt r)
  bwd : ∀ r, C (P.tgt r) → C (P.src r)

variable {P}

/-- The sub-table on a union of components. -/
def compData {C : V → Prop} (hC : P.Closed C) : P.SubData where
  pV := C
  pR r := C (P.src r)
  e_mem x hx := by rw [P.src_e]; exact hx
  src_mem _ h := h
  tgt_mem r h := hC.fwd r h
  cc r s u t v w hr hs hu hrs htu hsu hw := by
    rw [P.mul_src _ _ _ hrs, P.mul_src _ _ _ hsu]
    exact ⟨fun _ ↦ hs, fun _ ↦ hr⟩

theorem compMul_eq_some {C : V → Prop} (hC : P.Closed C) {r s t : {r // C (P.src r)}} :
    (P.sub (compData hC)).mul r s = some t ↔ P.mul r.1 s.1 = some t.1 :=
  subMul_eq_some (compData hC)

/-- The complement of a union of components is one. -/
theorem Closed.compl {C : V → Prop} (hC : P.Closed C) : P.Closed fun x ↦ ¬ C x :=
  ⟨fun r h h' ↦ h (hC.bwd r h'), fun r h h' ↦ h (hC.fwd r h')⟩

/-- **Weight lifting for a table split into two unions of components.** -/
theorem lift2_of_split {C : V → Prop} (hC : P.Closed C)
    (h1 : (P.sub (compData hC)).Lift2) (h2 : (P.sub (compData hC.compl)).Lift2) : P.Lift2 := by
  classical
  intro w hw
  obtain ⟨ω1, hω1, hw1⟩ := h1 (fun r ↦ w r.1) fun r s t h ↦
    hw _ _ _ ((compMul_eq_some hC).1 h)
  obtain ⟨ω2, hω2, hw2⟩ := h2 (fun r ↦ w r.1) fun r s t h ↦
    hw _ _ _ ((compMul_eq_some hC.compl).1 h)
  refine ⟨fun r ↦ if h : C (P.src r) then ω1 ⟨r, h⟩ else ω2 ⟨r, h⟩, fun r s t h ↦ ?_, fun r ↦ ?_⟩
  · have hs : P.src s = P.tgt r := (P.mul_mid r s t h).symm
    have ht : P.src t = P.src r := P.mul_src r s t h
    by_cases hr : C (P.src r)
    · have hs' : C (P.src s) := by rw [hs]; exact hC.fwd r hr
      have ht' : C (P.src t) := by rw [ht]; exact hr
      simp only [dif_pos hr, dif_pos hs', dif_pos ht']
      exact hω1 ⟨r, hr⟩ ⟨s, hs'⟩ ⟨t, ht'⟩ ((compMul_eq_some hC).2 h)
    · have hs' : ¬ C (P.src s) := by rw [hs]; exact hC.compl.fwd r hr
      have ht' : ¬ C (P.src t) := by rw [ht]; exact hr
      simp only [dif_neg hr, dif_neg hs', dif_neg ht']
      exact hω2 ⟨r, hr⟩ ⟨s, hs'⟩ ⟨t, ht'⟩ ((compMul_eq_some hC.compl).2 h)
  · by_cases hr : C (P.src r)
    · simp only [dif_pos hr]; exact hw1 ⟨r, hr⟩
    · simp only [dif_neg hr]; exact hw2 ⟨r, hr⟩

open Classical in
/-- The quotient morphism `kT → kT_C` onto a union of components. -/
def compMor {C : V → Prop} (hC : P.Closed C) : Mor P.toMult (P.sub (compData hC)).toMult where
  f r := if h : C (P.src r) then some ⟨r, h⟩ else none
  hmul r s := by
    by_cases hr : C (P.src r)
    · by_cases hs : C (P.src s)
      · simp only [dif_pos hr, dif_pos hs, Option.bind_some]
        cases h : P.mul r s with
        | none =>
          simp only [Option.bind_none]
          cases h' : (P.sub (compData hC)).mul ⟨r, hr⟩ ⟨s, hs⟩ with
          | none => rfl
          | some t => exact absurd ((compMul_eq_some hC).1 h') (by rw [h]; exact fun h0 ↦ by cases h0)
        | some t =>
          have ht : C (P.src t) := by rw [P.mul_src _ _ _ h]; exact hr
          simp only [Option.bind_some, dif_pos ht]
          exact (compMul_eq_some hC (t := ⟨t, ht⟩)).2 h
      · simp only [dif_pos hr, dif_neg hs, Option.bind_some, Option.bind_none]
        cases h : P.mul r s with
        | none => rfl
        | some t =>
          exfalso; apply hs
          rw [← P.mul_mid r s t h]; exact hC.fwd r hr
    · simp only [dif_neg hr, Option.bind_none]
      cases h : P.mul r s with
      | none => rfl
      | some t =>
        have ht : ¬ C (P.src t) := by rw [P.mul_src _ _ _ h]; exact hr
        simp only [Option.bind_some, dif_neg ht]
  hid x := by
    by_cases hx : C x
    · right; exact ⟨⟨x, hx⟩, by simp only [P.src_e, dif_pos hx]; rfl⟩
    · left; simp only [P.src_e, dif_neg hx]
  hid' x' := ⟨x'.1, by simp only [P.src_e, dif_pos (show C x'.1 from x'.2)]; rfl, fun y hy ↦ by
    by_cases h : C y
    · simp only [P.src_e, dif_pos h, Option.some.injEq] at hy
      have h2 : P.e y = P.e x'.1 := congrArg Subtype.val hy
      rw [← P.src_e y, h2, P.src_e]
    · simp only [P.src_e, dif_neg h] at hy; cases hy⟩

open Classical in
theorem comp_isRepresentationFinite {C : V → Prop} (hC : P.Closed C) (k : Type u) [Field k]
    (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((P.sub (compData hC)).Lin k) :=
  (compMor hC).isRepresentationFinite k (fun r' ↦ ⟨r'.1, by
    simp only [compMor, dif_pos (show C (P.src r'.1) from r'.2)]⟩) h

/-- A connected table: every two vertices are joined by a zigzag of rays. -/
def Conn (P : Tab V R L) : Prop :=
  ∀ x y : V, Relation.EqvGen (fun x y ↦ ∃ r, P.src r = x ∧ P.tgt r = y) x y

/-- **A disconnected table splits along a component.** -/
theorem exists_split (hnc : ¬ P.Conn) :
    ∃ C : V → Prop, P.Closed C ∧ (∃ x, C x) ∧ ∃ x, ¬ C x := by
  unfold Conn at hnc
  push Not at hnc
  obtain ⟨x, y, hxy⟩ := hnc
  let rel := Relation.EqvGen (fun x y : V ↦ ∃ r, P.src r = x ∧ P.tgt r = y)
  refine ⟨rel x, ⟨fun r h ↦ ?_, fun r h ↦ ?_⟩, ⟨x, Relation.EqvGen.refl x⟩, ⟨y, hxy⟩⟩
  · exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ⟨r, rfl, rfl⟩)
  · exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨r, rfl, rfl⟩))

open Classical in
/-- **A proper union of components has fewer rays.** -/
theorem card_comp_lt {C : V → Prop} (hx : ∃ x, ¬ C x) :
    Fintype.card {r // C (P.src r)} < Fintype.card R := by
  obtain ⟨x, hx⟩ := hx
  exact Fintype.card_subtype_lt (p := fun r ↦ C (P.src r)) (x := P.e x) (by rw [P.src_e]; exact hx)

/-! ### The linearization of a representation-finite table -/

variable (P) (k : Type u) [Field k] [IsAlgClosed k]

/-- **The linearization of a ray table is basic.** -/
theorem isBasic_lin : IsBasicAlgebra (P.Lin k) := by
  classical
  set σ := Fintype.equivFin V
  refine ⟨Fintype.card V, fun i ↦ P.b k (P.e (σ.symm i)),
    (CompleteOrthogonalIdempotents.equiv σ.symm).2 (P.b_e_complete k),
    fun i ↦ P.b_e_primitive k _, fun i j hex ↦ ?_⟩
  obtain ⟨x, y, hx, hy, hxy, -⟩ := hex
  by_contra hij
  have hne : σ.symm i ≠ σ.symm j := fun h ↦ hij (σ.symm.injective h)
  have hxc : x ∈ P.corSp k (σ.symm i) (σ.symm j) := by
    rw [← hx]; exact P.e_mul_mul_e_mem k _ _ x
  have hxd : x ∈ P.degSp k 1 := by
    rw [P.mem_degSp_iff]
    intro r hr
    obtain ⟨e1, e2⟩ := (P.mem_corSp_iff k).1 hxc r hr
    have hre : r ≠ P.e (P.src r) := by
      intro h; apply hne; rw [← e1, ← e2, h, P.tgt_e, P.src_e]
    have := P.deg_pos r hre; omega
  have hall : y ∈ P.degSp k 0 := by
    rw [P.mem_degSp_iff]; intro r _; exact P.deg_nonneg r
  have hm := P.mul_mem_degSp k hxd hall
  rw [add_zero, hxy] at hm
  have := P.repr_e_of_mem_degSp k (x := σ.symm i) hm
  change (P.basis k).repr (P.b k (P.e (σ.symm i))) (P.e (σ.symm i)) = 0 at this
  rw [← Mult.basis_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
  exact one_ne_zero this

end Tab

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  (hfin : IsRepresentationFinite k (S.P.Lin k))

theorem coch_zero : S.coch k (0 : R → R → k) = 0 :=
  S.bilin_ext k fun u v ↦ by rw [coch_b, Pi.zero_apply, Pi.zero_apply, zero_smul]; rfl

theorem self_hΨ (a z : S.P.Lin k) :
    (LinearEquiv.refl k (S.P.Lin k)) (a * z + S.coch k 0 a z) =
      (LinearEquiv.refl k (S.P.Lin k)) a * (LinearEquiv.refl k (S.P.Lin k)) z := by
  simp [coch_zero]

/-- **A representation-finite ray table presents its own linearization** (Definition 3.9(3)). -/
theorem self_rayPres :
    (S.fibreIdem k hfin 0 (LinearEquiv.refl k _) (S.self_hΨ k)).IsRayPres (k := k) S.P.toMult
      (S.fibreIdx k hfin 0 (LinearEquiv.refl k _) (S.self_hΨ k)) (S.P.b k) :=
  S.fibre_rayPres k hfin 0 (LinearEquiv.refl k _) (S.self_hΨ k)

end Sys

end RaySys

end MultiplicativeBasisDeformations
