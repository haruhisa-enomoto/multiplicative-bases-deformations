module

public import MultiplicativeBasisDeformations.Foundations.GradedPreproj
public import MultiplicativeBasisDeformations.Foundations.StarCorner
public import MultiplicativeBasisDeformations.Foundations.TraceTypesAD
public import Mathlib.Tactic.IntervalCases

/-!
# Lemma A.7: closed paths of degree sixteen in `Π(E₇)`

`lem:e7-sixteen-return` (`periodic-mesh-calculations.tex`): "Every vertex
of `Π(E₇)` has a nonzero closed path of path degree sixteen, over every field.
… Thus `U_0, …, U_8` are nonnegative. The same recurrence gives `U_9 = U_7`. Its
reversibility implies `U_{8+j} = U_{8-j}` for `0 ≤ j ≤ 8`. In particular
`U_16 = I` and all preceding matrices are nonnegative. Apply (A.17)."

The matrices `U_d` are integer matrices determined by the recurrence; we list
them in a fixed labelling of the vertices and check the recurrence, the
nonnegativity and `U_16 = I` by direct computation.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace E7Return

/-- The adjacency matrix of `E₇` in the labelling: centre `0`; arm of length one
`1`; arm of length two `2, 3`; arm of length three `4, 5, 6`. -/
def A7 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 0]

/-- The matrices `U_0, …, U_16` of `E_7` in the labelling `e7`. -/
def Ulit : ℕ → Matrix (Fin 7) (Fin 7) ℤ
  | 0 => !![1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1]
  | 1 => !![0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 0]
  | 2 => !![2, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0, 0]
  | 3 => !![0, 1, 2, 0, 2, 0, 1; 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 0; 2, 0, 0, 1, 0, 1, 0; 0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0]
  | 4 => !![3, 0, 0, 1, 0, 2, 0; 0, 1, 1, 0, 1, 0, 1; 0, 1, 1, 0, 2, 0, 1; 1, 0, 0, 0, 0, 1, 0; 0, 1, 2, 0, 2, 0, 0; 2, 0, 0, 1, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0]
  | 5 => !![0, 2, 2, 0, 3, 0, 1; 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 1, 0, 2, 0; 0, 0, 1, 0, 1, 0, 1; 3, 0, 0, 1, 0, 1, 0; 0, 1, 2, 0, 1, 0, 0; 1, 0, 0, 1, 0, 0, 0]
  | 6 => !![4, 0, 0, 1, 0, 2, 0; 0, 1, 1, 0, 2, 0, 0; 0, 1, 2, 0, 2, 0, 1; 1, 0, 0, 1, 0, 1, 0; 0, 2, 2, 0, 2, 0, 1; 2, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0]
  | 7 => !![0, 2, 3, 0, 3, 0, 1; 2, 0, 0, 1, 0, 1, 0; 3, 0, 0, 1, 0, 1, 0; 0, 1, 1, 0, 1, 0, 0; 3, 0, 0, 1, 0, 2, 0; 0, 1, 1, 0, 2, 0, 1; 1, 0, 0, 0, 0, 1, 0]
  | 8 => !![4, 0, 0, 2, 0, 2, 0; 0, 1, 2, 0, 1, 0, 1; 0, 2, 2, 0, 2, 0, 0; 2, 0, 0, 0, 0, 0, 0; 0, 1, 2, 0, 3, 0, 1; 2, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 1, 0, 1]
  | 9 => !![0, 2, 3, 0, 3, 0, 1; 2, 0, 0, 1, 0, 1, 0; 3, 0, 0, 1, 0, 1, 0; 0, 1, 1, 0, 1, 0, 0; 3, 0, 0, 1, 0, 2, 0; 0, 1, 1, 0, 2, 0, 1; 1, 0, 0, 0, 0, 1, 0]
  | 10 => !![4, 0, 0, 1, 0, 2, 0; 0, 1, 1, 0, 2, 0, 0; 0, 1, 2, 0, 2, 0, 1; 1, 0, 0, 1, 0, 1, 0; 0, 2, 2, 0, 2, 0, 1; 2, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0]
  | 11 => !![0, 2, 2, 0, 3, 0, 1; 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 1, 0, 2, 0; 0, 0, 1, 0, 1, 0, 1; 3, 0, 0, 1, 0, 1, 0; 0, 1, 2, 0, 1, 0, 0; 1, 0, 0, 1, 0, 0, 0]
  | 12 => !![3, 0, 0, 1, 0, 2, 0; 0, 1, 1, 0, 1, 0, 1; 0, 1, 1, 0, 2, 0, 1; 1, 0, 0, 0, 0, 1, 0; 0, 1, 2, 0, 2, 0, 0; 2, 0, 0, 1, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0]
  | 13 => !![0, 1, 2, 0, 2, 0, 1; 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 0; 2, 0, 0, 1, 0, 1, 0; 0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0]
  | 14 => !![2, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0, 0]
  | 15 => !![0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 0]
  | 16 => !![1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1]
  | _ => 0

theorem U0 : UBound.U A7 0 = Ulit 0 := by rw [UBound.U]; decide

theorem U1 : UBound.U A7 1 = Ulit 1 := by rw [UBound.U]; decide

set_option maxRecDepth 100000 in
theorem U2 : UBound.U A7 2 = Ulit 2 := by
  show UBound.U A7 (0 + 2) = _
  rw [UBound.U, U1, U0]
  decide

set_option maxRecDepth 100000 in
theorem U3 : UBound.U A7 3 = Ulit 3 := by
  show UBound.U A7 (1 + 2) = _
  rw [UBound.U, U2, U1]
  decide

set_option maxRecDepth 100000 in
theorem U4 : UBound.U A7 4 = Ulit 4 := by
  show UBound.U A7 (2 + 2) = _
  rw [UBound.U, U3, U2]
  decide

set_option maxRecDepth 100000 in
theorem U5 : UBound.U A7 5 = Ulit 5 := by
  show UBound.U A7 (3 + 2) = _
  rw [UBound.U, U4, U3]
  decide

set_option maxRecDepth 100000 in
theorem U6 : UBound.U A7 6 = Ulit 6 := by
  show UBound.U A7 (4 + 2) = _
  rw [UBound.U, U5, U4]
  decide

set_option maxRecDepth 100000 in
theorem U7 : UBound.U A7 7 = Ulit 7 := by
  show UBound.U A7 (5 + 2) = _
  rw [UBound.U, U6, U5]
  decide

set_option maxRecDepth 100000 in
theorem U8 : UBound.U A7 8 = Ulit 8 := by
  show UBound.U A7 (6 + 2) = _
  rw [UBound.U, U7, U6]
  decide

set_option maxRecDepth 100000 in
theorem U9 : UBound.U A7 9 = Ulit 9 := by
  show UBound.U A7 (7 + 2) = _
  rw [UBound.U, U8, U7]
  decide

set_option maxRecDepth 100000 in
theorem U10 : UBound.U A7 10 = Ulit 10 := by
  show UBound.U A7 (8 + 2) = _
  rw [UBound.U, U9, U8]
  decide

set_option maxRecDepth 100000 in
theorem U11 : UBound.U A7 11 = Ulit 11 := by
  show UBound.U A7 (9 + 2) = _
  rw [UBound.U, U10, U9]
  decide

set_option maxRecDepth 100000 in
theorem U12 : UBound.U A7 12 = Ulit 12 := by
  show UBound.U A7 (10 + 2) = _
  rw [UBound.U, U11, U10]
  decide

set_option maxRecDepth 100000 in
theorem U13 : UBound.U A7 13 = Ulit 13 := by
  show UBound.U A7 (11 + 2) = _
  rw [UBound.U, U12, U11]
  decide

set_option maxRecDepth 100000 in
theorem U14 : UBound.U A7 14 = Ulit 14 := by
  show UBound.U A7 (12 + 2) = _
  rw [UBound.U, U13, U12]
  decide

set_option maxRecDepth 100000 in
theorem U15 : UBound.U A7 15 = Ulit 15 := by
  show UBound.U A7 (13 + 2) = _
  rw [UBound.U, U14, U13]
  decide

set_option maxRecDepth 100000 in
theorem U16 : UBound.U A7 16 = Ulit 16 := by
  show UBound.U A7 (14 + 2) = _
  rw [UBound.U, U15, U14]
  decide

theorem U_eq_Ulit : ∀ d ≤ 16, UBound.U A7 d = Ulit d := by
  intro d hd
  interval_cases d
  exacts [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16]

set_option maxRecDepth 100000 in
theorem Ulit_nonneg : ∀ d ≤ 16, ∀ a b, 0 ≤ Ulit d a b := by
  intro d hd
  interval_cases d <;> decide

theorem Ulit_16 : Ulit 16 = 1 := by decide

/-! ### The labelling of an `E₇` star -/

variable {L : Fin 3 → ℕ} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hLa : L a = 0) (hLb : L b = 1) (hLc : L c = 2)

include hLa hLb hLc in
/-- The vertices `0, …, 6` of the star. -/
def e7 : Fin 7 → StarV L :=
  ![none, some ⟨a, ⟨0, by omega⟩⟩, some ⟨b, ⟨0, by omega⟩⟩, some ⟨b, ⟨1, by omega⟩⟩,
    some ⟨c, ⟨0, by omega⟩⟩, some ⟨c, ⟨1, by omega⟩⟩, some ⟨c, ⟨2, by omega⟩⟩]

include hab hac hbc in
theorem e7_injective : Function.Injective (e7 hLa hLb hLc) := by
  intro n m h
  fin_cases n <;> fin_cases m <;> simp_all [e7, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

include hab hac hbc in
theorem e7_surjective : Function.Surjective (e7 hLa hLb hLc) := by
  rintro (_ | ⟨i, ⟨j, hj⟩⟩)
  · exact ⟨0, rfl⟩
  · rcases TraceAlg.fin_three_cases hab hac hbc i with rfl | rfl | rfl
    · obtain rfl : j = 0 := by omega
      exact ⟨1, rfl⟩
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩

/-- The labelling as an equivalence. -/
def E7eqv : Fin 7 ≃ (starTree L).Dbl :=
  Equiv.ofBijective (e7 hLa hLb hLc) ⟨e7_injective hab hac hbc hLa hLb hLc,
    e7_surjective hab hac hbc hLa hLb hLc⟩

include hab hac hbc in
theorem adjM_e7 (n m : Fin 7) :
    (starTree L).adjM (e7 hLa hLb hLc n) (e7 hLa hLb hLc m) = A7 n m := by
  classical
  simp only [OrientedTree.adjM, Matrix.of_apply]
  fin_cases n <;> fin_cases m <;>
    simp [e7, A7, starTree, starGraph, starAdj, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

theorem U_submatrix (d : ℕ) :
    (UBound.U (starTree L).adjM d).submatrix (E7eqv hab hac hbc hLa hLb hLc)
      (E7eqv hab hac hbc hLa hLb hLc) = UBound.U A7 d := by
  have hA : (starTree L).adjM.submatrix (E7eqv hab hac hbc hLa hLb hLc)
      (E7eqv hab hac hbc hLa hLb hLc) = A7 := by
    ext n m
    exact adjM_e7 hab hac hbc hLa hLb hLc n m
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      match d, ih with
      | 0, _ => simp [UBound.U]
      | 1, _ => exact hA
      | d + 2, ih =>
          rw [UBound.U, UBound.U, Matrix.submatrix_sub, Pi.sub_apply, Pi.sub_apply,
            ← Matrix.submatrix_mul_equiv _ _ _ (E7eqv hab hac hbc hLa hLb hLc), hA,
            ih (d + 1) (by omega), ih d (by omega)]

include hab hac hbc hLa hLb hLc in
/-- **Lemma A.7**: every vertex of `Π(E₇)` carries a closed path of degree
sixteen outside the ideal, over every field. -/
theorem e7_return {k : Type*} [Field k] (v : (starTree L).Dbl) :
    ∃ p : Quiver.Path v v, p.length = 16 ∧
      LinearPaths.path (k := k) p ∉ (starTree L).Id k v v := by
  set E := E7eqv hab hac hbc hLa hLb hLc
  have hU : ∀ d ≤ 16, ∀ x y : (starTree L).Dbl, 0 ≤ UBound.U (starTree L).adjM d x y := by
    intro d hd x y
    obtain ⟨n, rfl⟩ := E.surjective x
    obtain ⟨m, rfl⟩ := E.surjective y
    have := congrFun (congrFun (U_submatrix hab hac hbc hLa hLb hLc d) n) m
    rw [Matrix.submatrix_apply] at this
    rw [this, U_eq_Ulit d hd]
    exact Ulit_nonneg d hd n m
  have h16 : UBound.U (starTree L).adjM 16 v v = 1 := by
    obtain ⟨n, rfl⟩ := E.surjective v
    have := congrFun (congrFun (U_submatrix hab hac hbc hLa hLb hLc 16) n) n
    rw [Matrix.submatrix_apply] at this
    rw [this, U_eq_Ulit 16 le_rfl, Ulit_16, Matrix.one_apply_eq]
  have := OrientedTree.U_le_finrank (T := starTree L) (k := k) v 16 hU v
  rw [h16] at this
  exact OrientedTree.exists_path_of_finrank (by exact_mod_cast this)

end E7Return

end MultiplicativeBasisDeformations
