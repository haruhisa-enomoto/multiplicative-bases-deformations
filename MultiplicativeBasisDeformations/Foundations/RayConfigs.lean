import MultiplicativeBasisDeformations.Foundations.RaySetting

/-!
# Forbidden configurations in faithful supports

`def:faithful-support` with Lemma 8.8: if finitely many rays from `x` (or into `x`) have a
factorization order isomorphic to a table poset that passes the `decide` checks of
`FinPoset` (unique lower covers and the dimension count), finite representation type is
contradicted. The axioms of the table poset follow from those of the factorization order.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)

open PosetRep

/-- The axioms of a table read off a factorization order. -/
theorem ax_of_rf {n : ℕ} {le : Fin n → Fin n → Bool} (r : Fin n → R)
    (hr : Function.Injective r) (hle : ∀ i j, le i j = true ↔ P.RF (r i) (r j)) : Ax le :=
  ⟨fun i ↦ (hle i i).2 (P.rf_refl _), fun i j m h1 h2 ↦
    (hle i m).2 (P.rf_trans ((hle i j).1 h1) ((hle j m).1 h2)),
    fun i j h1 h2 ↦ hr (P.rf_antisymm ((hle i j).1 h1) ((hle j i).1 h2))⟩

theorem ax_of_lf {n : ℕ} {le : Fin n → Fin n → Bool} (r : Fin n → R)
    (hr : Function.Injective r) (hle : ∀ i j, le i j = true ↔ P.LF (r i) (r j)) : Ax le :=
  ⟨fun i ↦ (hle i i).2 (P.lf_refl _), fun i j m h1 h2 ↦
    (hle i m).2 (P.lf_trans ((hle i j).1 h1) ((hle j m).1 h2)),
    fun i j h1 h2 ↦ hr (P.lf_antisymm ((hle i j).1 h1) ((hle j i).1 h2))⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **A forbidden configuration in a faithful projective support.** -/
theorem projSup_false (hfin : IsRepresentationFinite k (P.Lin k)) {n : ℕ}
    {le : Fin n → Fin n → Bool} (x : V) (r : Fin n → R) (hr : Function.Injective r)
    (hsrc : ∀ i, P.src (r i) = x) (hle : ∀ i j, le i j = true ↔ P.RF (r i) (r j))
    (d : Fin n → ℕ) (hu : UniqOK le) (hc : CountOK le d) : False := by
  classical
  have : Fact (Ax le) := ⟨P.ax_of_rf r hr hle⟩
  set T := Finset.univ.image r
  have hT : ∀ s ∈ T, P.src s = x := fun s hs ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs; exact hsrc i
  have hmem : ∀ a : P.ProjSup T, ∃ i, r i = a.ray := fun a ↦ by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 a.ray_mem; exact ⟨i, hi⟩
  let e : Pos n le ≃o P.ProjSup T :=
    { toFun := fun i ↦ ProjSup.mk (r i.v) (Finset.mem_image_of_mem r (Finset.mem_univ _))
      invFun := fun a ↦ ⟨(hmem a).choose⟩
      left_inv := fun i ↦ by
        obtain ⟨v⟩ := i
        have h := (hmem (ProjSup.mk (P := P) (T := T) (r v)
          (Finset.mem_image_of_mem r (Finset.mem_univ _)))).choose_spec
        simp only [ProjSup.ray_mk] at h
        exact congrArg Pos.mk (hr h)
      right_inv := fun a ↦ ProjSup.ext (by simpa using (hmem a).choose_spec)
      map_rel_iff' := fun {i j} ↦ by
        change P.RF (r i.v) (r j.v) ↔ le i.v j.v = true
        exact (hle _ _).symm }
  exact inc_forbidden k e d hu hc (P.projSup_isRepresentationFinite T hT k hfin)

/-- **A forbidden configuration in a faithful injective support** (order: `r ≤ s` if
`r = v s`). -/
theorem injSup_false (hfin : IsRepresentationFinite k (P.Lin k)) {n : ℕ}
    {le : Fin n → Fin n → Bool} (x : V) (r : Fin n → R) (hr : Function.Injective r)
    (htgt : ∀ i, P.tgt (r i) = x) (hle : ∀ i j, le i j = true ↔ P.LF (r i) (r j))
    (d : Fin n → ℕ) (hu : UniqOK le) (hc : CountOK le d) : False := by
  classical
  have : Fact (Ax le) := ⟨P.ax_of_lf r hr hle⟩
  set T := Finset.univ.image r
  have hT : ∀ s ∈ T, P.tgt s = x := fun s hs ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs; exact htgt i
  have hmem : ∀ a : P.InjSup T, ∃ i, r i = a.ray := fun a ↦ by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 a.ray_mem; exact ⟨i, hi⟩
  let e : Pos n le ≃o P.InjSup T :=
    { toFun := fun i ↦ InjSup.mk (r i.v) (Finset.mem_image_of_mem r (Finset.mem_univ _))
      invFun := fun a ↦ ⟨(hmem a).choose⟩
      left_inv := fun i ↦ by
        obtain ⟨v⟩ := i
        have h := (hmem (InjSup.mk (P := P) (T := T) (r v)
          (Finset.mem_image_of_mem r (Finset.mem_univ _)))).choose_spec
        simp only [InjSup.ray_mk] at h
        exact congrArg Pos.mk (hr h)
      right_inv := fun a ↦ InjSup.ext (by simpa using (hmem a).choose_spec)
      map_rel_iff' := fun {i j} ↦ by
        change P.LF (r i.v) (r j.v) ↔ le i.v j.v = true
        exact (hle _ _).symm }
  exact inc_forbidden k e d hu hc (P.injSup_isRepresentationFinite T hT k hfin)

/-- The four-point crown: lower points `0, 1`, upper points `2, 3`, all four comparisons. -/
def tCrown : Fin 4 → Fin 4 → Bool := fun i j ↦ i == j || (i.val < 2 && 2 ≤ j.val)

theorem tCrown_uniq : UniqOK tCrown := by unfold UniqOK; decide

theorem tCrown_count : CountOK tCrown ![1, 1, 1, 1] := by unfold CountOK; decide

/-- **A four-point crown in a faithful projective support is excluded.** -/
theorem crown_false (hfin : IsRepresentationFinite k (P.Lin k)) (x : V) (l1 l2 u1 u2 : R)
    (hsrc : P.src l1 = x ∧ P.src l2 = x ∧ P.src u1 = x ∧ P.src u2 = x)
    (h11 : P.RF l1 u1) (h12 : P.RF l1 u2) (h21 : P.RF l2 u1) (h22 : P.RF l2 u2)
    (n1 : ¬ P.RF l1 l2) (n2 : ¬ P.RF l2 l1) (n3 : ¬ P.RF u1 u2) (n4 : ¬ P.RF u2 u1)
    (n5 : ¬ P.RF u1 l1) (n6 : ¬ P.RF u1 l2) (n7 : ¬ P.RF u2 l1) (n8 : ¬ P.RF u2 l2) : False := by
  set r : Fin 4 → R := ![l1, l2, u1, u2] with hr
  have hle : ∀ i j, tCrown i j = true ↔ P.RF (r i) (r j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [tCrown, r] <;>
      first | exact P.rf_refl _ | assumption | skip
  have hanti : ∀ i j : Fin 4, tCrown i j = true → tCrown j i = true → i = j := by decide
  have hinj : Function.Injective r := fun i j hij ↦ hanti i j
    ((hle i j).2 (by rw [hij]; exact P.rf_refl _)) ((hle j i).2 (by rw [hij]; exact P.rf_refl _))
  refine P.projSup_false k hfin x r hinj (fun i ↦ ?_) hle ![1, 1, 1, 1] tCrown_uniq tCrown_count
  fin_cases i
  · exact hsrc.1
  · exact hsrc.2.1
  · exact hsrc.2.2.1
  · exact hsrc.2.2.2

/-- The four-leaf star `0 → 1 → 2, 3, 4`. -/
def tStar4 : Fin 5 → Fin 5 → Bool := fun i j ↦ i == j || i.val == 0 || (i.val == 1 && 1 ≤ j.val)

theorem tStar4_uniq : UniqOK tStar4 := by unfold UniqOK; decide

theorem tStar4_count : CountOK tStar4 ![1, 2, 1, 1, 1] := by unfold CountOK; decide

/-- **A four-leaf star `p₀ → p₁ → l₁, l₂, l₃` in a faithful projective support is excluded.** -/
theorem star4_false (hfin : IsRepresentationFinite k (P.Lin k)) (x : V) (p0 p1 l1 l2 l3 : R)
    (hsrc : P.src p0 = x ∧ P.src p1 = x ∧ P.src l1 = x ∧ P.src l2 = x ∧ P.src l3 = x)
    (h01 : P.RF p0 p1) (h1 : P.RF p1 l1) (h2 : P.RF p1 l2) (h3 : P.RF p1 l3)
    (n10 : ¬ P.RF p1 p0) (n1 : ∀ l ∈ [l1, l2, l3], ¬ P.RF l p0 ∧ ¬ P.RF l p1)
    (n12 : ¬ P.RF l1 l2) (n13 : ¬ P.RF l1 l3) (n21 : ¬ P.RF l2 l1) (n23 : ¬ P.RF l2 l3)
    (n31 : ¬ P.RF l3 l1) (n32 : ¬ P.RF l3 l2) : False := by
  set r : Fin 5 → R := ![p0, p1, l1, l2, l3] with hr
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at n1
  obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := n1
  have hle : ∀ i j, tStar4 i j = true ↔ P.RF (r i) (r j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [tStar4, r] <;>
      first | exact P.rf_refl _ | assumption | exact P.rf_trans h01 ‹_› | skip
  have hanti : ∀ i j : Fin 5, tStar4 i j = true → tStar4 j i = true → i = j := by decide
  have hinj : Function.Injective r := fun i j hij ↦ hanti i j
    ((hle i j).2 (by rw [hij]; exact P.rf_refl _)) ((hle j i).2 (by rw [hij]; exact P.rf_refl _))
  refine P.projSup_false k hfin x r hinj (fun i ↦ ?_) hle ![1, 2, 1, 1, 1] tStar4_uniq
    tStar4_count
  fin_cases i
  · exact hsrc.1
  · exact hsrc.2.1
  · exact hsrc.2.2.1
  · exact hsrc.2.2.2.1
  · exact hsrc.2.2.2.2

/-- The six-point tree `0 → 1, 2, 3` and `1 → 4, 5` (two adjacent trivalent points). -/
def tSix : Fin 6 → Fin 6 → Bool := fun i j ↦
  i == j || i.val == 0 || (i.val == 1 && (j.val == 4 || j.val == 5))

theorem tSix_uniq : UniqOK tSix := by unfold UniqOK; decide

theorem tSix_count : CountOK tSix ![2, 2, 1, 1, 1, 1] := by unfold CountOK; decide

/-- **The six-point tree in a faithful projective support is excluded.** -/
theorem six_false (hfin : IsRepresentationFinite k (P.Lin k)) (x : V) (r : Fin 6 → R)
    (hsrc : ∀ i, P.src (r i) = x) (hpos : ∀ i j, tSix i j = true → P.RF (r i) (r j))
    (hneg : ∀ i j, tSix i j = false → ¬ P.RF (r i) (r j)) : False := by
  have hle : ∀ i j, tSix i j = true ↔ P.RF (r i) (r j) := fun i j ↦
    ⟨hpos i j, fun h ↦ by by_contra h'; exact hneg i j (by simpa using h') h⟩
  have hanti : ∀ i j : Fin 6, tSix i j = true → tSix j i = true → i = j := by decide
  have hinj : Function.Injective r := fun i j hij ↦ hanti i j
    ((hle i j).2 (by rw [hij]; exact P.rf_refl _)) ((hle j i).2 (by rw [hij]; exact P.rf_refl _))
  exact P.projSup_false k hfin x r hinj hsrc hle ![2, 2, 1, 1, 1, 1] tSix_uniq tSix_count

/-- A table configuration in a faithful projective support, given by positive and negative
comparisons. -/
theorem table_supp_false (hfin : IsRepresentationFinite k (P.Lin k)) {n : ℕ}
    (le : Fin n → Fin n → Bool) (x : V) (r : Fin n → R) (d : Fin n → ℕ) (hu : UniqOK le)
    (hc : CountOK le d) (hanti : ∀ i j, le i j = true → le j i = true → i = j)
    (hsrc : ∀ i, P.src (r i) = x) (hpos : ∀ i j, le i j = true → P.RF (r i) (r j))
    (hneg : ∀ i j, le i j = false → ¬ P.RF (r i) (r j)) : False := by
  have hle : ∀ i j, le i j = true ↔ P.RF (r i) (r j) := fun i j ↦
    ⟨hpos i j, fun h ↦ by by_contra h'; exact hneg i j (by simpa using h') h⟩
  have hinj : Function.Injective r := fun i j hij ↦ hanti i j
    ((hle i j).2 (by rw [hij]; exact P.rf_refl _)) ((hle j i).2 (by rw [hij]; exact P.rf_refl _))
  exact P.projSup_false k hfin x r hinj hsrc hle d hu hc

/-- The chain `Q₀ → Q₁ → Q₂ → Q₃` with leaves `Q₁ → Y₁`, `Q₂ → Y₂` (indices `4, 5`). -/
def tL6 : Fin 6 → Fin 6 → Bool := fun i j ↦
  i == j || (i.val ≤ 3 && j.val ≤ 3 && i.val ≤ j.val) || (j.val == 4 && i.val ≤ 1) ||
    (j.val == 5 && i.val ≤ 2)

theorem tL6_uniq : UniqOK tL6 := by unfold UniqOK; decide

theorem tL6_count : CountOK tL6 ![1, 2, 2, 1, 1, 1] := by unfold CountOK; decide

theorem tL6_anti : ∀ i j, tL6 i j = true → tL6 j i = true → i = j := by decide

end Tab

end RaySys

end MultiplicativeBasisDeformations
