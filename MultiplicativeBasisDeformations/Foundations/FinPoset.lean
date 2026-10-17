import MultiplicativeBasisDeformations.Foundations.TreePoset
import MultiplicativeBasisDeformations.Foundations.SupportPoset
import MultiplicativeBasisDeformations.Foundations.CategoryAlgebraCorners

/-!
# Concrete finite posets and forbidden configurations

For the configurations excluded by Lemma 8.8 in Part III (four-point crowns, four-leaf stars,
the Euclidean trees of the table after `lem:dimension-infinity`): a poset on `Fin n` given by
a Boolean table (`Pos`), whose axioms, cover relation, uniqueness of lower covers
and dimension count are checked by `decide`. `forbidden` transfers the conclusion along an
order isomorphism, for the poset and its dual.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace PosetRep

universe u

/-- A poset on `Fin n` given by a table. -/
structure Pos (n : ℕ) (le : Fin n → Fin n → Bool) where
  v : Fin n
deriving DecidableEq

variable {n : ℕ} {le : Fin n → Fin n → Bool}

/-- The underlying vertices. -/
def posEquiv : Pos n le ≃ Fin n where
  toFun a := a.v
  invFun i := ⟨i⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Pos n le) := Fintype.ofEquiv (Fin n) posEquiv.symm

/-- The strict comparison of the table. -/
def ltB (le : Fin n → Fin n → Bool) (i j : Fin n) : Bool := le i j && i != j

/-- The cover relation of the table. -/
def covB (le : Fin n → Fin n → Bool) (i j : Fin n) : Bool :=
  ltB le i j && (Finset.univ.filter fun m ↦ ltB le i m && ltB le m j).card == 0

/-- The axioms of a partial order, checked on the table. -/
def Ax (le : Fin n → Fin n → Bool) : Prop :=
  (∀ i, le i i = true) ∧ (∀ i j m, le i j = true → le j m = true → le i m = true) ∧
    ∀ i j, le i j = true → le j i = true → i = j

variable [hA : Fact (Ax le)]

instance : PartialOrder (Pos n le) where
  le a b := le a.v b.v = true
  le_refl a := hA.out.1 a.v
  le_trans a b c := hA.out.2.1 a.v b.v c.v
  le_antisymm a b h1 h2 := by
    cases a; cases b; congr 1; exact hA.out.2.2 _ _ h1 h2

theorem pos_le_iff (a b : Pos n le) : a ≤ b ↔ le a.v b.v = true := Iff.rfl

instance : DecidableRel (α := Pos n le) (· ≤ ·) := fun a b ↦
  inferInstanceAs (Decidable (le a.v b.v = true))

theorem pos_lt_iff (a b : Pos n le) : a < b ↔ ltB le a.v b.v = true := by
  rw [lt_iff_le_and_ne, pos_le_iff]
  simp only [ltB, Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun he ↦ h2 (by cases a; cases b; simp_all)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun he ↦ h2 (he ▸ rfl)⟩

instance : DecidableRel (α := Pos n le) (· < ·) := fun a b ↦
  decidable_of_iff _ (pos_lt_iff a b).symm

instance : LocallyFiniteOrder (Pos n le) := Fintype.toLocallyFiniteOrder

theorem pos_covBy_iff (a b : Pos n le) : a ⋖ b ↔ covB le a.v b.v = true := by
  rw [CovBy, pos_lt_iff]
  simp only [covB, Bool.and_eq_true, beq_iff_eq, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm ↦ ?_⟩
    exact h2 (c := ⟨m⟩) ((pos_lt_iff _ _).2 hm.1) ((pos_lt_iff _ _).2 hm.2)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc1 hc2 ↦ h2 (x := c.v) ?_⟩
    exact ⟨(pos_lt_iff _ _).1 hc1, (pos_lt_iff _ _).1 hc2⟩

instance : DecidableRel (α := Pos n le) (· ⋖ ·) := fun a b ↦
  decidable_of_iff _ (pos_covBy_iff a b).symm

instance : DecidableRel (α := (Pos n le)ᵒᵈ) (· ⋖ ·) := fun a b ↦
  decidable_of_iff (OrderDual.ofDual b ⋖ OrderDual.ofDual a) ofDual_covBy_ofDual_iff

/-- Unique lower covers above a point, on the table. -/
def UniqOK (le : Fin n → Fin n → Bool) : Prop :=
  ∀ x y m m' : Fin n, le x m = true → covB le m y = true → le x m' = true → covB le m' y = true →
    m = m'

theorem pos_uniq (hu : UniqOK le) (x y : Pos n le) : Subsingleton (EPath (· ⋖ ·) x y) :=
  ⟨subsingleton_ePath_of_lowerCover fun x y m m' h1 h2 h3 h4 ↦ by
    have := hu x.v y.v m.v m'.v h1 ((pos_covBy_iff _ _).1 h2) h3 ((pos_covBy_iff _ _).1 h4)
    cases m; cases m'; simp_all⟩

/-- The dimension count on the table. -/
def CountOK (le : Fin n → Fin n → Bool) (d : Fin n → ℕ) : Prop :=
  (∃ i, 0 < d i) ∧
    ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, if covB le i j then d i * d j else 0

theorem pos_sq_eq (d : Fin n → ℕ) : ∑ v : Pos n le, d v.v ^ 2 = ∑ i, d i ^ 2 :=
  Fintype.sum_equiv posEquiv _ _ fun _ ↦ rfl

theorem pos_arr_eq (d : Fin n → ℕ) :
    ∑ a : Arr (P := Pos n le) (· ⋖ ·), d (tgt a).v * d (src a).v =
      ∑ i, ∑ j, if covB le i j then d i * d j else 0 := by
  rw [← Finset.sum_product', Finset.univ_product_univ]
  rw [← Fintype.sum_equiv (posEquiv.prodCongr posEquiv) (fun q : Pos n le × Pos n le ↦
    if covB le q.1.v q.2.v then d q.1.v * d q.2.v else 0) _ fun _ ↦ rfl]
  rw [← Finset.sum_filter]
  refine ((Finset.sum_subtype (p := fun q : Pos n le × Pos n le ↦ q.1 ⋖ q.2)
    (F := inferInstanceAs (Fintype (Arr (P := Pos n le) (· ⋖ ·)))) _
    (fun q ↦ ?_) _).trans ?_).symm
  · simp [pos_covBy_iff]
  · exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

theorem pos_count (d : Fin n → ℕ) (hc : CountOK le d) :
    ∑ v : Pos n le, d v.v ^ 2 ≤ ∑ a : Arr (P := Pos n le) (· ⋖ ·), d (tgt a).v * d (src a).v := by
  have e1 : ∑ v : Pos n le, d v.v ^ 2 = ∑ i, d i ^ 2 :=
    Fintype.sum_equiv posEquiv _ _ fun _ ↦ rfl
  have e2 : ∑ a : Arr (P := Pos n le) (· ⋖ ·), d (tgt a).v * d (src a).v =
      ∑ i, ∑ j, if covB le i j then d i * d j else 0 := by
    rw [← Finset.sum_product', Finset.univ_product_univ]
    rw [← Fintype.sum_equiv (posEquiv.prodCongr posEquiv) (fun q : Pos n le × Pos n le ↦
      if covB le q.1.v q.2.v then d q.1.v * d q.2.v else 0) _ fun _ ↦ rfl]
    rw [← Finset.sum_filter]
    refine ((Finset.sum_subtype (p := fun q : Pos n le × Pos n le ↦ q.1 ⋖ q.2)
      (F := inferInstanceAs (Fintype (Arr (P := Pos n le) (· ⋖ ·)))) _
      (fun q ↦ ?_) _).trans ?_).symm
    · simp [pos_covBy_iff]
    · exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  rw [e1, e2]; exact hc.2

/-- **Forbidden configurations**: a poset isomorphic to a table poset with unique lower
covers whose dimension count holds has representation-infinite incidence algebra. -/
theorem forbidden (k : Type u) [Field k] [IsAlgClosed k] {Q : Type} [PartialOrder Q] [Fintype Q]
    [DecidableEq Q] [LocallyFiniteOrder Q] (e : Pos n le ≃o Q) (d : Fin n → ℕ) (hu : UniqOK le)
    (hc : CountOK le d) : ¬ IsRepresentationFinite k (IncidenceAlgebra k Q) := by
  have h0 := not_isRepresentationFinite (k := k) (P := Pos n le) (fun v ↦ d v.v) covBy_lt
    (pos_uniq hu) nonempty_ePath (by obtain ⟨i, hi⟩ := hc.1; exact ⟨⟨i⟩, hi⟩) (pos_count d hc)
  have := incidence_finiteDimensional (k := k) (P := Q)
  have := incidence_finiteDimensional (k := k) (P := Pos n le)
  exact fun h ↦ h0 (isRepresentationFinite_of_algEquiv (incidenceEquiv e).symm h)

/-! ### Transposed tables -/

instance : Fact (Ax (flip le)) :=
  ⟨⟨fun i ↦ hA.out.1 i, fun i j m h1 h2 ↦ hA.out.2.1 m j i h2 h1,
    fun i j h1 h2 ↦ hA.out.2.2 i j h2 h1⟩⟩

/-- The transposed table is the dual poset. -/
def flipIso : Pos n (flip le) ≃o (Pos n le)ᵒᵈ where
  toFun a := OrderDual.toDual ⟨a.v⟩
  invFun a := ⟨(OrderDual.ofDual a).v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **Forbidden configurations, dual form.** -/
theorem forbidden_dual (k : Type u) [Field k] [IsAlgClosed k] {Q : Type} [PartialOrder Q]
    [Fintype Q] [DecidableEq Q] [LocallyFiniteOrder Q] (e : Pos n le ≃o Q) (d : Fin n → ℕ)
    (hu : UniqOK (flip le)) (hc : CountOK (flip le) d) :
    ¬ IsRepresentationFinite k (IncidenceAlgebra k Qᵒᵈ) :=
  forbidden k (flipIso.trans e.dual) d hu hc

end PosetRep

end MultiplicativeBasisDeformations
