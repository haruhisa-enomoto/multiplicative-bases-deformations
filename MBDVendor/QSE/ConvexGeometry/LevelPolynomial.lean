module

public import Mathlib.RingTheory.Polynomial.Basic
public import MBDVendor.QSE.ConvexGeometry.ClosedSets

/-!
# Level generating polynomials

For a closure operator on a finite ground type, the manuscript records the
number of closed sets at each cardinality level in a polynomial.  This file
defines that invariant independently of the later module-theoretic
instantiations.
-/

@[expose] public section

open Polynomial Set

namespace MBDVendor.QSE.SetClosure

variable {E : Type*}

/-- The number of closed sets having cardinality `n`. -/
noncomputable def levelCount [Finite E]
    (c : SetClosure E) (n : ℕ) : ℕ :=
  {C : c.Closeds | (C : Set E).ncard = n}.ncard

/-- The cardinality generating polynomial of the closed-set lattice. -/
noncomputable def levelPolynomial [Finite E]
    (c : SetClosure E) : ℕ[X] := by
  letI := Fintype.ofFinite c.Closeds
  exact ∑ C : c.Closeds, X ^ (C : Set E).ncard

/-- The coefficient of `X ^ n` is the number of closed sets at level
`n`. -/
@[simp]
theorem levelPolynomial_coeff [Finite E]
    (c : SetClosure E) (n : ℕ) :
    c.levelPolynomial.coeff n = c.levelCount n := by
  classical
  letI := Fintype.ofFinite c.Closeds
  simp only [levelPolynomial, levelCount, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow, Finset.sum_boole]
  rw [Set.ncard_eq_toFinset_card']
  change
    (Finset.univ.filter fun C : c.Closeds =>
      n = (C : Set E).ncard).card =
    (Set.toFinset {C : c.Closeds |
      (C : Set E).ncard = n}).card
  apply congrArg Finset.card
  ext C
  simp [eq_comm]

/-- Evaluating the level polynomial at one counts all closed sets. -/
@[simp]
theorem levelPolynomial_eval_one [Finite E]
    (c : SetClosure E) :
    c.levelPolynomial.eval 1 = Nat.card c.Closeds := by
  classical
  letI := Fintype.ofFinite c.Closeds
  simp [levelPolynomial, Polynomial.eval_finsetSum,
    Nat.card_eq_fintype_card]

/-- Equality of level polynomials is equivalent to equality at every
cardinality level. -/
theorem levelPolynomial_eq_iff [Finite E]
    (c d : SetClosure E) :
    c.levelPolynomial = d.levelPolynomial ↔
      ∀ n : ℕ, c.levelCount n = d.levelCount n := by
  constructor
  · intro h n
    rw [← levelPolynomial_coeff, h, levelPolynomial_coeff]
  · intro h
    ext n
    simpa using h n

/-- Enumerating the closed sets by a finite type rewrites the level
polynomial as the corresponding cardinality sum. -/
theorem levelPolynomial_eq_sum_equiv
    [Finite E] {W : Type*} [Fintype W]
    (c : SetClosure E) (e : W ≃ c.Closeds) :
    c.levelPolynomial =
      ∑ w : W, X ^ ((e w : c.Closeds) : Set E).ncard := by
  classical
  letI := Fintype.ofFinite c.Closeds
  unfold levelPolynomial
  symm
  apply Fintype.sum_equiv e
  intro w
  rfl

/-- If the enumerating parameter carries an explicit size statistic, that
statistic is the exponent in the level polynomial. -/
theorem levelPolynomial_eq_sum_stat
    [Finite E] {W : Type*} [Fintype W]
    (c : SetClosure E) (e : W ≃ c.Closeds)
    (stat : W → ℕ)
    (hstat : ∀ w, ((e w : c.Closeds) : Set E).ncard = stat w) :
    c.levelPolynomial = ∑ w : W, X ^ stat w := by
  rw [levelPolynomial_eq_sum_equiv c e]
  congr 1
  funext w
  rw [hstat w]

/-- No subset of a finite ground type can occur above its cardinality. -/
theorem levelCount_eq_zero_of_card_lt
    [Finite E] (c : SetClosure E)
    {n : ℕ} (hn : Nat.card E < n) :
    c.levelCount n = 0 := by
  classical
  rw [levelCount, Set.ncard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro C hC
  change (C : Set E).ncard = n at hC
  have hle : (C : Set E).ncard ≤ Nat.card E := by
    simpa [Set.ncard_univ] using
      Set.ncard_le_ncard (Set.subset_univ (C : Set E))
        (Set.finite_univ : (Set.univ : Set E).Finite)
  omega

/-- Equality through the bottom and top four levels determines the entire
level polynomial when the ground set has at most nine elements. -/
theorem levelPolynomial_eq_of_bottom_top_four
    [Finite E] (c d : SetClosure E)
    (hcard : Nat.card E ≤ 9)
    (hbottom : ∀ i ≤ 4, c.levelCount i = d.levelCount i)
    (htop : ∀ i ≤ 4,
      c.levelCount (Nat.card E - i) =
        d.levelCount (Nat.card E - i)) :
    c.levelPolynomial = d.levelPolynomial := by
  rw [levelPolynomial_eq_iff]
  intro n
  by_cases hn4 : n ≤ 4
  · exact hbottom n hn4
  by_cases hnE : n ≤ Nat.card E
  · let i := Nat.card E - n
    have hi : i ≤ 4 := by
      dsimp only [i]
      omega
    have hrecover : Nat.card E - i = n := by
      dsimp only [i]
      omega
    simpa only [hrecover] using htop i hi
  · have hlt : Nat.card E < n := Nat.lt_of_not_ge hnE
    rw [levelCount_eq_zero_of_card_lt c hlt,
      levelCount_eq_zero_of_card_lt d hlt]

end MBDVendor.QSE.SetClosure
