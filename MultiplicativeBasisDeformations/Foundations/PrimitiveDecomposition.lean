module

public import MultiplicativeBasisDeformations.Foundations.NormedBasis

/-!
# Complete sets of primitive orthogonal idempotents

Every idempotent of a finite-dimensional algebra is a sum of pairwise orthogonal
primitive idempotents: split a nonprimitive idempotent `f` as `g + (f - g)` with
`g` an idempotent of the corner `fAf`, and induct on `dim fA`. In particular a
finite-dimensional algebra has a complete set of primitive orthogonal
idempotents (`exists_primitive_decomposition`), as used in Lemma 2.1
(`graded-category.tex`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- The subspace `fA`. -/
def leftIdealSpace (f : A) : Submodule k A := LinearMap.range (LinearMap.mulLeft k f)

theorem mem_leftIdealSpace {f x : A} : x ∈ leftIdealSpace (k := k) f ↔ ∃ a, f * a = x :=
  Iff.rfl

theorem leftIdealSpace_lt {f g : A} (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (hfg : f * g = g) (hgf : g * f = g) (hne : g ≠ f) :
    leftIdealSpace (k := k) g < leftIdealSpace (k := k) f := by
  refine lt_of_le_of_ne (fun x ⟨a, ha⟩ ↦ ⟨g * a, ?_⟩) fun h ↦ hne ?_
  · change f * (g * a) = x
    rw [← mul_assoc, hfg]; exact ha
  · have hfm : f ∈ leftIdealSpace (k := k) f := ⟨f, hf.eq⟩
    rw [← h] at hfm
    obtain ⟨a, ha⟩ := hfm
    change g * a = f at ha
    have : g * f = f := by rw [← ha, ← mul_assoc, hg.eq]
    rw [← this, hgf]

/-- The data of a decomposition of `f` into orthogonal primitive idempotents. -/
def IsPrimDecomp (f : A) (l : List A) : Prop :=
  (∀ x ∈ l, IsPrimitiveIdempotent x ∧ f * x = x ∧ x * f = x) ∧
    l.Pairwise (fun x y ↦ x * y = 0 ∧ y * x = 0) ∧ l.sum = f

variable (k) in
include k in
theorem exists_primDecomp_aux : ∀ (d : ℕ) (f : A), IsIdempotentElem f →
    Module.finrank k (leftIdealSpace (k := k) f) = d → ∃ l : List A, IsPrimDecomp f l := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro f hf hd
  by_cases h0 : f = 0
  · exact ⟨[], fun x hx ↦ by simp at hx, List.Pairwise.nil, by simp [h0]⟩
  by_cases hp : IsPrimitiveIdempotent f
  · exact ⟨[f], fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨hp, hf.eq, hf.eq⟩,
      List.pairwise_singleton _ _, by simp⟩
  -- a nontrivial idempotent `g` of the corner
  obtain ⟨g, hg, hfg, hgf, hg0, hgf'⟩ : ∃ g : A, IsIdempotentElem g ∧ f * g = g ∧ g * f = g ∧
      g ≠ 0 ∧ g ≠ f := by
    by_contra hcon
    push Not at hcon
    exact hp ⟨hf, h0, fun g hg h1 h2 ↦ by
      by_cases hz : g = 0
      · exact Or.inl hz
      · exact Or.inr (hcon g hg h1 h2 hz)⟩
  set g' := f - g
  have hg' : IsIdempotentElem g' := by
    change (f - g) * (f - g) = f - g
    rw [sub_mul, mul_sub, mul_sub, hf.eq, hfg, hgf, hg.eq]; abel
  have hfg' : f * g' = g' := by
    change f * (f - g) = f - g; rw [mul_sub, hf.eq, hfg]
  have hg'f : g' * f = g' := by
    change (f - g) * f = f - g; rw [sub_mul, hf.eq, hgf]
  have hg'ne : g' ≠ f := fun h ↦ hg0 (by
    have : f - g = f := h
    rwa [sub_eq_self] at this)
  obtain ⟨l1, h1⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt
    (leftIdealSpace_lt hf hg hfg hgf hgf')) g hg rfl
  obtain ⟨l2, h2⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt
    (leftIdealSpace_lt hf hg' hfg' hg'f hg'ne)) g' hg' rfl
  refine ⟨l1 ++ l2, fun x hx ↦ ?_, ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨hpx, hgx, hxg⟩ := h1.1 x hx
      refine ⟨hpx, ?_, ?_⟩
      · rw [← hgx, ← mul_assoc, hfg]
      · rw [← hxg, mul_assoc, hgf]
    · obtain ⟨hpx, hgx, hxg⟩ := h2.1 x hx
      refine ⟨hpx, ?_, ?_⟩
      · rw [← hgx, ← mul_assoc, hfg']
      · rw [← hxg, mul_assoc, hg'f]
  · refine List.pairwise_append.2 ⟨h1.2.1, h2.2.1, fun x hx y hy ↦ ?_⟩
    obtain ⟨-, hgx, hxg⟩ := h1.1 x hx
    obtain ⟨-, hgy, hyg⟩ := h2.1 y hy
    have hgg' : g * g' = 0 := by
      change g * (f - g) = 0; rw [mul_sub, hgf, hg.eq, sub_self]
    have hg'g : g' * g = 0 := by
      change (f - g) * g = 0; rw [sub_mul, hfg, hg.eq, sub_self]
    constructor
    · rw [← hxg, ← hgy, mul_assoc, ← mul_assoc g, hgg', zero_mul, mul_zero]
    · rw [← hyg, ← hgx, mul_assoc, ← mul_assoc g', hg'g, zero_mul, mul_zero]
  · rw [List.sum_append, h1.2.2, h2.2.2]
    change g + (f - g) = f
    abel

variable (k A) in
include k in
/-- **A finite-dimensional algebra has a complete set of primitive orthogonal
idempotents.** -/
theorem exists_primitive_decomposition :
    ∃ (n : ℕ) (e : Fin n → A), CompleteOrthogonalIdempotents e ∧ ∀ i, IsPrimitiveIdempotent (e i) := by
  obtain ⟨l, hl⟩ := exists_primDecomp_aux k _ (1 : A) IsIdempotentElem.one rfl
  refine ⟨l.length, l.get, ⟨⟨fun i ↦ (hl.1 _ (List.get_mem l i)).1.1, fun i j hij ↦ ?_⟩, ?_⟩,
    fun i ↦ (hl.1 _ (List.get_mem l i)).1⟩
  · have hpw := List.pairwise_iff_get.1 hl.2.1
    rcases lt_or_gt_of_ne hij with h | h
    · exact (hpw i j h).1
    · exact (hpw j i h).2
  · rw [← List.sum_ofFn, List.ofFn_get]
    exact hl.2.2

end MultiplicativeBasisDeformations
