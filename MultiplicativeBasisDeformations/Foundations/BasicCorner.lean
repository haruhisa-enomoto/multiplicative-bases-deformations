module

public import MultiplicativeBasisDeformations.Foundations.PrimitiveDecomposition
public import MultiplicativeBasisDeformations.Foundations.CornerRadical

/-!
# The basic algebra as a full corner

Lemma 2.1 (`graded-category.tex`) works with "the basic algebra `B₀ = eAe`
of `A`, where `e = e_1 + ⋯ + e_n` is a sum of primitive orthogonal idempotents,
one from each isomorphism class of indecomposable projectives". Here: take a
complete set `f_s` of primitive orthogonal idempotents, one representative `f_r`
in each class of `f_s A ≅ f_t A`, and `e = Σ f_r`. Then `AeA = A`
(`full_basicCorner`) and `eAe` is basic (`isBasicAlgebra_basicCorner`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace BasicCorner

open Classical

variable {A : Type v} [Ring A]

/-- `aA ≅ bA`, by elements `x ∈ aAb`, `y ∈ bAa` with `xy = a`, `yx = b`. -/
def IsoData (a b : A) : Prop :=
  ∃ x y : A, a * x * b = x ∧ b * y * a = y ∧ x * y = a ∧ y * x = b

theorem isoData_refl {a : A} (ha : IsIdempotentElem a) : IsoData a a :=
  ⟨a, a, by rw [ha.eq, ha.eq], by rw [ha.eq, ha.eq], ha.eq, ha.eq⟩

theorem IsoData.symm {a b : A} (h : IsoData a b) : IsoData b a := by
  obtain ⟨x, y, h1, h2, h3, h4⟩ := h
  exact ⟨y, x, h2, h1, h4, h3⟩

theorem left_of_sandwich {a b x : A} (ha : IsIdempotentElem a) (h : a * x * b = x) : a * x = x := by
  rw [← h, ← mul_assoc, ← mul_assoc, ha.eq]

theorem right_of_sandwich {a b x : A} (hb : IsIdempotentElem b) (h : a * x * b = x) : x * b = x := by
  rw [← h, mul_assoc, hb.eq]

theorem IsoData.trans {a b c : A} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hc : IsIdempotentElem c) (h : IsoData a b) (h' : IsoData b c) : IsoData a c := by
  obtain ⟨x, y, h1, h2, h3, h4⟩ := h
  obtain ⟨x', y', h1', h2', h3', h4'⟩ := h'
  refine ⟨x * x', y' * y, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, left_of_sandwich ha h1, mul_assoc, right_of_sandwich hc h1']
  · rw [← mul_assoc, left_of_sandwich hc h2', mul_assoc, right_of_sandwich ha h2]
  · calc x * x' * (y' * y) = x * (x' * y') * y := by simp only [mul_assoc]
      _ = a := by rw [h3', right_of_sandwich hb h1, h3]
  · calc y' * y * (x * x') = y' * (y * x) * x' := by simp only [mul_assoc]
      _ = c := by rw [h4, right_of_sandwich hb h2', h4']

variable {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A] {n : ℕ} {f : Fin n → A}
  (hf : CompleteOrthogonalIdempotents f)

/-- The representative of the class of `f_s`: the least `t` with `f_t A ≅ f_s A`. -/
def rep (s : Fin n) : Fin n :=
  (Finset.univ.filter fun t ↦ IsoData (f t) (f s)).min' ⟨s, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact isoData_refl (hf.idem s)⟩

include hf in
theorem rep_spec (s : Fin n) : IsoData (f (rep hf s)) (f s) := by
  have := Finset.min'_mem (Finset.univ.filter fun t ↦ IsoData (f t) (f s)) ⟨s, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact isoData_refl (hf.idem s)⟩
  exact (Finset.mem_filter.1 this).2

include hf in
theorem rep_eq {s t : Fin n} (h : IsoData (f s) (f t)) : rep hf s = rep hf t := by
  have : (Finset.univ.filter fun r ↦ IsoData (f r) (f s)) =
      Finset.univ.filter fun r ↦ IsoData (f r) (f t) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hr ↦ hr.trans (hf.idem r) (hf.idem s) (hf.idem t) h,
      fun hr ↦ hr.trans (hf.idem r) (hf.idem t) (hf.idem s) h.symm⟩
  simp only [rep, this]

include hf in
theorem rep_rep (s : Fin n) : rep hf (rep hf s) = rep hf s :=
  rep_eq hf (rep_spec hf s)

/-- The representatives. -/
def reps : Finset (Fin n) := Finset.univ.image (rep hf)

/-- `e = Σ_{r} f_r`. -/
def eB : A := ∑ r ∈ reps hf, f r

include hf in
theorem eB_idem : IsIdempotentElem (eB hf) := hf.toOrthogonalIdempotents.isIdempotentElem_sum

include hf in
theorem f_mul_eB {r : Fin n} (hr : r ∈ reps hf) : f r * eB hf = f r :=
  hf.toOrthogonalIdempotents.mul_sum_of_mem hr

include hf in
theorem eB_mul_f {r : Fin n} (hr : r ∈ reps hf) : eB hf * f r = f r := by
  unfold eB
  rw [Finset.sum_mul, Finset.sum_eq_single r (fun t _ htr ↦ hf.ortho htr) (fun h ↦ absurd hr h),
    (hf.idem r).eq]

include hf in
/-- **`AeA = A`.** -/
theorem full_eB (a : A) : a ∈ Submodule.span k {x | ∃ p q : A, x = p * eB hf * q} := by
  have ha : a = ∑ t, f t * a := by rw [← Finset.sum_mul, hf.complete, one_mul]
  rw [ha]
  refine Submodule.sum_mem _ fun t _ ↦ Submodule.subset_span ?_
  obtain ⟨x, y, h1, -, h3, -⟩ := (rep_spec hf t).symm
  have hr : rep hf t ∈ reps hf := Finset.mem_image_of_mem _ (Finset.mem_univ t)
  refine ⟨x * f (rep hf t), y * a, ?_⟩
  rw [mul_assoc x, f_mul_eB hf hr, right_of_sandwich (hf.idem _) h1, ← mul_assoc, h3]

include hf in
theorem rep_of_mem {r : Fin n} (hr : r ∈ reps hf) : rep hf r = r := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hr
  exact rep_rep hf s

/-- The idempotents `f_r` of the corner `eAe`. -/
def gB (j : Fin (reps hf).card) : (eB_idem hf).Corner :=
  cornerMk (eB_idem hf) (f ((reps hf).equivFin.symm j).1)
    ((Subsemigroup.mem_corner_iff (eB_idem hf)).2
      ⟨eB_mul_f hf ((reps hf).equivFin.symm j).2, f_mul_eB hf ((reps hf).equivFin.symm j).2⟩)

theorem gB_val (j : Fin (reps hf).card) :
    cornerVal (eB_idem hf) (gB hf j) = f ((reps hf).equivFin.symm j).1 := rfl

variable (k) in
include k in
theorem gB_complete : CompleteOrthogonalIdempotents (gB hf) := by
  refine ⟨⟨fun j ↦ corner_ext _ ?_, fun i j hij ↦ corner_ext _ ?_⟩, corner_ext _ ?_⟩
  · rw [corner_mul_val, gB_val]; exact (hf.idem _).eq
  · rw [corner_mul_val, gB_val, gB_val, corner_zero_val]
    refine hf.ortho fun h ↦ hij ?_
    exact (reps hf).equivFin.symm.injective (Subtype.ext h)
  · rw [← cornerValL_apply (k := k), map_sum, corner_one_val]
    simp_rw [cornerValL_apply, gB_val]
    rw [Equiv.sum_comp (reps hf).equivFin.symm (fun r ↦ f r.1),
      Finset.sum_coe_sort (reps hf) f]
    rfl

variable (k) in
include k in
theorem gB_primitive (hprim : ∀ s, IsPrimitiveIdempotent (f s)) (j : Fin (reps hf).card) :
    IsPrimitiveIdempotent (gB hf j) := by
  have he := eB_idem hf
  have hp := hprim ((reps hf).equivFin.symm j).1
  refine ⟨(gB_complete k hf).idem j, fun h ↦ hp.2.1 ?_, fun G hG h1 h2 ↦ ?_⟩
  · have := congrArg (cornerVal (eB_idem hf)) h
    rwa [gB_val, corner_zero_val] at this
  · have hG' : IsIdempotentElem (cornerVal (eB_idem hf) G) := by
      change _ * _ = _; rw [← corner_mul_val, hG.eq]
    have h1' := congrArg (cornerVal (eB_idem hf)) h1
    have h2' := congrArg (cornerVal (eB_idem hf)) h2
    rw [corner_mul_val, gB_val] at h1' h2'
    rcases hp.2.2 _ hG' h1' h2' with h | h
    · left; apply corner_ext; rw [h, corner_zero_val]
    · right; apply corner_ext; rw [h, gB_val]

theorem gB_basic (i j : Fin (reps hf).card)
    (h : ∃ x y : (eB_idem hf).Corner, gB hf i * x * gB hf j = x ∧ gB hf j * y * gB hf i = y ∧
      x * y = gB hf i ∧ y * x = gB hf j) : i = j := by
  obtain ⟨x, y, h1, h2, h3, h4⟩ := h
  have hiso : IsoData (f ((reps hf).equivFin.symm i).1) (f ((reps hf).equivFin.symm j).1) := by
    refine ⟨cornerVal _ x, cornerVal _ y, ?_, ?_, ?_, ?_⟩
    · have := congrArg (cornerVal (eB_idem hf)) h1
      rwa [corner_mul_val, corner_mul_val, gB_val, gB_val] at this
    · have := congrArg (cornerVal (eB_idem hf)) h2
      rwa [corner_mul_val, corner_mul_val, gB_val, gB_val] at this
    · have := congrArg (cornerVal (eB_idem hf)) h3
      rwa [corner_mul_val, gB_val] at this
    · have := congrArg (cornerVal (eB_idem hf)) h4
      rwa [corner_mul_val, gB_val] at this
  have := rep_eq hf hiso
  rw [rep_of_mem hf ((reps hf).equivFin.symm i).2, rep_of_mem hf ((reps hf).equivFin.symm j).2]
    at this
  exact (reps hf).equivFin.symm.injective (Subtype.ext this)

end BasicCorner

variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **The basic algebra is a full corner**: there is an idempotent `e` with
`AeA = A` and `eAe` basic. -/
theorem exists_basic_full_corner :
    ∃ (e : A) (he : IsIdempotentElem e),
      (∀ a : A, a ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q}) ∧ IsBasicAlgebra he.Corner := by
  obtain ⟨n, f, hf, hprim⟩ := exists_primitive_decomposition k A
  exact ⟨BasicCorner.eB hf, BasicCorner.eB_idem hf, BasicCorner.full_eB hf,
    ⟨_, BasicCorner.gB hf, BasicCorner.gB_complete k hf, BasicCorner.gB_primitive k hf hprim,
      BasicCorner.gB_basic hf⟩⟩

end MultiplicativeBasisDeformations
