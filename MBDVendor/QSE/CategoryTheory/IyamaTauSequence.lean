import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels
import MBDVendor.QSE.CategoryTheory.CategoricalRadical
import MBDVendor.QSE.CategoryTheory.MinimalMorphism

/-!
# Iyama tau-sequences: categorical base layer

This file packages the weak-kernel, weak-cokernel, minimality, and radical
approximation conditions in the definition of a right or left tau-sequence.
It is independent of any module category or concrete quiver.

Mathlib represents a weak kernel by the data of an `IsWeakLimit`.  We wrap
that data in `Nonempty` to obtain a proposition.  A weak cokernel is defined
by applying the same construction in the opposite category.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u

namespace ShortComplex

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]

/-- The first map of `S` exhibits a weak kernel of its second map. -/
def IsWeakKernel (S : ShortComplex D) : Prop :=
  Nonempty (IsWeakLimit (KernelFork.ofι S.f S.zero))

/-- The second map of `S` exhibits a weak cokernel of its first map. -/
def IsWeakCokernel (S : ShortComplex D) : Prop :=
  IsWeakKernel S.op

/-- Factorization form of the weak-kernel condition. -/
theorem isWeakKernel_iff (S : ShortComplex D) :
    IsWeakKernel S ↔
      ∀ {W : D} (k : W ⟶ S.X₂), k ≫ S.g = 0 →
        ∃ l : W ⟶ S.X₁, l ≫ S.f = k := by
  constructor
  · rintro ⟨h⟩ W k hk
    let s : KernelFork S.g := KernelFork.ofι k hk
    exact ⟨h.lift s, h.fac s WalkingParallelPair.zero⟩
  · intro h
    refine ⟨Fork.IsWeakLimit.mk' (KernelFork.ofι S.f S.zero) ?_⟩
    intro s
    let hl := h (Fork.ι s) (KernelFork.condition s)
    exact ⟨Classical.choose hl, Classical.choose_spec hl⟩

/-- A chosen weak-kernel factorization.  Its value is noncanonical. -/
def IsWeakKernel.lift {S : ShortComplex D} (hS : IsWeakKernel S)
    {W : D} (k : W ⟶ S.X₂) (hk : k ≫ S.g = 0) : W ⟶ S.X₁ :=
  Classical.choose ((isWeakKernel_iff S).mp hS k hk)

@[reassoc]
theorem IsWeakKernel.lift_f {S : ShortComplex D} (hS : IsWeakKernel S)
    {W : D} (k : W ⟶ S.X₂) (hk : k ≫ S.g = 0) :
    hS.lift k hk ≫ S.f = k :=
  Classical.choose_spec ((isWeakKernel_iff S).mp hS k hk)

/-- Evaluating a weak kernel against any source object gives an exact pair
of postcomposition maps. -/
theorem IsWeakKernel.exact_postcomp {S : ShortComplex D}
    (hS : IsWeakKernel S) (W : D) :
    Function.Exact
      (fun l : W ⟶ S.X₁ ↦ l ≫ S.f)
      (fun k : W ⟶ S.X₂ ↦ k ≫ S.g) := by
  intro k
  constructor
  · intro hk
    obtain ⟨l, hl⟩ := (isWeakKernel_iff S).mp hS k hk
    exact ⟨l, hl⟩
  · rintro ⟨l, rfl⟩
    dsimp only
    rw [Category.assoc, S.zero, comp_zero]

/-- Factorization form of the weak-cokernel condition, transported back from
the opposite category. -/
theorem isWeakCokernel_iff (S : ShortComplex D) :
    IsWeakCokernel S ↔
      ∀ {W : D} (k : S.X₂ ⟶ W), S.f ≫ k = 0 →
        ∃ l : S.X₃ ⟶ W, S.g ≫ l = k := by
  rw [IsWeakCokernel, isWeakKernel_iff]
  change
    (∀ {W : Dᵒᵖ} (k : W ⟶ Opposite.op S.X₂),
      k ≫ S.f.op = 0 →
        ∃ l : W ⟶ Opposite.op S.X₃, l ≫ S.g.op = k) ↔ _
  constructor
  · intro h W k hk
    obtain ⟨l, hl⟩ := h k.op (by
      rw [← op_comp, hk, op_zero])
    exact ⟨l.unop, by
      simpa only [unop_comp, Quiver.Hom.unop_op] using
        congrArg Quiver.Hom.unop hl⟩
  · intro h W k hk
    obtain ⟨l, hl⟩ := h k.unop (by
      simpa only [unop_comp, Quiver.Hom.unop_op, unop_zero] using
        congrArg Quiver.Hom.unop hk)
    exact ⟨l.op, by
      simpa only [op_comp, Quiver.Hom.op_unop] using
        congrArg Quiver.Hom.op hl⟩

/-- The weak-kernel predicate is preserved by isomorphisms of short
complexes. -/
theorem IsWeakKernel.of_iso {S T : ShortComplex D}
    (hS : IsWeakKernel S) (e : S ≅ T) : IsWeakKernel T := by
  rw [isWeakKernel_iff]
  intro W k hk
  have hkS : (k ≫ e.inv.τ₂) ≫ S.g = 0 := by
    rw [Category.assoc, e.inv.comm₂₃, ← Category.assoc, hk, zero_comp]
  obtain ⟨l, hl⟩ := (isWeakKernel_iff S).mp hS (k ≫ e.inv.τ₂) hkS
  refine ⟨l ≫ e.hom.τ₁, ?_⟩
  calc
    (l ≫ e.hom.τ₁) ≫ T.f = l ≫ (e.hom.τ₁ ≫ T.f) :=
      Category.assoc _ _ _
    _ = l ≫ (S.f ≫ e.hom.τ₂) := by rw [e.hom.comm₁₂]
    _ = (l ≫ S.f) ≫ e.hom.τ₂ := (Category.assoc _ _ _).symm
    _ = (k ≫ e.inv.τ₂) ≫ e.hom.τ₂ := by rw [hl]
    _ = k := by
      rw [Category.assoc]
      have he := congrArg ShortComplex.Hom.τ₂ e.inv_hom_id
      change e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 T.X₂ at he
      rw [he, Category.comp_id]

/-- The weak-cokernel predicate is preserved by isomorphisms of short
complexes. -/
theorem IsWeakCokernel.of_iso {S T : ShortComplex D}
    (hS : IsWeakCokernel S) (e : S ≅ T) : IsWeakCokernel T := by
  rw [isWeakCokernel_iff]
  intro W k hk
  have hkS : S.f ≫ (e.hom.τ₂ ≫ k) = 0 := by
    rw [← Category.assoc, ← e.hom.comm₁₂, Category.assoc, hk, comp_zero]
  obtain ⟨l, hl⟩ :=
    (isWeakCokernel_iff S).mp hS (e.hom.τ₂ ≫ k) hkS
  refine ⟨e.inv.τ₃ ≫ l, ?_⟩
  calc
    T.g ≫ (e.inv.τ₃ ≫ l) = (T.g ≫ e.inv.τ₃) ≫ l :=
      (Category.assoc _ _ _).symm
    _ = (e.inv.τ₂ ≫ S.g) ≫ l := by rw [e.inv.comm₂₃]
    _ = e.inv.τ₂ ≫ (S.g ≫ l) := Category.assoc _ _ _
    _ = e.inv.τ₂ ≫ (e.hom.τ₂ ≫ k) := by rw [hl]
    _ = k := by
      rw [← Category.assoc]
      have he := congrArg ShortComplex.Hom.τ₂ e.inv_hom_id
      change e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 T.X₂ at he
      rw [he, Category.id_comp]

/-- Evaluating a weak cokernel against any target object gives an exact pair
of precomposition maps. -/
theorem IsWeakCokernel.exact_precomp {S : ShortComplex D}
    (hS : IsWeakCokernel S) (W : D) :
    Function.Exact
      (fun l : S.X₃ ⟶ W ↦ S.g ≫ l)
      (fun k : S.X₂ ⟶ W ↦ S.f ≫ k) := by
  intro k
  constructor
  · intro hk
    obtain ⟨l, hl⟩ := (isWeakCokernel_iff S).mp hS k hk
    exact ⟨l, hl⟩
  · rintro ⟨l, rfl⟩
    dsimp only
    rw [← Category.assoc, S.zero, zero_comp]

end ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ShortComplex

/-- A minimal weak kernel is weakly universal and right minimal.

In the intended Krull--Schmidt/Fitting setting this is equivalent to Iyama's
literal condition that no nonzero summand `W ⟶ 0` splits off. -/
def IsMinimalWeakKernel (S : ShortComplex C) : Prop :=
  IsWeakKernel S ∧ IsRightMinimal S.f

/-- A minimal weak cokernel is weakly universal and left minimal.

In the intended Krull--Schmidt/Fitting setting this is equivalent to Iyama's
literal condition that no nonzero summand `0 ⟶ W` splits off. -/
def IsMinimalWeakCokernel (S : ShortComplex C) : Prop :=
  IsWeakCokernel S ∧ IsLeftMinimal S.g

end ShortComplex

open CategoricalRadical

/-- Iyama's radical approximation condition for a complex
`X₁ → X₂ → X₃`.

Every radical map out of `X₁` factors through the first map, and every
radical map into `X₃` factors through the second map. -/
structure TauApproximation (S : ShortComplex C) : Prop where
  f_radical : IsRadicalMorphism S.f
  g_radical : IsRadicalMorphism S.g
  factors_from_left :
    ∀ {W : C} (a : S.X₁ ⟶ W), IsRadicalMorphism a →
      ∃ b : S.X₂ ⟶ W, S.f ≫ b = a
  factors_into_right :
    ∀ {W : C} (a : W ⟶ S.X₃), IsRadicalMorphism a →
      ∃ b : W ⟶ S.X₂, b ≫ S.g = a

/-- A right tau-sequence satisfies the radical approximation condition and
has a minimal weak kernel as its first map. -/
structure RightTauSequence (S : ShortComplex C) : Prop
    extends TauApproximation S where
  minimalWeakKernel : ShortComplex.IsMinimalWeakKernel S

/-- A left tau-sequence satisfies the radical approximation condition and
has a minimal weak cokernel as its second map. -/
structure LeftTauSequence (S : ShortComplex C) : Prop
    extends TauApproximation S where
  minimalWeakCokernel : ShortComplex.IsMinimalWeakCokernel S

namespace TauApproximation

/-- The first map of a tau-approximation remains radical after transporting
the short complex along an isomorphism. -/
theorem f_radical_of_iso {S T : ShortComplex C}
    (hS : TauApproximation S) (e : S ≅ T) :
    IsRadicalMorphism T.f := by
  have hTf : T.f = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ := by
    have he₂ : e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 T.X₂ := by
      have he := congrArg ShortComplex.Hom.τ₂ e.inv_hom_id
      change e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 _ at he
      exact he
    calc
      T.f = T.f ≫ 𝟙 _ := by simp
      _ = T.f ≫ (e.inv.τ₂ ≫ e.hom.τ₂) := by rw [he₂]
      _ = (T.f ≫ e.inv.τ₂) ≫ e.hom.τ₂ :=
        (Category.assoc _ _ _).symm
      _ = (e.inv.τ₁ ≫ S.f) ≫ e.hom.τ₂ := by
        rw [← e.inv.comm₁₂]
      _ = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ := Category.assoc _ _ _
  rw [hTf]
  simpa only [Category.assoc] using
    isRadicalMorphism_postcomp e.hom.τ₂
      (isRadicalMorphism_precomp e.inv.τ₁ hS.f_radical)

/-- The second map of a tau-approximation remains radical after transporting
the short complex along an isomorphism. -/
theorem g_radical_of_iso {S T : ShortComplex C}
    (hS : TauApproximation S) (e : S ≅ T) :
    IsRadicalMorphism T.g := by
  have hTg : T.g = e.inv.τ₂ ≫ S.g ≫ e.hom.τ₃ := by
    have he₃ : e.inv.τ₃ ≫ e.hom.τ₃ = 𝟙 T.X₃ := by
      have he := congrArg ShortComplex.Hom.τ₃ e.inv_hom_id
      change e.inv.τ₃ ≫ e.hom.τ₃ = 𝟙 _ at he
      exact he
    calc
      T.g = T.g ≫ 𝟙 _ := by simp
      _ = T.g ≫ (e.inv.τ₃ ≫ e.hom.τ₃) := by rw [he₃]
      _ = (T.g ≫ e.inv.τ₃) ≫ e.hom.τ₃ :=
        (Category.assoc _ _ _).symm
      _ = (e.inv.τ₂ ≫ S.g) ≫ e.hom.τ₃ := by
        rw [← e.inv.comm₂₃]
      _ = e.inv.τ₂ ≫ S.g ≫ e.hom.τ₃ := Category.assoc _ _ _
  rw [hTg]
  simpa only [Category.assoc] using
    isRadicalMorphism_postcomp e.hom.τ₃
      (isRadicalMorphism_precomp e.inv.τ₂ hS.g_radical)

end TauApproximation

namespace RightTauSequence

/-- If the left term of a right tau-sequence is nonzero, then its middle
term is nonzero.  In fact, only right minimality of the first map is used. -/
theorem not_isZero_X₂_of_not_isZero_X₁
    {S : ShortComplex C} (hS : RightTauSequence S)
    (hleft : ¬ IsZero S.X₁) :
    ¬ IsZero S.X₂ := by
  intro hmiddle
  have hf : S.f = 0 := hmiddle.eq_of_tgt _ _
  haveI hzeroIso : IsIso (0 : S.X₁ ⟶ S.X₁) :=
    hS.minimalWeakKernel.2 0 (by
      rw [zero_comp]
      exact hf.symm)
  apply hleft
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_epi (0 : S.X₁ ⟶ S.X₁)]
  simp

private theorem isIso_of_sub_id_radical
    {X : C} (e : X ⟶ X)
    (he : IsRadicalMorphism (e - 𝟙 X)) :
    IsIso e := by
  have hi : IsIso (𝟙 X - (e - 𝟙 X) ≫ (-𝟙 X)) :=
    he (-𝟙 X)
  have hrewrite : 𝟙 X - (e - 𝟙 X) ≫ (-𝟙 X) = e := by
    simp
  rw [hrewrite] at hi
  exact hi

/-- In a right tau-sequence, the second map is automatically right minimal.
The weak-kernel and radical conditions rule out a redundant middle-term
summand. -/
theorem isRightMinimal_g {S : ShortComplex C}
    (hS : RightTauSequence S) :
    IsRightMinimal S.g := by
  intro e he
  have hkernel : (e - 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Preadditive.sub_comp, he, Category.id_comp, sub_self]
  obtain ⟨l, hl⟩ :=
    (ShortComplex.isWeakKernel_iff S).mp
      hS.minimalWeakKernel.1 (e - 𝟙 S.X₂) hkernel
  apply isIso_of_sub_id_radical e
  rw [← hl]
  exact isRadicalMorphism_precomp l hS.f_radical

/-- Two right tau-sequences with isomorphic right endpoints are isomorphic
as short complexes. -/
theorem nonempty_iso_of_iso_X₃
    {S T : ShortComplex C}
    (hS : RightTauSequence S) (hT : RightTauSequence T)
    (e₃ : S.X₃ ≅ T.X₃) : Nonempty (S ≅ T) := by
  have hSg : IsRadicalMorphism (S.g ≫ e₃.hom) :=
    isRadicalMorphism_postcomp e₃.hom hS.g_radical
  obtain ⟨a, ha⟩ := hT.factors_into_right (S.g ≫ e₃.hom) hSg
  have hTg : IsRadicalMorphism (T.g ≫ e₃.inv) :=
    isRadicalMorphism_postcomp e₃.inv hT.g_radical
  obtain ⟨b, hb⟩ := hS.factors_into_right (T.g ≫ e₃.inv) hTg
  have hab : (a ≫ b) ≫ S.g = S.g := by
    calc
      (a ≫ b) ≫ S.g = a ≫ (b ≫ S.g) := Category.assoc _ _ _
      _ = a ≫ (T.g ≫ e₃.inv) := by rw [hb]
      _ = (a ≫ T.g) ≫ e₃.inv := by rw [Category.assoc]
      _ = (S.g ≫ e₃.hom) ≫ e₃.inv := by rw [ha]
      _ = S.g := by rw [Category.assoc, e₃.hom_inv_id, Category.comp_id]
  have hba : (b ≫ a) ≫ T.g = T.g := by
    calc
      (b ≫ a) ≫ T.g = b ≫ (a ≫ T.g) := Category.assoc _ _ _
      _ = b ≫ (S.g ≫ e₃.hom) := by rw [ha]
      _ = (b ≫ S.g) ≫ e₃.hom := by rw [Category.assoc]
      _ = (T.g ≫ e₃.inv) ≫ e₃.hom := by rw [hb]
      _ = T.g := by rw [Category.assoc, e₃.inv_hom_id, Category.comp_id]
  letI : IsIso (a ≫ b) := hS.isRightMinimal_g (a ≫ b) hab
  letI : IsIso (b ≫ a) := hT.isRightMinimal_g (b ≫ a) hba
  letI : IsIso a := isIso_of_isIso_comp_both a b
  let e₂ : S.X₂ ≅ T.X₂ := asIso a
  have he₂ : e₂.hom = a := by simp [e₂]
  have hSf : (S.f ≫ a) ≫ T.g = 0 := by
    rw [Category.assoc, ha, ← Category.assoc, S.zero, zero_comp]
  obtain ⟨p, hp⟩ :=
    (ShortComplex.isWeakKernel_iff T).mp hT.minimalWeakKernel.1
      (S.f ≫ a) hSf
  have hba' : e₂.inv ≫ S.g = T.g ≫ e₃.inv := by
    rw [← cancel_epi e₂.hom]
    rw [e₂.hom_inv_id_assoc, ← Category.assoc, he₂, ha,
      Category.assoc, e₃.hom_inv_id, Category.comp_id]
  have hTf : (T.f ≫ e₂.inv) ≫ S.g = 0 := by
    rw [Category.assoc, hba', ← Category.assoc, T.zero, zero_comp]
  obtain ⟨q, hq⟩ :=
    (ShortComplex.isWeakKernel_iff S).mp hS.minimalWeakKernel.1
      (T.f ≫ e₂.inv) hTf
  have hpq : (p ≫ q) ≫ S.f = S.f := by
    calc
      (p ≫ q) ≫ S.f = p ≫ (q ≫ S.f) := Category.assoc _ _ _
      _ = p ≫ (T.f ≫ e₂.inv) := by rw [hq]
      _ = (p ≫ T.f) ≫ e₂.inv := by rw [Category.assoc]
      _ = (S.f ≫ a) ≫ e₂.inv := by rw [hp]
      _ = S.f := by
        rw [← he₂, Category.assoc, e₂.hom_inv_id, Category.comp_id]
  have hqp : (q ≫ p) ≫ T.f = T.f := by
    calc
      (q ≫ p) ≫ T.f = q ≫ (p ≫ T.f) := Category.assoc _ _ _
      _ = q ≫ (S.f ≫ a) := by rw [hp]
      _ = (q ≫ S.f) ≫ a := by rw [Category.assoc]
      _ = (T.f ≫ e₂.inv) ≫ a := by rw [hq]
      _ = T.f := by
        rw [← he₂, Category.assoc, e₂.inv_hom_id, Category.comp_id]
  letI : IsIso (p ≫ q) := hS.minimalWeakKernel.2 (p ≫ q) hpq
  letI : IsIso (q ≫ p) := hT.minimalWeakKernel.2 (q ≫ p) hqp
  letI : IsIso p := isIso_of_isIso_comp_both p q
  exact ⟨ShortComplex.isoMk (asIso p) e₂ e₃ hp ha⟩

/-- The contravariant representable complex of a right tau-sequence is exact
at its middle term. -/
theorem exact_postcomp {S : ShortComplex C} (hS : RightTauSequence S)
    (W : C) :
    Function.Exact
      (fun l : W ⟶ S.X₁ ↦ l ≫ S.f)
      (fun k : W ⟶ S.X₂ ↦ k ≫ S.g) :=
  hS.minimalWeakKernel.1.exact_postcomp W

end RightTauSequence

namespace LeftTauSequence

private theorem isIso_of_sub_id_radical
    {X : C} (e : X ⟶ X)
    (he : IsRadicalMorphism (e - 𝟙 X)) :
    IsIso e := by
  have hi : IsIso (𝟙 X - (e - 𝟙 X) ≫ (-𝟙 X)) :=
    he (-𝟙 X)
  have hrewrite : 𝟙 X - (e - 𝟙 X) ≫ (-𝟙 X) = e := by
    simp
  rw [hrewrite] at hi
  exact hi

/-- In a left tau-sequence, the first map is automatically left minimal.
The weak-cokernel and radical conditions rule out a redundant middle-term
summand. -/
theorem isLeftMinimal_f {S : ShortComplex C}
    (hS : LeftTauSequence S) :
    IsLeftMinimal S.f := by
  intro e he
  have hcokernel : S.f ≫ (e - 𝟙 S.X₂) = 0 := by
    rw [Preadditive.comp_sub, he, Category.comp_id, sub_self]
  obtain ⟨l, hl⟩ :=
    (ShortComplex.isWeakCokernel_iff S).mp
      hS.minimalWeakCokernel.1 (e - 𝟙 S.X₂) hcokernel
  apply isIso_of_sub_id_radical e
  rw [← hl]
  exact isRadicalMorphism_postcomp l hS.g_radical

/-- Two left tau-sequences with isomorphic left endpoints are isomorphic
as short complexes. -/
theorem nonempty_iso_of_iso_X₁
    {S T : ShortComplex C}
    (hS : LeftTauSequence S) (hT : LeftTauSequence T)
    (e₁ : S.X₁ ≅ T.X₁) : Nonempty (S ≅ T) := by
  have hTf : IsRadicalMorphism (e₁.hom ≫ T.f) :=
    isRadicalMorphism_precomp e₁.hom hT.f_radical
  obtain ⟨a, ha⟩ := hS.factors_from_left (e₁.hom ≫ T.f) hTf
  have hSf : IsRadicalMorphism (e₁.inv ≫ S.f) :=
    isRadicalMorphism_precomp e₁.inv hS.f_radical
  obtain ⟨b, hb⟩ := hT.factors_from_left (e₁.inv ≫ S.f) hSf
  have hab : S.f ≫ (a ≫ b) = S.f := by
    calc
      S.f ≫ (a ≫ b) = (S.f ≫ a) ≫ b := (Category.assoc _ _ _).symm
      _ = (e₁.hom ≫ T.f) ≫ b := by rw [ha]
      _ = e₁.hom ≫ (T.f ≫ b) := Category.assoc _ _ _
      _ = e₁.hom ≫ (e₁.inv ≫ S.f) := by rw [hb]
      _ = S.f := by rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
  have hba : T.f ≫ (b ≫ a) = T.f := by
    calc
      T.f ≫ (b ≫ a) = (T.f ≫ b) ≫ a := (Category.assoc _ _ _).symm
      _ = (e₁.inv ≫ S.f) ≫ a := by rw [hb]
      _ = e₁.inv ≫ (S.f ≫ a) := Category.assoc _ _ _
      _ = e₁.inv ≫ (e₁.hom ≫ T.f) := by rw [ha]
      _ = T.f := by rw [← Category.assoc, e₁.inv_hom_id, Category.id_comp]
  letI : IsIso (a ≫ b) := hS.isLeftMinimal_f (a ≫ b) hab
  letI : IsIso (b ≫ a) := hT.isLeftMinimal_f (b ≫ a) hba
  letI : IsIso a := isIso_of_isIso_comp_both a b
  let e₂ : S.X₂ ≅ T.X₂ := asIso a
  have he₂ : e₂.hom = a := by simp [e₂]
  have hSTg : S.f ≫ (a ≫ T.g) = 0 := by
    rw [← Category.assoc, ha, Category.assoc, T.zero, comp_zero]
  obtain ⟨r, hr⟩ :=
    (ShortComplex.isWeakCokernel_iff S).mp hS.minimalWeakCokernel.1
      (a ≫ T.g) hSTg
  have hfa : T.f ≫ e₂.inv = e₁.inv ≫ S.f := by
    rw [← cancel_epi e₁.hom]
    calc
      e₁.hom ≫ (T.f ≫ e₂.inv) =
          (e₁.hom ≫ T.f) ≫ e₂.inv := (Category.assoc _ _ _).symm
      _ = (S.f ≫ a) ≫ e₂.inv := by rw [← ha]
      _ = S.f := by
        rw [← he₂, Category.assoc, e₂.hom_inv_id, Category.comp_id]
      _ = e₁.hom ≫ (e₁.inv ≫ S.f) := by
        rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
  have hTSg : T.f ≫ (e₂.inv ≫ S.g) = 0 := by
    rw [← Category.assoc, hfa, Category.assoc, S.zero, comp_zero]
  obtain ⟨s, hs⟩ :=
    (ShortComplex.isWeakCokernel_iff T).mp hT.minimalWeakCokernel.1
      (e₂.inv ≫ S.g) hTSg
  have hrs : S.g ≫ (r ≫ s) = S.g := by
    calc
      S.g ≫ (r ≫ s) = (S.g ≫ r) ≫ s := (Category.assoc _ _ _).symm
      _ = (a ≫ T.g) ≫ s := by rw [hr]
      _ = a ≫ (T.g ≫ s) := Category.assoc _ _ _
      _ = a ≫ (e₂.inv ≫ S.g) := by rw [hs]
      _ = S.g := by
        rw [← he₂, ← Category.assoc, e₂.hom_inv_id, Category.id_comp]
  have hsr : T.g ≫ (s ≫ r) = T.g := by
    calc
      T.g ≫ (s ≫ r) = (T.g ≫ s) ≫ r := (Category.assoc _ _ _).symm
      _ = (e₂.inv ≫ S.g) ≫ r := by rw [hs]
      _ = e₂.inv ≫ (S.g ≫ r) := Category.assoc _ _ _
      _ = e₂.inv ≫ (a ≫ T.g) := by rw [hr]
      _ = T.g := by
        rw [← he₂, ← Category.assoc, e₂.inv_hom_id, Category.id_comp]
  letI : IsIso (r ≫ s) := hS.minimalWeakCokernel.2 (r ≫ s) hrs
  letI : IsIso (s ≫ r) := hT.minimalWeakCokernel.2 (s ≫ r) hsr
  letI : IsIso r := isIso_of_isIso_comp_both r s
  exact ⟨ShortComplex.isoMk e₁ e₂ (asIso r)
    (by rw [he₂]; exact ha.symm)
    (by rw [he₂]; exact hr.symm)⟩

/-- The covariant representable complex of a left tau-sequence is exact at
its middle term. -/
theorem exact_precomp {S : ShortComplex C} (hS : LeftTauSequence S)
    (W : C) :
    Function.Exact
      (fun l : S.X₃ ⟶ W ↦ S.g ≫ l)
      (fun k : S.X₂ ⟶ W ↦ S.f ≫ k) :=
  hS.minimalWeakCokernel.1.exact_precomp W

end LeftTauSequence

end MBDVendor.QSE.Iyama
