module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import MBDVendor.QSE.CategoryTheory.HomIdealPowers
public import MBDVendor.QSE.CategoryTheory.IyamaTauSequence
public import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Radical-power propagation in Iyama right ladders

This file formalizes the annihilator-propagation calculation in Iyama,
*Tau-categories I*, Lemma 6.4.1(1)(i).  A weak-kernel right-ladder step moves
an annihilator to the next rung up to its complementary term.  Iteration and
nilpotence then force one complementary composite to be nonzero in the
corresponding radical power.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.RightLadder

universe v u

open CategoricalIdeal CategoricalRadical

variable {C : Type u} [Category.{v} C]

section ExplicitStep

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The explicit right-ladder step from Iyama, Section 3.2:

`ZNext ⊞ U → YNext ⊞ ZPrev → YPrev`,

with first-map matrix `[[bNext, 0], [-g, h]]` and second map
`(f, bPrev)`. -/
def stepComplex
    {ZPrev YPrev ZNext YNext U : C}
    (bPrev : ZPrev ⟶ YPrev) (bNext : ZNext ⟶ YNext)
    (f : YNext ⟶ YPrev) (g : ZNext ⟶ ZPrev)
    (h : U ⟶ ZPrev)
    (comm : bNext ≫ f = g ≫ bPrev)
    (hzero : h ≫ bPrev = 0) : ShortComplex C :=
  ShortComplex.mk
    (biprod.desc (biprod.lift bNext (-g)) (biprod.lift 0 h))
    (biprod.desc f bPrev)
    (by
      apply biprod.hom_ext'
      · simp [comm]
      · simp [hzero])

/-- One weak-kernel right-ladder step propagates an annihilator across the
step, up to the complementary `U`-term.

This is the literal calculation
`sPrev = sNext ≫ g + t ≫ h` and `sNext ≫ bNext = 0` in the proof of
Iyama 6.4.1(1)(i). -/
theorem exists_next_annihilator
    {ZPrev YPrev ZNext YNext U W : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    (hweak : ShortComplex.IsWeakKernel
      (stepComplex bPrev bNext f g h comm hzero))
    (sPrev : W ⟶ ZPrev) (hsPrev : sPrev ≫ bPrev = 0) :
    ∃ (sNext : W ⟶ ZNext) (t : W ⟶ U),
      sNext ≫ bNext = 0 ∧
        sPrev = sNext ≫ g + t ≫ h := by
  let k : W ⟶ YNext ⊞ ZPrev := biprod.lift 0 sPrev
  have hk : k ≫ (stepComplex
      bPrev bNext f g h comm hzero).g = 0 := by
    dsimp [k, stepComplex]
    rw [biprod.lift_desc, zero_comp, hsPrev, zero_add]
    rfl
  obtain ⟨l, hl⟩ :=
    (ShortComplex.isWeakKernel_iff _).mp hweak k hk
  have l_eq :
      l = biprod.lift (l ≫ biprod.fst) (l ≫ biprod.snd) := by
    apply biprod.hom_ext <;> simp <;> rfl
  let sNext : W ⟶ ZNext := -(l ≫ biprod.fst)
  let t : W ⟶ U := l ≫ biprod.snd
  refine ⟨sNext, t, ?_, ?_⟩
  · have hcomponent := congrArg (fun q ↦ q ≫ biprod.fst) hl
    dsimp [k, stepComplex] at hcomponent
    rw [l_eq] at hcomponent
    dsimp [sNext]
    simpa [Category.assoc] using congrArg Neg.neg hcomponent
  · have hcomponent := congrArg (fun q ↦ q ≫ biprod.snd) hl
    dsimp [k, stepComplex] at hcomponent
    rw [l_eq] at hcomponent
    dsimp [sNext, t]
    simpa [Category.assoc] using hcomponent.symm

/-- If an explicit right-ladder step is isomorphic to a right tau-sequence,
then all three visible components of its first map belong to the chosen
categorical radical ideal. -/
theorem stepMaps_mem_radical_of_rightTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    bNext ∈ R.ideal.hom ZNext YNext ∧
      g ∈ R.ideal.hom ZNext ZPrev ∧
        h ∈ R.ideal.hom U ZPrev := by
  have hstep_mem :
      (stepComplex bPrev bNext f g h comm hzero).f ∈
        R.ideal.hom
          (stepComplex bPrev bNext f g h comm hzero).X₁
          (stepComplex bPrev bNext f g h comm hzero).X₂ := by
    exact (R.mem_iff _).2 (hS.toTauApproximation.f_radical_of_iso e)
  refine ⟨?_, ?_, ?_⟩
  · have hcomponent :=
      R.ideal.postcomp
        (biprod.fst : YNext ⊞ ZPrev ⟶ YNext)
        (R.ideal.precomp
          (biprod.inl : ZNext ⟶ ZNext ⊞ U) hstep_mem)
    simpa [stepComplex, Category.assoc] using hcomponent
  · have hcomponent :=
      R.ideal.postcomp
        (biprod.snd : YNext ⊞ ZPrev ⟶ ZPrev)
        (R.ideal.precomp
          (-(biprod.inl : ZNext ⟶ ZNext ⊞ U)) hstep_mem)
    simpa [stepComplex, Category.assoc] using hcomponent
  · have hcomponent :=
      R.ideal.postcomp
        (biprod.snd : YNext ⊞ ZPrev ⟶ ZPrev)
        (R.ideal.precomp
          (biprod.inr : U ⟶ ZNext ⊞ U) hstep_mem)
    simpa [stepComplex, Category.assoc] using hcomponent

/-- The next horizontal arrow in an explicit right-ladder step is radical. -/
theorem nextMap_mem_radical_of_rightTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    bNext ∈ R.ideal.hom ZNext YNext :=
  (stepMaps_mem_radical_of_rightTauSequence_iso_stepComplex R hS e).1

/-- `Nonempty` form of radicality of the next horizontal arrow. -/
theorem nextMap_mem_radical_of_rightTauSequence_nonempty_iso_stepComplex
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : Nonempty
      (S ≅ stepComplex bPrev bNext f g h comm hzero)) :
    bNext ∈ R.ideal.hom ZNext YNext := by
  obtain ⟨e⟩ := e
  exact nextMap_mem_radical_of_rightTauSequence_iso_stepComplex R hS e

/-- Both connecting components in an explicit right-ladder step are
radical. -/
theorem connectingMaps_mem_radical_of_rightTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    g ∈ R.ideal.hom ZNext ZPrev ∧
      h ∈ R.ideal.hom U ZPrev :=
  (stepMaps_mem_radical_of_rightTauSequence_iso_stepComplex R hS e).2

/-- `Nonempty` form matching the noncanonical mesh isomorphisms stored in
Iyama ladder data. -/
theorem connectingMaps_mem_radical_of_rightTauSequence_nonempty_iso_stepComplex
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : Nonempty
      (S ≅ stepComplex bPrev bNext f g h comm hzero)) :
    g ∈ R.ideal.hom ZNext ZPrev ∧
      h ∈ R.ideal.hom U ZPrev := by
  obtain ⟨e⟩ := e
  exact connectingMaps_mem_radical_of_rightTauSequence_iso_stepComplex
    R hS e

/-- Family form aligned with the hypotheses of right-ladder radical-power
propagation. -/
theorem connectingMaps_mem_radical_of_rightTauSequence_stepFamily
    (R : NilpotentRadicalData C)
    (S : ℕ → ShortComplex C)
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (comm : ∀ n : ℕ, b (n + 1) ≫ f n = g n ≫ b n)
    (hzero : ∀ n : ℕ, h n ≫ b n = 0)
    (hS : ∀ n : ℕ, RightTauSequence (S n))
    (e : ∀ n : ℕ, Nonempty
      (S n ≅ stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n))) :
    (∀ n : ℕ,
      g n ∈ R.ideal.hom (Z (n + 1)) (Z n)) ∧
      ∀ n : ℕ,
        h n ∈ R.ideal.hom (U (n + 1)) (Z n) := by
  constructor
  · intro n
    exact
      (connectingMaps_mem_radical_of_rightTauSequence_nonempty_iso_stepComplex
        R (hS n) (e n)).1
  · intro n
    exact
      (connectingMaps_mem_radical_of_rightTauSequence_nonempty_iso_stepComplex
        R (hS n) (e n)).2

/-- A right tau-sequence isomorphic to an explicit right-ladder step makes
that step a weak-kernel complex. -/
theorem isWeakKernel_stepComplex_of_rightTauSequence_nonempty_iso
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : Nonempty
      (S ≅ stepComplex bPrev bNext f g h comm hzero)) :
    ShortComplex.IsWeakKernel
      (stepComplex bPrev bNext f g h comm hzero) := by
  obtain ⟨e⟩ := e
  exact hS.minimalWeakKernel.1.of_iso e

end ExplicitStep

section RadicalPropagation

variable [Preadditive C]

/-- The backwards composite of the first `n` right-ladder connecting maps. -/
def backwardComposite
    (Z : ℕ → C) (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n) :
    ∀ n : ℕ, Z n ⟶ Z 0
  | 0 => 𝟙 (Z 0)
  | n + 1 => g n ≫ backwardComposite Z g n

omit [Preadditive C] in
@[simp]
theorem backwardComposite_zero
    (Z : ℕ → C) (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n) :
    backwardComposite Z g 0 = 𝟙 (Z 0) :=
  rfl

omit [Preadditive C] in
@[simp]
theorem backwardComposite_succ
    (Z : ℕ → C) (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (n : ℕ) :
    backwardComposite Z g (n + 1) =
      g n ≫ backwardComposite Z g n :=
  rfl

/-- A chain of radical connecting maps has its length-`n` composite in the
`n`th ideal power. -/
theorem backwardComposite_mem_pow
    (I : HomIdeal C)
    (Z : ℕ → C) (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (hg : ∀ n : ℕ, g n ∈ I.hom (Z (n + 1)) (Z n)) :
    ∀ n : ℕ,
      backwardComposite Z g n ∈ (I.pow n).hom (Z n) (Z 0)
  | 0 => by simp
  | n + 1 => by
      rw [I.pow_succ_eq_mul_pow]
      exact HomIdeal.comp_mem_mul (hg n)
        (backwardComposite_mem_pow I Z g hg n)

/-- The exact abstract output needed from every explicit right-ladder step. -/
def HasAnnihilatorPropagation
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n) : Prop :=
  ∀ (n : ℕ) {W : C} (s : W ⟶ Z n), s ≫ b n = 0 →
    ∃ (sNext : W ⟶ Z (n + 1)) (t : W ⟶ U (n + 1)),
      sNext ≫ b (n + 1) = 0 ∧
        s = sNext ≫ g n + t ≫ h n

/-- A family of explicit weak-kernel right-ladder steps supplies the abstract
annihilator-propagation property. -/
theorem hasAnnihilatorPropagation_of_weakKernels
    [HasBinaryBiproducts C]
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (comm : ∀ n : ℕ, b (n + 1) ≫ f n = g n ≫ b n)
    (hzero : ∀ n : ℕ, h n ≫ b n = 0)
    (hweak : ∀ n : ℕ, ShortComplex.IsWeakKernel
      (stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n))) :
    HasAnnihilatorPropagation Z Y U b g h := by
  intro n W s hs
  exact exists_next_annihilator (hweak n) s hs

/-- Right tau-sequence models of all explicit ladder steps supply the
annihilator propagation used in radical-power iteration. -/
theorem hasAnnihilatorPropagation_of_rightTauSequence_stepFamily
    [HasBinaryBiproducts C]
    (S : ℕ → ShortComplex C)
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (comm : ∀ n : ℕ, b (n + 1) ≫ f n = g n ≫ b n)
    (hzero : ∀ n : ℕ, h n ≫ b n = 0)
    (hS : ∀ n : ℕ, RightTauSequence (S n))
    (e : ∀ n : ℕ, Nonempty
      (S n ≅ stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n))) :
    HasAnnihilatorPropagation Z Y U b g h := by
  apply hasAnnihilatorPropagation_of_weakKernels Z Y U b f g h comm hzero
  intro n
  exact isWeakKernel_stepComplex_of_rightTauSequence_nonempty_iso
    (hS n) (e n)

/-- If all complementary terms vanish after composing to the initial source,
an initial annihilator propagates through every finite right-ladder prefix. -/
theorem exists_propagated_annihilator
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (hstep : HasAnnihilatorPropagation Z Y U b g h)
    (hkill : ∀ n : ℕ,
      h n ≫ backwardComposite Z g n = 0)
    {W : C} (s₀ : W ⟶ Z 0) (hs₀ : s₀ ≫ b 0 = 0) :
    ∀ n : ℕ, ∃ s : W ⟶ Z n,
      s ≫ b n = 0 ∧ s₀ = s ≫ backwardComposite Z g n
  | 0 => ⟨s₀, hs₀, by simp⟩
  | n + 1 => by
      obtain ⟨s, hs, hs₀⟩ :=
        exists_propagated_annihilator Z Y U b g h hstep hkill s₀ hs₀ n
      obtain ⟨sNext, t, hsNext, hrelation⟩ := hstep n s hs
      refine ⟨sNext, hsNext, ?_⟩
      calc
        s₀ = s ≫ backwardComposite Z g n := hs₀
        _ = (sNext ≫ g n + t ≫ h n) ≫
              backwardComposite Z g n := by rw [hrelation]
        _ = sNext ≫ backwardComposite Z g (n + 1) := by
          simp [Preadditive.add_comp, Category.assoc, hkill n]

/-- Radical-power propagation in the form used in Iyama 6.4.1(1)(i).

Starting from a nonzero annihilator, some complementary morphism
`hᵢ ≫ gᵢ₋₁ ≫ ⋯ ≫ g₁` is nonzero.  It automatically lies in the
corresponding radical power.  Thus the hypothesis that every
`Jⁱ(Uᵢ,Z₀)` vanishes is incompatible with the initial nonzero
annihilator. -/
theorem exists_nonzero_remainder_in_radical_power
    (R : NilpotentRadicalData C)
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (hstep : HasAnnihilatorPropagation Z Y U b g h)
    (hg : ∀ n : ℕ,
      g n ∈ R.ideal.hom (Z (n + 1)) (Z n))
    (hh : ∀ n : ℕ,
      h n ∈ R.ideal.hom (U (n + 1)) (Z n))
    {W : C} (s₀ : W ⟶ Z 0)
    (hs₀ : s₀ ≫ b 0 = 0) (hs₀ne : s₀ ≠ 0) :
    ∃ n : ℕ,
      h n ≫ backwardComposite Z g n ∈
          (R.ideal.pow (n + 1)).hom (U (n + 1)) (Z 0) ∧
        h n ≫ backwardComposite Z g n ≠ 0 := by
  have hprefix := backwardComposite_mem_pow R.ideal Z g hg
  have hremainder_mem (n : ℕ) :
      h n ≫ backwardComposite Z g n ∈
        (R.ideal.pow (n + 1)).hom (U (n + 1)) (Z 0) := by
    rw [R.ideal.pow_succ_eq_mul_pow]
    exact HomIdeal.comp_mem_mul (hh n) (hprefix n)
  by_contra hexists
  have hkill (n : ℕ) :
      h n ≫ backwardComposite Z g n = 0 := by
    by_contra hne
    exact hexists ⟨n, hremainder_mem n, hne⟩
  have hprop :=
    exists_propagated_annihilator Z Y U b g h hstep hkill s₀ hs₀
  apply hs₀ne
  apply R.eq_zero_of_mem_every_power
  intro n
  obtain ⟨s, hs, heq⟩ := hprop n
  rw [heq]
  exact (R.ideal.pow n).precomp s (hprefix n)

end RadicalPropagation

end MBDVendor.QSE.Iyama.RightLadder
