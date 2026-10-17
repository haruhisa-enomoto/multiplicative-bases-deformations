import Mathlib.CategoryTheory.Preadditive.Biproducts
import MBDVendor.QSE.CategoryTheory.HomIdealPowers
import MBDVendor.QSE.CategoryTheory.IyamaTauSequence
import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Radical-power propagation in Iyama left ladders

This is the categorical dual of the right-ladder calculation in Iyama,
*Tau-categories I*, Lemma 6.4.1(1)(i).  The explicit matrix is obtained by
opposing the right-ladder matrix and then writing the biproducts back in the
original category.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.LeftLadder

universe v u

open CategoricalIdeal CategoricalRadical

variable {C : Type u} [Category.{v} C]

section ExplicitStep

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The explicit left-ladder step, dual to Iyama's right-ladder step:

`YPrev → YNext ⊞ ZPrev → ZNext ⊞ U`,

with first map `(f, bPrev)` and second-map matrix
`[[bNext, -g], [0, h]]`. -/
def stepComplex
    {YPrev ZPrev YNext ZNext U : C}
    (bPrev : YPrev ⟶ ZPrev) (bNext : YNext ⟶ ZNext)
    (f : YPrev ⟶ YNext) (g : ZPrev ⟶ ZNext)
    (h : ZPrev ⟶ U)
    (comm : f ≫ bNext = bPrev ≫ g)
    (hzero : bPrev ≫ h = 0) : ShortComplex C :=
  ShortComplex.mk
    (biprod.lift f bPrev)
    (biprod.lift (biprod.desc bNext (-g)) (biprod.desc 0 h))
    (by
      apply biprod.hom_ext
      · simp [comm]
      · simp [hzero])

/-- One weak-cokernel left-ladder step propagates a coannihilator across the
step, up to the complementary `U`-term.

This is the dual identity
`sPrev = g ≫ sNext + h ≫ t` with `bNext ≫ sNext = 0`. -/
theorem exists_next_coannihilator
    {YPrev ZPrev YNext ZNext U W : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    (hweak : ShortComplex.IsWeakCokernel
      (stepComplex bPrev bNext f g h comm hzero))
    (sPrev : ZPrev ⟶ W) (hsPrev : bPrev ≫ sPrev = 0) :
    ∃ (sNext : ZNext ⟶ W) (t : U ⟶ W),
      bNext ≫ sNext = 0 ∧
        sPrev = g ≫ sNext + h ≫ t := by
  let k : YNext ⊞ ZPrev ⟶ W := biprod.desc 0 sPrev
  have hk : (stepComplex
      bPrev bNext f g h comm hzero).f ≫ k = 0 := by
    dsimp [k, stepComplex]
    rw [biprod.lift_desc, comp_zero, hsPrev, zero_add]
    rfl
  obtain ⟨l, hl⟩ :=
    (ShortComplex.isWeakCokernel_iff _).mp hweak k hk
  have l_eq :
      l = biprod.desc (biprod.inl ≫ l) (biprod.inr ≫ l) := by
    apply biprod.hom_ext' <;> simp
  let sNext : ZNext ⟶ W := -(biprod.inl ≫ l)
  let t : U ⟶ W := biprod.inr ≫ l
  refine ⟨sNext, t, ?_, ?_⟩
  · have hcomponent := congrArg (fun q ↦ biprod.inl ≫ q) hl
    dsimp [k, stepComplex] at hcomponent
    rw [l_eq] at hcomponent
    dsimp [sNext]
    simpa [Category.assoc] using congrArg Neg.neg hcomponent
  · have hcomponent := congrArg (fun q ↦ biprod.inr ≫ q) hl
    dsimp [k, stepComplex] at hcomponent
    rw [l_eq] at hcomponent
    dsimp [sNext, t]
    simpa [Category.assoc] using hcomponent.symm

/-- If an explicit left-ladder step is isomorphic to a left tau-sequence,
then all three visible components of its second map belong to the chosen
categorical radical ideal. -/
theorem stepMaps_mem_radical_of_leftTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {YPrev ZPrev YNext ZNext U : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    bNext ∈ R.ideal.hom YNext ZNext ∧
      g ∈ R.ideal.hom ZPrev ZNext ∧
        h ∈ R.ideal.hom ZPrev U := by
  have hstep_mem :
      (stepComplex bPrev bNext f g h comm hzero).g ∈
        R.ideal.hom
          (stepComplex bPrev bNext f g h comm hzero).X₂
          (stepComplex bPrev bNext f g h comm hzero).X₃ := by
    exact (R.mem_iff _).2 (hS.toTauApproximation.g_radical_of_iso e)
  refine ⟨?_, ?_, ?_⟩
  · have hcomponent :=
      R.ideal.postcomp
        (biprod.fst : ZNext ⊞ U ⟶ ZNext)
        (R.ideal.precomp
          (biprod.inl : YNext ⟶ YNext ⊞ ZPrev) hstep_mem)
    simpa [stepComplex, Category.assoc] using hcomponent
  · have hcomponent :=
      R.ideal.postcomp
        (biprod.fst : ZNext ⊞ U ⟶ ZNext)
        (R.ideal.precomp
          (-(biprod.inr : ZPrev ⟶ YNext ⊞ ZPrev)) hstep_mem)
    simpa [stepComplex, Category.assoc] using hcomponent
  · have hcomponent :=
      R.ideal.postcomp
        (biprod.snd : ZNext ⊞ U ⟶ U)
        (R.ideal.precomp
          (biprod.inr : ZPrev ⟶ YNext ⊞ ZPrev) hstep_mem)
    simpa [stepComplex, Category.assoc] using hcomponent

/-- The next horizontal arrow in an explicit left-ladder step is radical. -/
theorem nextMap_mem_radical_of_leftTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {YPrev ZPrev YNext ZNext U : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    bNext ∈ R.ideal.hom YNext ZNext :=
  (stepMaps_mem_radical_of_leftTauSequence_iso_stepComplex R hS e).1

/-- `Nonempty` form of radicality of the next horizontal arrow. -/
theorem nextMap_mem_radical_of_leftTauSequence_nonempty_iso_stepComplex
    (R : NilpotentRadicalData C)
    {YPrev ZPrev YNext ZNext U : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : Nonempty
      (S ≅ stepComplex bPrev bNext f g h comm hzero)) :
    bNext ∈ R.ideal.hom YNext ZNext := by
  obtain ⟨e⟩ := e
  exact nextMap_mem_radical_of_leftTauSequence_iso_stepComplex R hS e

/-- Both connecting components in an explicit left-ladder step are
radical. -/
theorem connectingMaps_mem_radical_of_leftTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {YPrev ZPrev YNext ZNext U : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    g ∈ R.ideal.hom ZPrev ZNext ∧
      h ∈ R.ideal.hom ZPrev U :=
  (stepMaps_mem_radical_of_leftTauSequence_iso_stepComplex R hS e).2

/-- `Nonempty` form matching noncanonical mesh isomorphisms. -/
theorem connectingMaps_mem_radical_of_leftTauSequence_nonempty_iso_stepComplex
    (R : NilpotentRadicalData C)
    {YPrev ZPrev YNext ZNext U : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : Nonempty
      (S ≅ stepComplex bPrev bNext f g h comm hzero)) :
    g ∈ R.ideal.hom ZPrev ZNext ∧
      h ∈ R.ideal.hom ZPrev U := by
  obtain ⟨e⟩ := e
  exact connectingMaps_mem_radical_of_leftTauSequence_iso_stepComplex
    R hS e

/-- Family form aligned with left-ladder radical-power propagation. -/
theorem connectingMaps_mem_radical_of_leftTauSequence_stepFamily
    (R : NilpotentRadicalData C)
    (S : ℕ → ShortComplex C)
    (Y Z U : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (f : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (h : ∀ n : ℕ, Z n ⟶ U (n + 1))
    (comm : ∀ n : ℕ, f n ≫ b (n + 1) = b n ≫ g n)
    (hzero : ∀ n : ℕ, b n ≫ h n = 0)
    (hS : ∀ n : ℕ, LeftTauSequence (S n))
    (e : ∀ n : ℕ, Nonempty
      (S n ≅ stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n))) :
    (∀ n : ℕ,
      g n ∈ R.ideal.hom (Z n) (Z (n + 1))) ∧
      ∀ n : ℕ,
        h n ∈ R.ideal.hom (Z n) (U (n + 1)) := by
  constructor
  · intro n
    exact
      (connectingMaps_mem_radical_of_leftTauSequence_nonempty_iso_stepComplex
        R (hS n) (e n)).1
  · intro n
    exact
      (connectingMaps_mem_radical_of_leftTauSequence_nonempty_iso_stepComplex
        R (hS n) (e n)).2

/-- A left tau-sequence isomorphic to an explicit left-ladder step makes
that step a weak-cokernel complex. -/
theorem isWeakCokernel_stepComplex_of_leftTauSequence_nonempty_iso
    {YPrev ZPrev YNext ZNext U : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : Nonempty
      (S ≅ stepComplex bPrev bNext f g h comm hzero)) :
    ShortComplex.IsWeakCokernel
      (stepComplex bPrev bNext f g h comm hzero) := by
  obtain ⟨e⟩ := e
  exact hS.minimalWeakCokernel.1.of_iso e

end ExplicitStep

section RadicalPropagation

variable [Preadditive C]

/-- The forwards composite of the first `n` left-ladder connecting maps. -/
def forwardComposite
    (Z : ℕ → C) (g : ∀ n : ℕ, Z n ⟶ Z (n + 1)) :
    ∀ n : ℕ, Z 0 ⟶ Z n
  | 0 => 𝟙 (Z 0)
  | n + 1 => forwardComposite Z g n ≫ g n

omit [Preadditive C] in
@[simp]
theorem forwardComposite_zero
    (Z : ℕ → C) (g : ∀ n : ℕ, Z n ⟶ Z (n + 1)) :
    forwardComposite Z g 0 = 𝟙 (Z 0) :=
  rfl

omit [Preadditive C] in
@[simp]
theorem forwardComposite_succ
    (Z : ℕ → C) (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (n : ℕ) :
    forwardComposite Z g (n + 1) =
      forwardComposite Z g n ≫ g n :=
  rfl

/-- A chain of radical connecting maps has its length-`n` composite in the
`n`th ideal power. -/
theorem forwardComposite_mem_pow
    (I : HomIdeal C)
    (Z : ℕ → C) (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (hg : ∀ n : ℕ, g n ∈ I.hom (Z n) (Z (n + 1))) :
    ∀ n : ℕ,
      forwardComposite Z g n ∈ (I.pow n).hom (Z 0) (Z n)
  | 0 => by simp
  | n + 1 => by
      rw [I.pow_succ]
      exact HomIdeal.comp_mem_mul
        (forwardComposite_mem_pow I Z g hg n) (hg n)

/-- The exact abstract output needed from every explicit left-ladder step. -/
def HasCoannihilatorPropagation
    (Y Z U : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (h : ∀ n : ℕ, Z n ⟶ U (n + 1)) : Prop :=
  ∀ (n : ℕ) {W : C} (s : Z n ⟶ W), b n ≫ s = 0 →
    ∃ (sNext : Z (n + 1) ⟶ W) (t : U (n + 1) ⟶ W),
      b (n + 1) ≫ sNext = 0 ∧
        s = g n ≫ sNext + h n ≫ t

/-- A family of explicit weak-cokernel left-ladder steps supplies the
abstract coannihilator-propagation property. -/
theorem hasCoannihilatorPropagation_of_weakCokernels
    [HasBinaryBiproducts C]
    (Y Z U : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (f : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (h : ∀ n : ℕ, Z n ⟶ U (n + 1))
    (comm : ∀ n : ℕ, f n ≫ b (n + 1) = b n ≫ g n)
    (hzero : ∀ n : ℕ, b n ≫ h n = 0)
    (hweak : ∀ n : ℕ, ShortComplex.IsWeakCokernel
      (stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n))) :
    HasCoannihilatorPropagation Y Z U b g h := by
  intro n W s hs
  exact exists_next_coannihilator (hweak n) s hs

/-- Left tau-sequence models of all explicit ladder steps supply the
coannihilator propagation used in radical-power iteration. -/
theorem hasCoannihilatorPropagation_of_leftTauSequence_stepFamily
    [HasBinaryBiproducts C]
    (S : ℕ → ShortComplex C)
    (Y Z U : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (f : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (h : ∀ n : ℕ, Z n ⟶ U (n + 1))
    (comm : ∀ n : ℕ, f n ≫ b (n + 1) = b n ≫ g n)
    (hzero : ∀ n : ℕ, b n ≫ h n = 0)
    (hS : ∀ n : ℕ, LeftTauSequence (S n))
    (e : ∀ n : ℕ, Nonempty
      (S n ≅ stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n))) :
    HasCoannihilatorPropagation Y Z U b g h := by
  apply hasCoannihilatorPropagation_of_weakCokernels
    Y Z U b f g h comm hzero
  intro n
  exact isWeakCokernel_stepComplex_of_leftTauSequence_nonempty_iso
    (hS n) (e n)

/-- If all complementary terms vanish after composing from the initial
target, an initial coannihilator propagates through every finite left-ladder
prefix. -/
theorem exists_propagated_coannihilator
    (Y Z U : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (h : ∀ n : ℕ, Z n ⟶ U (n + 1))
    (hstep : HasCoannihilatorPropagation Y Z U b g h)
    (hkill : ∀ n : ℕ,
      forwardComposite Z g n ≫ h n = 0)
    {W : C} (s₀ : Z 0 ⟶ W) (hs₀ : b 0 ≫ s₀ = 0) :
    ∀ n : ℕ, ∃ s : Z n ⟶ W,
      b n ≫ s = 0 ∧ s₀ = forwardComposite Z g n ≫ s
  | 0 => ⟨s₀, hs₀, by simp⟩
  | n + 1 => by
      obtain ⟨s, hs, hs₀⟩ :=
        exists_propagated_coannihilator
          Y Z U b g h hstep hkill s₀ hs₀ n
      obtain ⟨sNext, t, hsNext, hrelation⟩ := hstep n s hs
      refine ⟨sNext, hsNext, ?_⟩
      calc
        s₀ = forwardComposite Z g n ≫ s := hs₀
        _ = forwardComposite Z g n ≫
              (g n ≫ sNext + h n ≫ t) := by rw [hrelation]
        _ = (forwardComposite Z g n ≫ g n) ≫ sNext +
              (forwardComposite Z g n ≫ h n) ≫ t := by
          simp only [Preadditive.comp_add, Category.assoc]
        _ = forwardComposite Z g (n + 1) ≫ sNext := by
          rw [hkill n, zero_comp, add_zero]
          rfl

/-- Radical-power propagation dual to Iyama 6.4.1(1)(i).

Starting from a nonzero coannihilator, some complementary morphism
`g₁ ≫ ⋯ ≫ gᵢ₋₁ ≫ hᵢ` is nonzero and lies in the corresponding
radical power. -/
theorem exists_nonzero_coremainder_in_radical_power
    (R : NilpotentRadicalData C)
    (Y Z U : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (h : ∀ n : ℕ, Z n ⟶ U (n + 1))
    (hstep : HasCoannihilatorPropagation Y Z U b g h)
    (hg : ∀ n : ℕ,
      g n ∈ R.ideal.hom (Z n) (Z (n + 1)))
    (hh : ∀ n : ℕ,
      h n ∈ R.ideal.hom (Z n) (U (n + 1)))
    {W : C} (s₀ : Z 0 ⟶ W)
    (hs₀ : b 0 ≫ s₀ = 0) (hs₀ne : s₀ ≠ 0) :
    ∃ n : ℕ,
      forwardComposite Z g n ≫ h n ∈
          (R.ideal.pow (n + 1)).hom (Z 0) (U (n + 1)) ∧
        forwardComposite Z g n ≫ h n ≠ 0 := by
  have hprefix := forwardComposite_mem_pow R.ideal Z g hg
  have hcoremainder_mem (n : ℕ) :
      forwardComposite Z g n ≫ h n ∈
        (R.ideal.pow (n + 1)).hom (Z 0) (U (n + 1)) := by
    rw [R.ideal.pow_succ]
    exact HomIdeal.comp_mem_mul (hprefix n) (hh n)
  by_contra hexists
  have hkill (n : ℕ) :
      forwardComposite Z g n ≫ h n = 0 := by
    by_contra hne
    exact hexists ⟨n, hcoremainder_mem n, hne⟩
  have hprop :=
    exists_propagated_coannihilator
      Y Z U b g h hstep hkill s₀ hs₀
  apply hs₀ne
  apply R.eq_zero_of_mem_every_power
  intro n
  obtain ⟨s, hs, heq⟩ := hprop n
  rw [heq]
  exact (R.ideal.pow n).postcomp s (hprefix n)

end RadicalPropagation

end MBDVendor.QSE.Iyama.LeftLadder
