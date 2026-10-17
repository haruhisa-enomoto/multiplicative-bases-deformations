import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderPropagation
import MBDVendor.QSE.CategoryTheory.IyamaRightSuccessorSpecialness

/-!
# Radical-layer factorization in Iyama left ladders

This file proves the dual radical-layer calculation used in Iyama,
*Tau-categories I*, Lemma 6.4.1(1)(ii).  A morphism in the `n`th radical
power out of the source of a zero-initial left ladder factors, after
precomposition by an annihilator of the initial arrow, through the first
`n` domain maps.  Consequently a nonzero such morphism forces the `n`th
left-ladder domain to be nonzero.

The argument is entirely categorical and uses no concrete algebra or module
classification.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.LeftLadder

open CategoricalIdeal CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- One left mesh lowers a radical-power factor by one, with one component
along the next domain and one along the current essential arrow. -/
theorem exists_step_factor_of_mem_pow_succ
    [HasBinaryBiproducts C]
    (R : NilpotentRadicalData C)
    {YPrev ZPrev YNext ZNext U W : C}
    {bPrev : YPrev ⟶ ZPrev} {bNext : YNext ⟶ ZNext}
    {f : YPrev ⟶ YNext} {g : ZPrev ⟶ ZNext}
    {h : ZPrev ⟶ U}
    {comm : f ≫ bNext = bPrev ≫ g}
    {hzero : bPrev ≫ h = 0}
    {S : ShortComplex C}
    (hS : LeftTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero)
    (n : ℕ) {r : YPrev ⟶ W}
    (hr : r ∈ (R.ideal.pow (n + 1)).hom YPrev W) :
    ∃ (rNext : YNext ⟶ W),
      rNext ∈ (R.ideal.pow n).hom YNext W ∧
        ∃ (t : ZPrev ⟶ W),
          t ∈ (R.ideal.pow n).hom ZPrev W ∧
            r = f ≫ rNext + bPrev ≫ t := by
  let e₁ : S.X₁ ≅ YPrev := ShortComplex.π₁.mapIso e
  let e₂ : S.X₂ ≅ YNext ⊞ ZPrev := ShortComplex.π₂.mapIso e
  let rS : S.X₁ ⟶ W := e₁.hom ≫ r
  have hrS :
      rS ∈ (R.ideal.pow (n + 1)).hom S.X₁ W :=
    (R.ideal.pow (n + 1)).precomp e₁.hom hr
  obtain ⟨q, hq, hSq⟩ :=
    RightLadder.exists_factor_through_tau_f_of_mem_pow_succ
      R hS.toTauApproximation n hrS
  let qT : YNext ⊞ ZPrev ⟶ W :=
    e₂.inv ≫ q
  have hqT :
      qT ∈ (R.ideal.pow n).hom
        (YNext ⊞ ZPrev) W :=
    (R.ideal.pow n).precomp e₂.inv hq
  have hTq :
      (stepComplex bPrev bNext f g h comm hzero).f ≫ qT = r := by
    change biprod.lift f bPrev ≫ qT = r
    calc
      biprod.lift f bPrev ≫ qT =
          e₁.inv ≫ S.f ≫ q := by
            change
              (stepComplex bPrev bNext f g h comm hzero).f ≫
                  e.inv.τ₂ ≫ q =
                e.inv.τ₁ ≫ S.f ≫ q
            exact e.inv.comm₁₂_assoc q |>.symm
      _ = e₁.inv ≫ rS := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ e₁.inv ≫ z) hSq
      _ = r := by simpa only [rS] using e₁.inv_hom_id_assoc r
  let rNext : YNext ⟶ W := biprod.inl ≫ qT
  let t : ZPrev ⟶ W := biprod.inr ≫ qT
  refine ⟨rNext, (R.ideal.pow n).precomp biprod.inl hqT,
    t, (R.ideal.pow n).precomp biprod.inr hqT, ?_⟩
  rw [← hTq]
  change biprod.lift f bPrev ≫ qT =
    f ≫ (biprod.inl ≫ qT) + bPrev ≫ (biprod.inr ≫ qT)
  have hqT_desc :
      qT = biprod.desc (biprod.inl ≫ qT) (biprod.inr ≫ qT) := by
    apply biprod.hom_ext' <;> simp
  calc
    biprod.lift f bPrev ≫ qT =
        biprod.lift f bPrev ≫
          biprod.desc (biprod.inl ≫ qT) (biprod.inr ≫ qT) := by
            exact congrArg (fun z ↦ biprod.lift f bPrev ≫ z) hqT_desc
    _ = f ≫ (biprod.inl ≫ qT) +
          bPrev ≫ (biprod.inr ≫ qT) := by rw [biprod.lift_desc]

omit [Preadditive C] in
/-- Removing the first index from a family removes the first factor from its
forward composite. -/
theorem comp_forwardComposite_tail
    (Y : ℕ → C) (f : ∀ n : ℕ, Y n ⟶ Y (n + 1)) (n : ℕ) :
    f 0 ≫ forwardComposite (fun k ↦ Y (k + 1)) (fun k ↦ f (k + 1)) n =
      forwardComposite Y f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [forwardComposite_succ, forwardComposite_succ,
        ← Category.assoc, ih]

/-- The dual radical-layer factorization used in Iyama 6.4.1(1)(ii).

If a prefix `p` annihilates the current left-ladder arrow, precomposing a
`J^n` morphism by `p` makes it factor through the first `n` left-ladder
domain maps. -/
theorem exists_factor_through_forwardComposite
    [HasBinaryBiproducts C]
    (R : NilpotentRadicalData C)
    (n : ℕ)
    (S : ℕ → ShortComplex C)
    (Y Z U : ℕ → C)
    (b : ∀ k : ℕ, Y k ⟶ Z k)
    (f : ∀ k : ℕ, Y k ⟶ Y (k + 1))
    (g : ∀ k : ℕ, Z k ⟶ Z (k + 1))
    (h : ∀ k : ℕ, Z k ⟶ U (k + 1))
    (comm : ∀ k : ℕ, f k ≫ b (k + 1) = b k ≫ g k)
    (hzero : ∀ k : ℕ, b k ≫ h k = 0)
    (hS : ∀ k : ℕ, LeftTauSequence (S k))
    (e : ∀ k : ℕ, Nonempty
      (S k ≅ stepComplex (b k) (b (k + 1)) (f k) (g k) (h k)
        (comm k) (hzero k)))
    {P W : C} (p : P ⟶ Y 0) (hp : p ≫ b 0 = 0)
    {r : Y 0 ⟶ W} (hr : r ∈ (R.ideal.pow n).hom (Y 0) W) :
    ∃ t : Y n ⟶ W,
      p ≫ r = p ≫ forwardComposite Y f n ≫ t := by
  induction n generalizing S Y Z U b f g h with
  | zero =>
      exact ⟨r, by simp⟩
  | succ n ih =>
      obtain ⟨e₀⟩ := e 0
      obtain ⟨rNext, hrNext, t₀, ht₀, hrEq⟩ :=
        exists_step_factor_of_mem_pow_succ R (hS 0) e₀ n hr
      let S' : ℕ → ShortComplex C := fun k ↦ S (k + 1)
      let Y' : ℕ → C := fun k ↦ Y (k + 1)
      let Z' : ℕ → C := fun k ↦ Z (k + 1)
      let U' : ℕ → C := fun k ↦ U (k + 1)
      let b' : ∀ k : ℕ, Y' k ⟶ Z' k := fun k ↦ b (k + 1)
      let f' : ∀ k : ℕ, Y' k ⟶ Y' (k + 1) := fun k ↦ f (k + 1)
      let g' : ∀ k : ℕ, Z' k ⟶ Z' (k + 1) := fun k ↦ g (k + 1)
      let h' : ∀ k : ℕ, Z' k ⟶ U' (k + 1) := fun k ↦ h (k + 1)
      have comm' : ∀ k : ℕ, f' k ≫ b' (k + 1) = b' k ≫ g' k :=
        fun k ↦ comm (k + 1)
      have hzero' : ∀ k : ℕ, b' k ≫ h' k = 0 :=
        fun k ↦ hzero (k + 1)
      have hS' : ∀ k : ℕ, LeftTauSequence (S' k) :=
        fun k ↦ hS (k + 1)
      have e' : ∀ k : ℕ, Nonempty
          (S' k ≅ stepComplex (b' k) (b' (k + 1)) (f' k) (g' k) (h' k)
            (comm' k) (hzero' k)) :=
        fun k ↦ e (k + 1)
      have hp' : (p ≫ f 0) ≫ b' 0 = 0 := by
        calc
          (p ≫ f 0) ≫ b' 0 = p ≫ (f 0 ≫ b 1) := Category.assoc _ _ _
          _ = p ≫ (b 0 ≫ g 0) := by rw [comm 0]
          _ = (p ≫ b 0) ≫ g 0 := (Category.assoc _ _ _).symm
          _ = 0 := by rw [hp, zero_comp]
      obtain ⟨t, ht⟩ :=
        ih S' Y' Z' U' b' f' g' h' comm' hzero' hS' e'
          (p ≫ f 0) hp' hrNext
      refine ⟨t, ?_⟩
      calc
        p ≫ r = p ≫ (f 0 ≫ rNext + b 0 ≫ t₀) := by rw [hrEq]
        _ = (p ≫ f 0) ≫ rNext := by
          simp only [Preadditive.comp_add, ← Category.assoc, hp, zero_comp,
            add_zero]
        _ = (p ≫ f 0) ≫ forwardComposite Y' f' n ≫ t := ht
        _ = p ≫ (f 0 ≫ forwardComposite Y' f' n) ≫ t := by
          simp only [Category.assoc]
        _ = p ≫ forwardComposite Y f (n + 1) ≫ t := by
          change p ≫
              (f 0 ≫ forwardComposite
                (fun k ↦ Y (k + 1)) (fun k ↦ f (k + 1)) n) ≫ t = _
          rw [comp_forwardComposite_tail]

/-- A nonzero `J^n` morphism out of the source of a zero-initial left ladder
forces the domain of its `n`th arrow to be nonzero. -/
theorem not_isZero_domain_of_nonzero_mem_pow
    [HasBinaryBiproducts C]
    (R : NilpotentRadicalData C)
    (n : ℕ)
    (S : ℕ → ShortComplex C)
    (Y Z U : ℕ → C)
    (b : ∀ k : ℕ, Y k ⟶ Z k)
    (f : ∀ k : ℕ, Y k ⟶ Y (k + 1))
    (g : ∀ k : ℕ, Z k ⟶ Z (k + 1))
    (h : ∀ k : ℕ, Z k ⟶ U (k + 1))
    (comm : ∀ k : ℕ, f k ≫ b (k + 1) = b k ≫ g k)
    (hzero : ∀ k : ℕ, b k ≫ h k = 0)
    (hS : ∀ k : ℕ, LeftTauSequence (S k))
    (e : ∀ k : ℕ, Nonempty
      (S k ≅ stepComplex (b k) (b (k + 1)) (f k) (g k) (h k)
        (comm k) (hzero k)))
    (hbzero : b 0 = 0)
    {W : C} (r : Y 0 ⟶ W)
    (hr : r ∈ (R.ideal.pow n).hom (Y 0) W) (hrne : r ≠ 0) :
    ¬ IsZero (Y n) := by
  intro hYn
  obtain ⟨t, ht⟩ :=
    exists_factor_through_forwardComposite R n S Y Z U b f g h comm hzero
      hS e (𝟙 (Y 0)) (by simp [hbzero]) hr
  apply hrne
  calc
    r = forwardComposite Y f n ≫ t := by simpa using ht
    _ = 0 := by
      rw [hYn.eq_of_src t 0, comp_zero]

end MBDVendor.QSE.Iyama.LeftLadder
