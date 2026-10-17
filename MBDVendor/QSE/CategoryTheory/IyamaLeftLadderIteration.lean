import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderNormalization
import MBDVendor.QSE.CategoryTheory.IyamaLeftSuccessorSpecialness
import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderRadicalLayer

/-!
# Infinite and finite special left ladders from a zero boundary

This file combines target conormalization and complementary-successor
specialness into an unconditional dependent left-ladder construction.  It
then exposes flat infinite families and exact finite prefixes for Iyama,
*Tau-categories I*, Lemma 6.4.1(1)(ii).  The construction is entirely
categorical and uses no concrete algebra or module classification.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MBDVendor.QSE.Iyama.LeftLadder

open CategoricalIdeal CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- The unconditional categorical builder supplied by target normalization
and dual successor specialness. -/
def specialLeftLadderBuilder
    (T : FiniteTauCategoryData C Ind) : SpecialLeftLadderBuilder T where
  normalize a ha := chooseSpecialConormalization T a ha
  rawSuccessor_special s :=
    isSpecial_chosenLeftMesh_rawComplementSuccessor T s.p s.special

abbrev PackedSpecialCosplitState (T : FiniteTauCategoryData C Ind) :=
  Σ Y : C, SpecialCosplitState T Y

def nextConormalization
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T)
    {Y : C} (s : SpecialCosplitState T Y) :
    SpecialConormalization T s.rawSuccessor :=
  B.normalize s.rawSuccessor (B.rawSuccessor_special s)

def nextPackedCosplitState
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T)
    (p : PackedSpecialCosplitState T) :
    PackedSpecialCosplitState T :=
  ⟨(splitEpiComplement p.2.p).complement,
    (nextConormalization T B p.2).state⟩

structure SpecialLeftLadderRung
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T)
    (p : PackedSpecialCosplitState T) where
  f : p.1 ⟶ (nextPackedCosplitState T B p).1
  g : p.2.Z ⟶ (nextPackedCosplitState T B p).2.Z
  h : p.2.Z ⟶ (nextPackedCosplitState T B p).2.U
  comm :
    f ≫ (nextPackedCosplitState T B p).2.b =
      p.2.b ≫ g
  hzero : p.2.b ≫ h = 0
  meshIso : Nonempty
    (T.leftMesh p.1 ≅
      stepComplex p.2.b (nextPackedCosplitState T B p).2.b
        f g h comm hzero)

theorem nonempty_specialLeftLadderRung
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T)
    (p : PackedSpecialCosplitState T) :
    Nonempty (SpecialLeftLadderRung T B p) := by
  rcases p with ⟨Y, s⟩
  let N := nextConormalization T B s
  obtain ⟨e⟩ := N.arrowIso
  let eY : (splitEpiComplement s.p).complement ≅
      (splitEpiComplement s.p).complement :=
    Arrow.leftFunc.mapIso e
  let eX : (T.leftMesh Y).X₃ ≅ biprod N.state.Z N.state.U :=
    Arrow.rightFunc.mapIso e
  have heNext :
      ((splitEpiComplement s.p).inclusion ≫ (T.leftMesh Y).g) ≫
          eX.hom =
        eY.hom ≫
          biprod.lift N.state.b
            (0 : (splitEpiComplement s.p).complement ⟶ N.state.U) := by
    change s.rawSuccessor ≫ e.hom.right =
      e.hom.left ≫
        biprod.lift N.state.b
          (0 : (splitEpiComplement s.p).complement ⟶ N.state.U)
    exact e.hom.w.symm
  obtain ⟨f, g, h, comm, hzero, emesh⟩ :=
    exists_stepComplex_iso_of_split_cofactor_and_padded_next
      (T.leftMesh Y) (T.leftTermIso Y) s.p
      (splitEpiComplement s.p) N.state.b eY eX heNext
  exact ⟨
    { f := f
      g := g
      h := h
      comm := comm
      hzero := hzero
      meshIso := emesh }⟩

def chooseSpecialLeftLadderRung
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T)
    (p : PackedSpecialCosplitState T) :
    SpecialLeftLadderRung T B p :=
  Classical.choice (nonempty_specialLeftLadderRung T B p)

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
theorem isSpecial_of_isZero_target
    (R : NilpotentRadicalData C)
    {X Z : C} (hZ : IsZero Z) (a : X ⟶ Z) :
    IsSpecial R a := by
  have ha : a = 0 := hZ.eq_of_tgt a 0
  constructor
  · rw [ha]
    intro g
    simpa only [zero_comp, sub_zero] using
      (inferInstance : IsIso (CategoryStruct.id X))
  · intro r hr
    have hr0 : r = 0 := hZ.eq_of_tgt r 0
    rw [ha, hr0, add_zero]
    exact ⟨Iso.refl _⟩

def zeroInitialCosplitState
    (T : FiniteTauCategoryData C Ind) (U₀ : C) :
    SpecialCosplitState T U₀ := by
  let p : (T.leftMesh U₀).X₂ ⟶ (0 : C) := 0
  have hp : IsSplitEpi p := by
    apply IsSplitEpi.mk'
    exact
      { section_ := 0
        id := (isZero_zero C).eq_of_src _ _ }
  letI : IsSplitEpi p := hp
  exact
    { Z := 0
      U := 0
      p := p
      p_split := hp
      special :=
        isSpecial_of_isZero_target T.radical (isZero_zero C)
          ((T.leftTermIso U₀).inv ≫ (T.leftMesh U₀).f ≫ p) }

def zeroInitialPackedCosplitState
    (T : FiniteTauCategoryData C Ind) (U₀ : C) :
    PackedSpecialCosplitState T :=
  ⟨U₀, zeroInitialCosplitState T U₀⟩

def iteratePackedCosplitState
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T)
    (p₀ : PackedSpecialCosplitState T) :
    ℕ → PackedSpecialCosplitState T
  | 0 => p₀
  | n + 1 => nextPackedCosplitState T B
      (iteratePackedCosplitState T B p₀ n)

/-! ## Flat infinite ladder and exact finite prefixes -/

structure InfiniteSpecialLeftLadderFromZero
    (T : FiniteTauCategoryData C Ind) (U₀ : C) where
  Y : ℕ → C
  Z : ℕ → C
  U : ℕ → C
  b : ∀ n, Y n ⟶ Z n
  b_special : ∀ n, IsSpecial T.radical (b n)
  initialSourceIso : U₀ ≅ Y 0
  initialTargetZero : IsZero (Z 0)
  b_zero : b 0 = 0
  f : ∀ n, Y n ⟶ Y (n + 1)
  g : ∀ n, Z n ⟶ Z (n + 1)
  h : ∀ n, Z n ⟶ U (n + 1)
  comm : ∀ n, f n ≫ b (n + 1) = b n ≫ g n
  hzero : ∀ n, b n ≫ h n = 0
  meshIso : ∀ n, Nonempty
    (T.leftMesh (Y n) ≅
      stepComplex (b n) (b (n + 1))
        (f n) (g n) (h n) (comm n) (hzero n))

def infiniteSpecialLeftLadderFromZero
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T) (U₀ : C) :
    InfiniteSpecialLeftLadderFromZero T U₀ := by
  let p₀ := zeroInitialPackedCosplitState T U₀
  let P : ℕ → PackedSpecialCosplitState T :=
    iteratePackedCosplitState T B p₀
  let R : ∀ n, SpecialLeftLadderRung T B (P n) :=
    fun n ↦ chooseSpecialLeftLadderRung T B (P n)
  exact
    { Y := fun n ↦ (P n).1
      Z := fun n ↦ (P n).2.Z
      U := fun n ↦ (P n).2.U
      b := fun n ↦ (P n).2.b
      b_special := fun n ↦ (P n).2.b_special
      initialSourceIso := Iso.refl U₀
      initialTargetZero := isZero_zero C
      b_zero := (isZero_zero C).eq_of_tgt _ _
      f := fun n ↦ (R n).f
      g := fun n ↦ (R n).g
      h := fun n ↦ (R n).h
      comm := fun n ↦ (R n).comm
      hzero := fun n ↦ (R n).hzero
      meshIso := fun n ↦ (R n).meshIso }

/-- The unconditional chosen infinite left ladder, with both dual-special
operations supplied by the categorical construction in this package. -/
def chosenInfiniteSpecialLeftLadderFromZero
    (T : FiniteTauCategoryData C Ind) (U₀ : C) :
    InfiniteSpecialLeftLadderFromZero T U₀ :=
  infiniteSpecialLeftLadderFromZero T (specialLeftLadderBuilder T) U₀

/-- The compiled dual radical layer applies directly to the flat ladder.
A nonzero degree-n morphism out of the original boundary object forces the
domain of the nth left-ladder arrow to be nonzero. -/
theorem InfiniteSpecialLeftLadderFromZero.terminalDomain_not_isZero
    {T : FiniteTauCategoryData C Ind} {U₀ : C}
    (L : InfiniteSpecialLeftLadderFromZero T U₀)
    (n : ℕ) {W : C} (q : U₀ ⟶ W)
    (hq : q ∈ (T.radical.ideal.pow n).hom U₀ W)
    (hqne : q ≠ 0) :
    ¬ IsZero (L.Y n) := by
  let r : L.Y 0 ⟶ W := L.initialSourceIso.inv ≫ q
  have hr : r ∈ (T.radical.ideal.pow n).hom (L.Y 0) W :=
    (T.radical.ideal.pow n).precomp L.initialSourceIso.inv hq
  have hrne : r ≠ 0 := by
    intro hrzero
    apply hqne
    calc
      q = L.initialSourceIso.hom ≫
          (L.initialSourceIso.inv ≫ q) := by simp
      _ = 0 := by rw [show L.initialSourceIso.inv ≫ q = 0 from hrzero,
        comp_zero]
  exact not_isZero_domain_of_nonzero_mem_pow
    T.radical n (fun k ↦ T.leftMesh (L.Y k))
    L.Y L.Z L.U L.b L.f L.g L.h L.comm L.hzero
    (fun k ↦ T.leftTau (L.Y k)) L.meshIso L.b_zero r hr hrne

structure FiniteSpecialLeftLadderFromZero
    (T : FiniteTauCategoryData C Ind) (U₀ : C) (n : ℕ) where
  Y : Fin (n + 1) → C
  Z : Fin (n + 1) → C
  U : Fin (n + 1) → C
  b : ∀ i, Y i ⟶ Z i
  b_special : ∀ i, IsSpecial T.radical (b i)
  initialSourceIso : U₀ ≅ Y 0
  initialTargetZero : IsZero (Z 0)
  b_zero : b 0 = 0
  f : ∀ i : Fin n, Y i.castSucc ⟶ Y i.succ
  g : ∀ i : Fin n, Z i.castSucc ⟶ Z i.succ
  h : ∀ i : Fin n, Z i.castSucc ⟶ U i.succ
  comm : ∀ i : Fin n, f i ≫ b i.succ = b i.castSucc ≫ g i
  hzero : ∀ i : Fin n, b i.castSucc ≫ h i = 0
  meshIso : ∀ i : Fin n, Nonempty
    (T.leftMesh (Y i.castSucc) ≅
      stepComplex (b i.castSucc) (b i.succ)
        (f i) (g i) (h i) (comm i) (hzero i))

def InfiniteSpecialLeftLadderFromZero.prefix
    {T : FiniteTauCategoryData C Ind} {U₀ : C}
    (L : InfiniteSpecialLeftLadderFromZero T U₀) (n : ℕ) :
    FiniteSpecialLeftLadderFromZero T U₀ n where
  Y i := L.Y i
  Z i := L.Z i
  U i := L.U i
  b i := L.b i
  b_special i := L.b_special i
  initialSourceIso := L.initialSourceIso
  initialTargetZero := L.initialTargetZero
  b_zero := L.b_zero
  f i := L.f i
  g i := L.g i
  h i := L.h i
  comm i := L.comm i
  hzero i := L.hzero i
  meshIso i := L.meshIso i

def finiteSpecialLeftLadderFromZero
    (T : FiniteTauCategoryData C Ind)
    (B : SpecialLeftLadderBuilder T) (U₀ : C) (n : ℕ) :
    FiniteSpecialLeftLadderFromZero T U₀ n :=
  (infiniteSpecialLeftLadderFromZero T B U₀).prefix n

/-- The unconditional chosen finite prefix of a zero-initial special left
ladder. -/
def chosenFiniteSpecialLeftLadderFromZero
    (T : FiniteTauCategoryData C Ind) (U₀ : C) (n : ℕ) :
    FiniteSpecialLeftLadderFromZero T U₀ n :=
  finiteSpecialLeftLadderFromZero T (specialLeftLadderBuilder T) U₀ n

/-- The dual radical-layer conclusion on the literal terminal object of the
chosen finite prefix. -/
theorem chosenFiniteSpecialLeftLadderFromZero_terminalDomain_not_isZero
    (T : FiniteTauCategoryData C Ind) (U₀ : C)
    (n : ℕ) {W : C} (q : U₀ ⟶ W)
    (hq : q ∈ (T.radical.ideal.pow n).hom U₀ W)
    (hqne : q ≠ 0) :
    ¬ IsZero
      ((chosenFiniteSpecialLeftLadderFromZero T U₀ n).Y (Fin.last n)) := by
  change ¬ IsZero ((chosenInfiniteSpecialLeftLadderFromZero T U₀).Y n)
  exact (chosenInfiniteSpecialLeftLadderFromZero T U₀).terminalDomain_not_isZero
    n q hq hqne

def FiniteSpecialLeftLadderFromZero.paddedArrow
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (L : FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) :
    L.Y i ⟶ biprod (L.Z i) (L.U i) :=
  biprod.lift (L.b i) 0

end MBDVendor.QSE.Iyama.LeftLadder
