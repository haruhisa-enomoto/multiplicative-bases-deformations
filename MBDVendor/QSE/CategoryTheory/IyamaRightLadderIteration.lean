import MBDVendor.QSE.CategoryTheory.IyamaRightSuccessorSpecialness

/-!
# Infinite special right ladders

This file iterates the split-complement successor construction from Iyama,
*Tau-categories I*, Section 3.2. Starting from an arbitrary special arrow,
it produces the full dependent family of normalized special arrows and chosen
right-mesh ladder rungs. The zero-padded summand of the initial normalization
is retained explicitly for the radical-power argument in Lemma 6.4.1(1)(i).

The construction is entirely categorical: it uses no presentation or
classification of a concrete algebra or its modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.RightLadder

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- One normalized special split factor through a chosen right mesh.  The
object `U` remembers the zero-padded source summand of the arrow which was
normalized to obtain this state. -/
structure SpecialSplitState (T : FiniteRightTauCategoryData C Ind) (Y : C) where
  Z : C
  U : C
  j : Z ⟶ (T.rightMesh Y).X₂
  [j_split : IsSplitMono j]
  special : IsSpecial T.radical
    (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom)

instance {T : FiniteRightTauCategoryData C Ind} {Y : C}
    (s : SpecialSplitState T Y) : IsSplitMono s.j :=
  s.j_split

namespace SpecialSplitState

variable {T : FiniteRightTauCategoryData C Ind} {Y : C}

/-- The essential special arrow represented by a normalized state. -/
def b (s : SpecialSplitState T Y) : s.Z ⟶ Y :=
  s.j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom

theorem b_special (s : SpecialSplitState T Y) :
    IsSpecial T.radical s.b :=
  s.special

/-- The raw successor obtained from the complement of the split mesh
factor. -/
def rawSuccessor (s : SpecialSplitState T Y) :
    (T.rightMesh Y).X₁ ⟶ (splitMonoComplement s.j).complement :=
  (T.rightMesh Y).f ≫ (splitMonoComplement s.j).projection

theorem rawSuccessor_special (s : SpecialSplitState T Y) :
    IsSpecial T.radical s.rawSuccessor :=
  isSpecial_chosenRightMesh_rawComplementSuccessor T s.j s.special

end SpecialSplitState

/-- A special arrow together with one chosen split-factor normalization. -/
structure SpecialNormalization
    (T : FiniteRightTauCategoryData C Ind) {X Y : C} (a : X ⟶ Y) where
  state : SpecialSplitState T Y
  arrowIso : Nonempty
    (Arrow.mk a ≅
      Arrow.mk
        (biprod.desc state.b (0 : state.U ⟶ Y)))

/-- Choose the special split-factor normal form of an arbitrary special
arrow. -/
def chooseSpecialNormalization
    (T : FiniteRightTauCategoryData C Ind)
    {X Y : C} (a : X ⟶ Y) (ha : IsSpecial T.radical a) :
    SpecialNormalization T a := by
  let h := exists_special_splitFactor_normalForm T a ha
  let Z := Classical.choose h
  let hZ := Classical.choose_spec h
  let U := Classical.choose hZ
  let hZU := Classical.choose_spec hZ
  let j := Classical.choose hZU
  let hjse := Classical.choose_spec hZU
  have hj : IsSplitMono j := hjse.1
  have hb : IsSpecial T.radical
      (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom) :=
    hjse.2.1
  have e : Nonempty
      (Arrow.mk a ≅
        Arrow.mk
          (biprod.desc
            (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom)
            (0 : U ⟶ Y))) :=
    hjse.2.2
  letI : IsSplitMono j := hj
  exact
    { state :=
        { Z := Z
          U := U
          j := j
          j_split := hj
          special := hb }
      arrowIso := e }

/-- Pack a dependent state together with its current right endpoint. -/
abbrev PackedSpecialSplitState (T : FiniteRightTauCategoryData C Ind) :=
  Σ Y : C, SpecialSplitState T Y

/-- Normalize the raw successor of a state. -/
def nextNormalization
    (T : FiniteRightTauCategoryData C Ind) {Y : C}
    (s : SpecialSplitState T Y) :
    SpecialNormalization T s.rawSuccessor :=
  chooseSpecialNormalization T s.rawSuccessor s.rawSuccessor_special

/-- The next packed state in the infinite special right ladder. -/
def nextPackedState
    (T : FiniteRightTauCategoryData C Ind)
    (p : PackedSpecialSplitState T) : PackedSpecialSplitState T :=
  ⟨(splitMonoComplement p.2.j).complement,
    (nextNormalization T p.2).state⟩

/-- All maps, relations, and the chosen-mesh identification in one
successive special right-ladder rung. -/
structure SpecialRightLadderRung
    (T : FiniteRightTauCategoryData C Ind)
    (p : PackedSpecialSplitState T) where
  f : (nextPackedState T p).1 ⟶ p.1
  g : (nextPackedState T p).2.Z ⟶ p.2.Z
  h : (nextPackedState T p).2.U ⟶ p.2.Z
  comm : (nextPackedState T p).2.b ≫ f = g ≫ p.2.b
  hzero : h ≫ p.2.b = 0
  meshIso : Nonempty
    (T.rightMesh p.1 ≅
      stepComplex p.2.b (nextPackedState T p).2.b
        f g h comm hzero)

/-- Every normalized special state has a next explicit right-ladder rung. -/
theorem nonempty_specialRightLadderRung
    (T : FiniteRightTauCategoryData C Ind)
    (p : PackedSpecialSplitState T) :
    Nonempty (SpecialRightLadderRung T p) := by
  rcases p with ⟨Y, s⟩
  let N := nextNormalization T s
  obtain ⟨e⟩ := N.arrowIso
  let eX : (T.rightMesh Y).X₁ ≅ N.state.Z ⊞ N.state.U :=
    Arrow.leftFunc.mapIso e
  let eY : (splitMonoComplement s.j).complement ≅
      (splitMonoComplement s.j).complement :=
    Arrow.rightFunc.mapIso e
  have heNext :
      ((T.rightMesh Y).f ≫ (splitMonoComplement s.j).projection) ≫
          eY.hom =
        eX.hom ≫
          biprod.desc N.state.b
            (0 : N.state.U ⟶ (splitMonoComplement s.j).complement) := by
    change s.rawSuccessor ≫ e.hom.right =
      e.hom.left ≫ biprod.desc N.state.b
        (0 : N.state.U ⟶ (splitMonoComplement s.j).complement)
    exact e.hom.w.symm
  obtain ⟨f, g, h, comm, hzero, emesh⟩ :=
    exists_chosen_rightMesh_step_of_split_factor_and_padded_next
      T s.j N.state.b eX eY heNext
  exact ⟨
    { f := f
      g := g
      h := h
      comm := comm
      hzero := hzero
      meshIso := emesh }⟩

/-- A chosen rung; the choice is immaterial to the existence theorem. -/
def chooseSpecialRightLadderRung
    (T : FiniteRightTauCategoryData C Ind)
    (p : PackedSpecialSplitState T) :
    SpecialRightLadderRung T p :=
  Classical.choice (nonempty_specialRightLadderRung T p)

/-- Primitive recursion of the normalized special states. -/
def iteratePackedState
    (T : FiniteRightTauCategoryData C Ind)
    (p₀ : PackedSpecialSplitState T) : ℕ → PackedSpecialSplitState T
  | 0 => p₀
  | n + 1 => nextPackedState T (iteratePackedState T p₀ n)

/-- An infinite special right ladder beginning at an arbitrary arrow.

`U 0` is the zero-padded branch in the normalization of the initial arrow;
the rung at `n` uses `U (n+1)`, exactly as in Iyama's displayed ladder. -/
structure InfiniteSpecialRightLadder
    (T : FiniteRightTauCategoryData C Ind)
    {X Y₀ : C} (a₀ : X ⟶ Y₀) where
  Y : ℕ → C
  Z : ℕ → C
  U : ℕ → C
  b : ∀ n, Z n ⟶ Y n
  b_special : ∀ n, IsSpecial T.radical (b n)
  initialIso : Nonempty
    (Arrow.mk a₀ ≅
      Arrow.mk (biprod.desc (b 0) (0 : U 0 ⟶ Y 0)))
  f : ∀ n, Y (Nat.succ n) ⟶ Y n
  g : ∀ n, Z (Nat.succ n) ⟶ Z n
  h : ∀ n, U (Nat.succ n) ⟶ Z n
  comm : ∀ n, b (Nat.succ n) ≫ f n = g n ≫ b n
  hzero : ∀ n, h n ≫ b n = 0
  meshIso : ∀ n, Nonempty
    (T.rightMesh (Y n) ≅
      stepComplex (b n) (b (Nat.succ n))
        (f n) (g n) (h n) (comm n) (hzero n))

/-- Construct the dependent infinite right ladder of an arbitrary special
arrow.  All choices are categorical and classification-free. -/
def infiniteSpecialRightLadder
    (T : FiniteRightTauCategoryData C Ind)
    {X Y₀ : C} (a₀ : X ⟶ Y₀)
    (ha₀ : IsSpecial T.radical a₀) :
    InfiniteSpecialRightLadder T a₀ := by
  let N₀ := chooseSpecialNormalization T a₀ ha₀
  let p₀ : PackedSpecialSplitState T := ⟨Y₀, N₀.state⟩
  let P : ℕ → PackedSpecialSplitState T := iteratePackedState T p₀
  let R : ∀ n, SpecialRightLadderRung T (P n) :=
    fun n ↦ chooseSpecialRightLadderRung T (P n)
  exact
    { Y := fun n ↦ (P n).1
      Z := fun n ↦ (P n).2.Z
      U := fun n ↦ (P n).2.U
      b := fun n ↦ (P n).2.b
      b_special := fun n ↦ (P n).2.b_special
      initialIso := N₀.arrowIso
      f := fun n ↦ (R n).f
      g := fun n ↦ (R n).g
      h := fun n ↦ (R n).h
      comm := fun n ↦ (R n).comm
      hzero := fun n ↦ (R n).hzero
      meshIso := fun n ↦ (R n).meshIso }

end MBDVendor.QSE.Iyama.RightLadder
