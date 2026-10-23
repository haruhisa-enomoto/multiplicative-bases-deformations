module

public import MBDVendor.QSE.CategoryTheory.IyamaReversedDomination

/-!
# Reversing a genuine finite right-ladder window over `Fin.rev`

This file is a pure dependent-reindexing adapter.  It introduces no new
representation-theoretic or concrete-module input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.TauSequenceComparison

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- A family of morphisms commutes with transport of its index. -/
theorem familyHom_naturality
    (F G : ℕ → C) (b : ∀ k, F k ⟶ G k)
    {m n : ℕ} (e : m = n) :
    b m ≫ eqToHom (congrArg G e) =
      eqToHom (congrArg F e) ≫ b n := by
  subst n
  simp

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Transport the connecting square of one genuine right-ladder rung from
indices `j+1 → j` to propositionally equal indices `a → c`. -/
theorem transported_right_rung_comm
    (Y Z : ℕ → C) (b : ∀ k, Z k ⟶ Y k)
    {a c j : ℕ} (ea : a = j + 1) (ec : j = c)
    (f : Y (j + 1) ⟶ Y j) (g : Z (j + 1) ⟶ Z j)
    (comm : b (j + 1) ≫ f = g ≫ b j) :
    b a ≫
        (eqToHom (congrArg Y ea) ≫ f ≫
          eqToHom (congrArg Y ec)) =
      (eqToHom (congrArg Z ea) ≫ g ≫
          eqToHom (congrArg Z ec)) ≫ b c := by
  subst a
  subst c
  simpa using comm

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Transport the zero relation for the complementary map of one genuine
right-ladder rung. -/
theorem transported_right_rung_hzero
    (Y Z U : ℕ → C) (b : ∀ k, Z k ⟶ Y k)
    {a c j : ℕ} (ea : a = j + 1) (ec : j = c)
    (h : U (j + 1) ⟶ Z j) (hzero : h ≫ b j = 0) :
    (eqToHom (congrArg U ea) ≫ h ≫
        eqToHom (congrArg Z ec)) ≫ b c = 0 := by
  subst a
  subst c
  simpa using hzero

/-- The explicit right-step complex is invariant, up to componentwise
equality isomorphisms, under transport of its two endpoint indices. -/
def transported_right_step_iso
    (Y Z U : ℕ → C) (b : ∀ k, Z k ⟶ Y k)
    {a c j : ℕ} (ea : a = j + 1) (ec : j = c)
    (f : Y (j + 1) ⟶ Y j) (g : Z (j + 1) ⟶ Z j)
    (h : U (j + 1) ⟶ Z j)
    (comm : b (j + 1) ≫ f = g ≫ b j)
    (hzero : h ≫ b j = 0) :
    RightLadder.stepComplex (b j) (b (j + 1)) f g h comm hzero ≅
      RightLadder.stepComplex (b c) (b a)
        (eqToHom (congrArg Y ea) ≫ f ≫
          eqToHom (congrArg Y ec))
        (eqToHom (congrArg Z ea) ≫ g ≫
          eqToHom (congrArg Z ec))
        (eqToHom (congrArg U ea) ≫ h ≫
          eqToHom (congrArg Z ec))
        (transported_right_rung_comm Y Z b ea ec f g comm)
        (transported_right_rung_hzero Y Z U b ea ec h hzero) := by
  subst a
  subst c
  simpa using
    (Iso.refl
      (RightLadder.stepComplex (b j) (b (j + 1)) f g h comm hzero))

/-- Restrict an actual infinite special right ladder to its first `n+1`
arrows and reverse that finite window using `Fin.rev`. -/
def ReversedRightPrefix.ofInfiniteSpecialRightLadder
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ) :
    ReversedRightPrefix T n := by
  let revIndex : Fin (n + 1) → ℕ := fun i ↦ i.rev.val
  let Z : Fin (n + 1) → C := fun i ↦ R.Z (revIndex i)
  let Y : Fin (n + 1) → C := fun i ↦ R.Y (revIndex i)
  let U : Fin (n + 1) → C := fun i ↦ R.U (revIndex i)
  let b : ∀ i, Z i ⟶ Y i := fun i ↦ R.b (revIndex i)
  let rungIndex : Fin n → ℕ := fun i ↦ i.rev.val
  have ea : ∀ i : Fin n,
      revIndex i.castSucc = rungIndex i + 1 := by
    intro i
    exact congrArg Fin.val (Fin.rev_castSucc i)
  have ec : ∀ i : Fin n,
      rungIndex i = revIndex i.succ := by
    intro i
    exact congrArg Fin.val (Fin.rev_succ i).symm
  let f : ∀ i : Fin n, Y i.castSucc ⟶ Y i.succ := fun i ↦
    eqToHom (congrArg R.Y (ea i)) ≫ R.f (rungIndex i) ≫
      eqToHom (congrArg R.Y (ec i))
  let g : ∀ i : Fin n, Z i.castSucc ⟶ Z i.succ := fun i ↦
    eqToHom (congrArg R.Z (ea i)) ≫ R.g (rungIndex i) ≫
      eqToHom (congrArg R.Z (ec i))
  let h : ∀ i : Fin n, U i.castSucc ⟶ Z i.succ := fun i ↦
    eqToHom (congrArg R.U (ea i)) ≫ R.h (rungIndex i) ≫
      eqToHom (congrArg R.Z (ec i))
  have comm : ∀ i : Fin n,
      b i.castSucc ≫ f i = g i ≫ b i.succ := by
    intro i
    exact transported_right_rung_comm R.Y R.Z R.b
      (ea i) (ec i) (R.f (rungIndex i)) (R.g (rungIndex i))
      (R.comm (rungIndex i))
  have hzero : ∀ i : Fin n, h i ≫ b i.succ = 0 := by
    intro i
    exact transported_right_rung_hzero R.Y R.Z R.U R.b
      (ea i) (ec i) (R.h (rungIndex i)) (R.hzero (rungIndex i))
  refine
    { Z := Z
      Y := Y
      U := U
      b := b
      f := f
      g := g
      h := h
      comm := comm
      hzero := hzero
      meshIso := ?_ }
  intro i
  have hMesh : Nonempty
      (T.rightMesh (R.Y (rungIndex i)) ≅
        RightLadder.stepComplex
          (R.b (rungIndex i)) (R.b (rungIndex i + 1))
          (R.f (rungIndex i)) (R.g (rungIndex i))
          (R.h (rungIndex i)) (R.comm (rungIndex i))
          (R.hzero (rungIndex i))) := by
    simpa only using R.meshIso (rungIndex i)
  let eMesh := Classical.choice hMesh
  let sourceTransport :
      T.rightMesh (Y i.succ) ≅ T.rightMesh (R.Y (rungIndex i)) :=
    eqToIso (congrArg T.rightMesh (congrArg R.Y (ec i).symm))
  let stepTransport := transported_right_step_iso R.Y R.Z R.U R.b
    (ea i) (ec i) (R.f (rungIndex i)) (R.g (rungIndex i))
    (R.h (rungIndex i)) (R.comm (rungIndex i))
    (R.hzero (rungIndex i))
  exact ⟨sourceTransport ≪≫ eMesh ≪≫ stepTransport⟩

/-- The displayed rung of the reversed prefix is the corresponding genuine
right-ladder rung, transported across the two `Fin.rev` index equalities. -/
def ReversedRightPrefix.ofInfiniteSpecialRightLadder_stepIso
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    (n : ℕ) (i : Fin n) :
    RightLadder.stepComplex
        (R.b i.rev.val) (R.b (i.rev.val + 1))
        (R.f i.rev.val) (R.g i.rev.val) (R.h i.rev.val)
        (R.comm i.rev.val) (R.hzero i.rev.val) ≅
      RightLadder.stepComplex
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).b i.succ)
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).b i.castSucc)
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).f i)
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).g i)
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).h i)
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).comm i)
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).hzero i) := by
  let ea : i.castSucc.rev.val = i.rev.val + 1 :=
    congrArg Fin.val (Fin.rev_castSucc i)
  let ec : i.rev.val = i.succ.rev.val :=
    congrArg Fin.val (Fin.rev_succ i).symm
  simpa only [ReversedRightPrefix.ofInfiniteSpecialRightLadder] using
    transported_right_step_iso R.Y R.Z R.U R.b ea ec
      (R.f i.rev.val) (R.g i.rev.val) (R.h i.rev.val)
      (R.comm i.rev.val) (R.hzero i.rev.val)

/-- The last padded arrow of a reversed finite window is the initial padded
arrow of the original right ladder. -/
def ReversedRightPrefix.ofInfiniteSpecialRightLadder_paddedArrowIso_last
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    (n : ℕ) :
      Arrow.mk
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
          (Fin.last n)) ≅
      Arrow.mk (biprod.desc (R.b 0) (0 : R.U 0 ⟶ R.Y 0)) := by
  change Arrow.mk
      (biprod.desc (R.b ((Fin.last n).rev.val))
        (0 : R.U ((Fin.last n).rev.val) ⟶ R.Y ((Fin.last n).rev.val))) ≅
    Arrow.mk (biprod.desc (R.b 0) (0 : R.U 0 ⟶ R.Y 0))
  rw [show (Fin.last n).rev.val = 0 by simp]

end MBDVendor.QSE.Iyama.TauSequenceComparison
