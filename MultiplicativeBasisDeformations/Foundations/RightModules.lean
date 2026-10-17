import MultiplicativeBasisDeformations.Foundations.NormedBasis

/-!
# Right modules, representation-finite algebras, and the radical of `ind(mod A)`

Conventions of the manuscript (`main.tex`): modules are
finite-dimensional right modules, and maps compose from left to right, so the
manuscript's `fg` is Lean's `f ≫ g`.

* Right `A`-modules are modelled as `ModuleCat Aᵐᵒᵖ`.
* `IsRepresentationFinite k A`: finitely many isomorphism classes of
  finite-dimensional indecomposable right modules. Borrowed from
  the magnitude-conjecture formalization,
  `MagnitudeConjecture/Algebra/RightModuleFiniteType.lean` (commit
  `3ac9f6a22`).
* `IndSkeleton k A`: one representative of each isomorphism class of
  finite-dimensional indecomposable right modules, indexed by `Fin n`; the
  full subcategory on them is `ind(mod A)`.
* The categorical radical `J` of `ind(mod A)` and its powers: `J(X, Y)` is
  spanned by the radical morphisms `f` (those with `1 - f g` invertible for all
  `g : Y ⟶ X`), and `J^{n+1}(X, Y)` is spanned by composites `f g` with `f`
  radical and `g ∈ J^n`, all intermediate objects being indecomposable
  (`graded-category.tex`).
* `Irr(X, Y) = J(X, Y) / J²(X, Y)`.
* Almost split sequences.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]

/-- Right `A`-modules: left modules over `Aᵐᵒᵖ`. -/
abbrev RightModuleCat := ModuleCat.{v} Aᵐᵒᵖ

/-- A finite-dimensional indecomposable right `A`-module. -/
def IsFiniteIndecomposable (M : RightModuleCat A) : Prop :=
  Module.Finite k M ∧ Indecomposable M

/-- `A` is representation-finite: there are finitely many isomorphism classes
of finite-dimensional indecomposable right `A`-modules. -/
def IsRepresentationFinite : Prop :=
  ∃ n : ℕ, ∃ X : Fin n → RightModuleCat A,
    (∀ i, IsFiniteIndecomposable k A (X i)) ∧
      ∀ M : RightModuleCat A, IsFiniteIndecomposable k A M →
        ∃ i, Nonempty (M ≅ X i)

/-- A complete irredundant list of finite-dimensional indecomposable right
`A`-modules. -/
structure IndSkeleton where
  /-- The number of isomorphism classes. -/
  n : ℕ
  /-- The chosen representatives. -/
  obj : Fin n → RightModuleCat A
  isFiniteIndecomposable : ∀ i, IsFiniteIndecomposable k A (obj i)
  pairwise : ∀ i j, Nonempty (obj i ≅ obj j) → i = j
  complete : ∀ M : RightModuleCat A, IsFiniteIndecomposable k A M →
    ∃ i, Nonempty (M ≅ obj i)

variable {k A}

namespace IndSkeleton

variable (S : IndSkeleton k A)

/-- `ind(mod A)`: the full subcategory on the chosen representatives. -/
abbrev Ind := InducedCategory (RightModuleCat A) S.obj

/-- The object of `ind(mod A)` with a given index. -/
def ind (x : Fin S.n) : S.Ind := x

/-- The inclusion of `ind(mod A)` into right modules. -/
abbrev incl : S.Ind ⥤ RightModuleCat A := inducedFunctor S.obj

/-- A radical morphism of `ind(mod A)`: `1 - f ≫ g` is invertible for every
`g` in the opposite direction. -/
def IsRadical {X Y : S.Ind} (f : X ⟶ Y) : Prop :=
  ∀ g : Y ⟶ X, IsIso (𝟙 X - f ≫ g)

/-- The radical powers `J^n(X, Y)` of `ind(mod A)`. -/
def radPow : ℕ → ∀ X Y : S.Ind, Submodule k (X ⟶ Y)
  | 0, _, _ => ⊤
  | n + 1, X, Y =>
      Submodule.span k
        {h | ∃ (Z : S.Ind) (f : X ⟶ Z) (g : Z ⟶ Y),
          S.IsRadical f ∧ g ∈ radPow n Z Y ∧ h = f ≫ g}

/-- The radical layer `J^d(X, Y) / J^{d+1}(X, Y)`, the degree-`d` part of the
radical grading `gr_J ind(mod A)`. -/
abbrev layer (d : ℕ) (X Y : S.Ind) :=
  ↥(S.radPow d X Y) ⧸ (S.radPow (d + 1) X Y).comap (S.radPow d X Y).subtype

/-- The class in `J^d / J^{d+1}` of a morphism in `J^d`. -/
def layerClass {d : ℕ} {X Y : S.Ind} (f : X ⟶ Y) (hf : f ∈ S.radPow d X Y) :
    S.layer d X Y :=
  Submodule.Quotient.mk ⟨f, hf⟩

/-- The space of irreducible maps `Irr(X, Y) = J(X, Y) / J²(X, Y)`. -/
abbrev Irr (X Y : S.Ind) := S.layer 1 X Y

/-- The class in `Irr(X, Y)` of a morphism in `J(X, Y)`. -/
def irrClass {X Y : S.Ind} (f : X ⟶ Y) (hf : f ∈ S.radPow 1 X Y) : S.Irr X Y :=
  S.layerClass f hf

end IndSkeleton

section AlmostSplit

variable {C : Type*} [Category C]

/-- A right almost split morphism: not a split epimorphism, and every
morphism into its target that is not a split epimorphism factors through it.
The same definition appears in the vendored library as
`MBDVendor.QSE.IsRightAlmostSplit`. -/
structure IsRightAlmostSplit {E Z : C} (f : E ⟶ Z) : Prop where
  not_isSplitEpi : ¬ IsSplitEpi f
  factors : ∀ {X : C} (g : X ⟶ Z), ¬ IsSplitEpi g → ∃ h : X ⟶ E, h ≫ f = g

/-- The dual notion of a left almost split morphism. -/
structure IsLeftAlmostSplit {Z E : C} (f : Z ⟶ E) : Prop where
  not_isSplitMono : ¬ IsSplitMono f
  factors : ∀ {X : C} (g : Z ⟶ X), ¬ IsSplitMono g → ∃ h : E ⟶ X, f ≫ h = g

/-- An almost split sequence `0 → U → E → V → 0`: a short exact sequence whose
first map is left almost split and whose second map is right almost split. -/
structure IsAlmostSplitSequence [Preadditive C] [HasZeroObject C]
    {U E V : C} (f : U ⟶ E) (g : E ⟶ V) : Prop where
  comp_eq_zero : f ≫ g = 0
  shortExact : (ShortComplex.mk f g comp_eq_zero).ShortExact
  left : IsLeftAlmostSplit f
  right : IsRightAlmostSplit g

end AlmostSplit

end MultiplicativeBasisDeformations
