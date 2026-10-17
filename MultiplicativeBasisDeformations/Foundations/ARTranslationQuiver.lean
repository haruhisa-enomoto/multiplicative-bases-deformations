import MultiplicativeBasisDeformations.Foundations.ARBridge
import MultiplicativeBasisDeformations.Foundations.MeshCategory

/-!
# The Auslander--Reiten quiver as a translation quiver

`graded-category.tex:84–96`: the vertices of `Γ_A` are the indecomposable
modules, and the arrows `X → Y` form a basis of `Irr(X, Y) = J(X, Y)/J²(X, Y)`.
The translation `τ` sends a nonprojective indecomposable `Y` to the starting
term of the almost split sequence ending at `Y`; it is a bijection from the
nonprojective onto the noninjective vertices. The mates of the arrows ending
at a nonprojective `Y` are the arrows starting at `τY`, indexed by the same
summands of the middle term.

Formally the arrows `X → Y` are `Fin (dim Irr(X, Y))`; the mate bijection
`(y ⟶ x) ≃ (τx ⟶ y)` is the identification of these index sets, which have
the same size because both dimensions equal the multiplicity of `y` in the
middle term of the almost split sequence ending at `x`. The projective and
injective vertices are those whose module is projective, respectively
injective, in `mod A`. The translation and the dimension identities come from
the vendored Auslander--Reiten theory through `ARBridge.lean`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

namespace IndSkeleton

variable (S : IndSkeleton k A)

/-- The vertices of the Auslander--Reiten quiver `Γ_A`. -/
def ARVertex : Type := Fin S.n

/-- The Auslander--Reiten quiver: the arrows `x → y` are indexed by
`Fin (dim Irr(x, y))`. -/
instance arQuiver : Quiver S.ARVertex where
  Hom x y := Fin (Module.finrank k (S.Irr (S.ind x) (S.ind y)))

instance (x y : S.ARVertex) : Fintype (x ⟶ y) :=
  inferInstanceAs (Fintype (Fin _))

instance (x y : S.ARVertex) : DecidableEq (x ⟶ y) :=
  inferInstanceAs (DecidableEq (Fin _))

instance : Fintype S.ARVertex := inferInstanceAs (Fintype (Fin S.n))

instance : DecidableEq S.ARVertex := inferInstanceAs (DecidableEq (Fin S.n))

/-- A vertex of `Γ_A` from an index. -/
def vertex (x : Fin S.n) : S.ARVertex := x

/-- The labelled module of a vertex, as an object of `ind(mod A)`. -/
def label (x : S.ARVertex) : S.Ind := S.ind x

/-- The index of a vertex. -/
def index (x : S.ARVertex) : Fin S.n := x

section AR

variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The arrow multiplicity of the vendored library: the multiplicity of `x`
in the middle term of the chosen minimal right almost split map ending at
`y`. -/
abbrev arrowMultiplicity (x y : Fin S.n) : ℕ :=
  MBDVendor.Magnitude.FiniteTauMatrix.arrowMultiplicity
    S.toVendor.finiteTauCategoryData.toFiniteRightTauCategoryData x y

/-- Over an algebraically closed field, `dim Irr(x, y)` is the multiplicity of
`x` in the middle term of the minimal right almost split map ending at `y`. -/
theorem finrank_irr_eq_arrowMultiplicity [IsAlgClosed k] (x y : Fin S.n) :
    Module.finrank k (S.Irr (S.ind x) (S.ind y)) = S.arrowMultiplicity x y :=
  (S.finrank_irr_eq_vendor (S.ind x) (S.ind y)).trans
    (S.toVendor.intrinsicIrreducible_finrank_eq_arrowMultiplicity x y)

/-- The nonprojective vertices of `Γ_A`. -/
def nonprojectiveVertices : Set S.ARVertex := {x | ¬ Projective (S.fg (S.index x))}

/-- The noninjective vertices of `Γ_A`. -/
def noninjectiveVertices : Set S.ARVertex := {x | ¬ Injective (S.fg (S.index x))}

/-- The Auslander--Reiten translation, a bijection from the nonprojective
onto the noninjective vertices. -/
def arTau : S.nonprojectiveVertices ≃ S.noninjectiveVertices :=
  S.toVendor.rightTranslationEquiv

/-- The two sides of a mesh have the same arrow count:
`dim Irr(y, x) = dim Irr(τ x, y)` for a nonprojective `x`. -/
theorem finrank_irr_mate [IsAlgClosed k] (x : S.nonprojectiveVertices) (y : S.ARVertex) :
    Module.finrank k (S.Irr (S.ind (S.index y)) (S.ind (S.index x.1))) =
      Module.finrank k
        (S.Irr (S.ind (S.index (S.arTau x).1)) (S.ind (S.index y))) := by
  rw [S.finrank_irr_eq_arrowMultiplicity, S.finrank_irr_eq_arrowMultiplicity]
  have h := S.toVendor.arrowMultiplicity_eq_inverseTranslation (S.arTau x) (S.index y)
  have hx : (S.toVendor.rightTranslationEquiv.symm (S.arTau x)).1 = S.index x.1 := by
    exact congrArg Subtype.val (S.toVendor.rightTranslationEquiv.symm_apply_apply x)
  rw [hx] at h
  exact h.symm

/-- `Γ_A` as a translation quiver (Definition 2.3). -/
abbrev arTranslationQuiver [IsAlgClosed k] : TranslationQuiver S.ARVertex where
  nonprojective := S.nonprojectiveVertices
  noninjective := S.noninjectiveVertices
  tau := S.arTau
  mate x y := finCongr (S.finrank_irr_mate x y)

end AR

end IndSkeleton

end MultiplicativeBasisDeformations
