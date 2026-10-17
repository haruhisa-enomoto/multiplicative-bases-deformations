import MultiplicativeBasisDeformations.Foundations.SquareFree

/-!
# The mesh category `k(Γ_A)` and standardness

`graded-category.tex:164–173`: for `Q = Γ_A`, choose bases in the
one-dimensional irreducible spaces. The first and second maps of the almost
split sequence ending at a nonprojective `Y` have components `u_a (σ a)` and
`v_a a` modulo `J²`, with `u_a, v_a ≠ 0`; the mesh relation is
`r_Y = ∑_{a : X → Y} c_{Y,a} (σ a) a` with `c_{Y,a} = u_a v_a`
(`eq:scalar-mesh`), and `k(Γ_A) = C(Γ_A, c)`. Definition 1.2
(`def:standardness`): `A` is standard if there is a `k`-linear equivalence
`k(Γ_A) ≃ ind(mod A)` sending each vertex to its labelled module.

Formalization:

* `Γ_A` is the translation quiver `arTranslationQuiver` of
  `ARTranslationQuiver.lean`; by Lemma 2.2 (`SquareFree.lean`) it has at most
  one arrow between ordered vertices.
* An `ArrowBases` value chooses a basis of each `Irr(x, y)`, indexed by the
  arrows `x → y`.
* The almost split sequence ending at a nonprojective `x` is the canonical one
  of the vendored Auslander--Reiten library, with its chosen decomposition of
  the middle term. For an arrow `a : y → x`, the summands isomorphic to `y`
  are the occurrences of `y`; there is exactly one, because their number is
  `dim Irr(y, x) = 1`. The coefficient is
  `c_{x,a} = ∑_{occurrences i of y} u_i v_i`, where `u_i` and `v_i` are the
  coordinates, in the chosen bases, of the classes of the components
  `τx → y` and `y → x` at `i`. It is nonzero because the components are
  irreducible, so their classes in the one-dimensional spaces `Irr` are
  nonzero.
* `k(Γ_A)` is the scalar mesh category `C(Γ_A, c)` of Definition 2.4.

The manuscript shows that a different choice of bases or almost split
sequences changes `k(Γ_A)` only by an object-fixing isomorphism
(`graded-category.tex:175–190`); Definition 1.2 is formalized with an
existential choice of bases.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

namespace IndSkeleton

variable (S : IndSkeleton k A)

/-- An irreducible morphism between labelled indecomposables of `mod A` is a
radical morphism. -/
theorem isRadicalMorphism_of_irreducible {x y : Fin S.n} {f : S.fg x ⟶ S.fg y}
    (hf : IsIrreducibleMorphism f) : CategoricalRadical.IsRadicalMorphism f :=
  (S.toVendor.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
    (y := y) f).2 hf.not_isSplitEpi

/-- The class in `Irr(x, y)` of a radical morphism of `mod A` between labelled
indecomposables. -/
def irrClassFG {x y : Fin S.n} (f : S.fg x ⟶ S.fg y)
    (hf : CategoricalRadical.IsRadicalMorphism f) : S.Irr (S.ind x) (S.ind y) :=
  S.irrClass ((S.homEquivFG (S.ind x) (S.ind y)).symm f) (by
    rw [mem_radPow_one_iff, isRadical_iff, map_homEquivFG_symm]
    exact hf)

/-- The class of an irreducible morphism in `Irr` is nonzero. -/
theorem irrClassFG_ne_zero {x y : Fin S.n} {f : S.fg x ⟶ S.fg y}
    (hf : IsIrreducibleMorphism f) :
    S.irrClassFG f (S.isRadicalMorphism_of_irreducible hf) ≠ 0 := by
  intro h0
  have hmem : (S.homEquivFG (S.ind x) (S.ind y)).symm f ∈ S.radPow 2 (S.ind x) (S.ind y) :=
    (Submodule.Quotient.mk_eq_zero
      ((S.radPow 2 (S.ind x) (S.ind y)).comap (S.radPow 1 (S.ind x) (S.ind y)).subtype)).1 h0
  rw [mem_radPow_two_iff, map_homEquivFG_symm] at hmem
  have hmem' : f ∈ S.toVendor.almostSplitSkeleton.radicalSquareHomAddSubgroup x y := by
    rw [← S.toVendor.almostSplitSkeleton.intrinsic_radicalSquare_eq x y]
    exact hmem
  exact ((S.toVendor.almostSplitSkeleton.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare
    f).1 hf).2 hmem'

/-- A choice of basis of every space of irreducible maps, indexed by the
arrows of `Γ_A`. -/
def ArrowBases :=
  ∀ x y : S.ARVertex, Module.Basis (x ⟶ y) k (S.Irr (S.label x) (S.label y))

/-- The vendored nonprojective label of a nonprojective vertex. -/
def vendorNonprojective (x : S.nonprojectiveVertices) :
    S.toVendor.tauData.Nonprojective :=
  S.toVendor.canonicalRightNonzeroEquivNonprojective.symm x

/-- The component `τx → y` of the first map of the almost split sequence ending
at `x`, at an occurrence `i` of `y` in its middle term. -/
def sourceComponent (x : S.nonprojectiveVertices) {y : Fin S.n}
    (i : S.toVendor.Occurrence y (S.index x.1)) :
    S.fg (S.index (S.arTau x).1) ⟶ S.fg y :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent S.toVendor.tauData
      (S.vendorNonprojective x) i.1 ≫
    eqToHom (congrArg S.toVendor.fgObj i.2)

theorem sourceComponent_isIrreducible (x : S.nonprojectiveVertices) {y : Fin S.n}
    (i : S.toVendor.Occurrence y (S.index x.1)) :
    IsIrreducibleMorphism (S.sourceComponent x i) := by
  obtain ⟨i, rfl⟩ := i
  simpa [sourceComponent] using
    MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent_isIrreducible
      S.toVendor.tauData (S.vendorNonprojective x) i

/-- The scalar `u_i v_i` contributed by one occurrence. -/
def occurrenceCoefficient (b : S.ArrowBases) (x : S.nonprojectiveVertices)
    (y : S.ARVertex) (a : y ⟶ x.1) (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) : k :=
  (b (S.arTau x).1 y).repr
      (S.irrClassFG (S.sourceComponent x i)
        (S.isRadicalMorphism_of_irreducible (S.sourceComponent_isIrreducible x i)))
      (S.arTranslationQuiver.mate x y a) *
    (b y x.1).repr
      (S.irrClassFG (S.toVendor.occurrenceMap i)
        (S.isRadicalMorphism_of_irreducible (S.toVendor.occurrenceMap_isIrreducible i)))
      a

/-- The mesh coefficient `c_{x,a} = ∑_i u_i v_i` (`eq:scalar-mesh`). -/
def arCoefficient (b : S.ArrowBases) (x : S.nonprojectiveVertices) (y : S.ARVertex)
    (a : y ⟶ x.1) : k :=
  ∑ i : S.toVendor.Occurrence (S.index y) (S.index x.1), S.occurrenceCoefficient b x y a i

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- A vector of a space with a basis indexed by a subsingleton type has a
nonzero coordinate if it is nonzero. -/
theorem basis_repr_ne_zero {ι V : Type*} [AddCommGroup V] [Module k V] [Subsingleton ι]
    (b : Module.Basis ι k V) {v : V} (hv : v ≠ 0) (j : ι) : b.repr v j ≠ 0 := by
  intro h
  apply hv
  apply b.repr.injective
  ext j'
  rw [Subsingleton.elim j' j, h, map_zero, Finsupp.zero_apply]

theorem arCoefficient_ne_zero (b : S.ArrowBases) (x : S.nonprojectiveVertices)
    (y : S.ARVertex) (a : y ⟶ x.1) : S.arCoefficient b x y a ≠ 0 := by
  classical
  have hone : Module.finrank k (S.Irr (S.ind (S.index y)) (S.ind (S.index x.1))) = 1 := by
    have hpos : 0 < Module.finrank k (S.Irr (S.ind (S.index y)) (S.ind (S.index x.1))) :=
      lt_of_le_of_lt (Nat.zero_le _) a.2
    have hle := S.finrank_irr_le_one (S.index y) (S.index x.1)
    omega
  have hcard : Fintype.card (S.toVendor.Occurrence (S.index y) (S.index x.1)) = 1 := by
    rw [← S.toVendor.arrowMultiplicity_eq_card_occurrence, ← hone,
      S.finrank_irr_eq_arrowMultiplicity]
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have hsum : S.arCoefficient b x y a = S.occurrenceCoefficient b x y a i₀ := by
    unfold arCoefficient
    rw [Fintype.sum_eq_single i₀ (fun i hi ↦ absurd (hi₀ i) hi)]
  rw [hsum]
  haveI : Subsingleton ((S.arTau x).1 ⟶ y) := S.hasAtMostOneArrow _ _
  haveI : Subsingleton (y ⟶ x.1) := S.hasAtMostOneArrow _ _
  exact mul_ne_zero
    (basis_repr_ne_zero _ (S.irrClassFG_ne_zero (S.sourceComponent_isIrreducible x i₀)) _)
    (basis_repr_ne_zero _ (S.irrClassFG_ne_zero (S.toVendor.occurrenceMap_isIrreducible i₀)) _)

/-- The coefficient system of `Γ_A` defined by the arrow bases and the almost
split sequences (`eq:scalar-mesh`). -/
def arCoefficients (b : S.ArrowBases) : MeshCoefficients k S.arTranslationQuiver :=
  fun x y a ↦ Units.mk0 (S.arCoefficient b x y a) (S.arCoefficient_ne_zero b x y a)

/-- The mesh category `k(Γ_A) = C(Γ_A, c)` for the coefficients defined by the
arrow bases and the almost split sequences. -/
abbrev ARMeshCategory (b : S.ArrowBases) :=
  ScalarMeshCategory k S.arTranslationQuiver (S.arCoefficients b)

/-- A vertex of `Γ_A`, as an object of `k(Γ_A)`. -/
abbrev meshObj (b : S.ArrowBases) (x : S.ARVertex) : S.ARMeshCategory b :=
  ScalarMeshCategory.obj (S.arCoefficients b) x

end IndSkeleton

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- A functor between `k`-linear categories is `k`-linear on morphisms. -/
def IsLinearFunctor {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Linear k C] [Linear k D] (F : C ⥤ D) : Prop :=
  ∀ (X Y : C) (c : k) (f g : X ⟶ Y), F.map (c • f + g) = c • F.map f + F.map g

namespace IndSkeleton

variable (S : IndSkeleton k A)

/-- Definition 1.2 for a chosen skeleton: for some choice of arrow bases there
is a `k`-linear equivalence `k(Γ_A) ≃ ind(mod A)` sending each vertex to its
labelled module. -/
def IsStandard : Prop :=
  ∃ (b : S.ArrowBases) (F : S.ARMeshCategory b ⥤ S.Ind),
    F.IsEquivalence ∧ IsLinearFunctor (k := k) F ∧
      ∀ x : S.ARVertex, Nonempty (F.obj (S.meshObj b x) ≅ S.label x)

end IndSkeleton

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u'

variable (k A : Type u') [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Definition 1.2 (`def:standardness`): `A` is standard, for every choice of
representatives of the indecomposable modules. -/
def IsStandard : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  ∀ S : IndSkeleton k A, S.IsStandard

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- Morphisms of `ind(mod A)`, as `k`-linear maps of the underlying spaces. -/
def homToLinearMap (X Y : S.Ind) : (X ⟶ Y) →ₗ[k] (S.obj X →ₗ[k] S.obj Y) where
  toFun f := f.hom.hom.restrictScalars k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homToLinearMap_injective (X Y : S.Ind) :
    Function.Injective (S.homToLinearMap X Y) := by
  intro f g h
  ext v
  exact LinearMap.congr_fun h v

instance finiteDimensional_hom (X Y : S.Ind) : FiniteDimensional k (X ⟶ Y) := by
  haveI : Module.Finite k (S.obj X) := (S.isFiniteIndecomposable X).1
  haveI : Module.Finite k (S.obj Y) := (S.isFiniteIndecomposable Y).1
  exact Module.Finite.of_injective _ (S.homToLinearMap_injective X Y)

instance finiteDimensional_layer (d : ℕ) (X Y : S.Ind) :
    FiniteDimensional k (S.layer d X Y) :=
  inferInstance

/-- Arrow bases exist, so the definition of standardness is not vacuous. -/
theorem nonempty_arrowBases : Nonempty S.ArrowBases :=
  ⟨fun _ _ ↦ Module.finBasisOfFinrankEq k _ rfl⟩

end MultiplicativeBasisDeformations.IndSkeleton
