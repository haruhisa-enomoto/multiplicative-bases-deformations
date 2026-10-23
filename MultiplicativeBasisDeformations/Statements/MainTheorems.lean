module

public import MultiplicativeBasisDeformations.Foundations.ARQuiver
public import MultiplicativeBasisDeformations.Foundations.Rays
public import MultiplicativeBasisDeformations.Foundations.ARBrick
public import MultiplicativeBasisDeformations.Foundations.FilteredNormalForm
public import MultiplicativeBasisDeformations.Statements.PartOne
public import MultiplicativeBasisDeformations.Foundations.StandardForm
public import MultiplicativeBasisDeformations.Foundations.SkeletonExists
public import MultiplicativeBasisDeformations.Foundations.BasicCorner
public import MultiplicativeBasisDeformations.Foundations.RayStandard
public import MultiplicativeBasisDeformations.Foundations.FinalBasis
public import MultiplicativeBasisDeformations.Foundations.StandardRay

/-!
# Main theorems (statements)

Theorems A and B of the introduction (`main.tex`), Theorem 11.7
(`thm:final-basis`), Corollary 5.5 (`cor:away-from-two-basis`), and
Theorem 11.8(2) (`thm:final-standardness`).

Throughout, `k` is algebraically closed and `A` is a finite-dimensional
`k`-algebra, in the same universe (the vendored Auslander--Reiten library
works in one universe). "Characteristic different from two" is `ringChar k ≠ 2`.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]
  (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Theorem B** (`main.tex`; Corollary 5.5, `cor:away-from-two-basis`).
Every basic finite-dimensional representation-finite algebra over an
algebraically closed field of characteristic different from two is
standard. -/
theorem theoremB (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A)
    (hchar : ringChar k ≠ 2) :
    IsStandard k A := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  intro S
  classical
  obtain ⟨b⟩ := S.nonempty_arrowBases
  -- Proposition 5.4: surjective mesh derivatives give the filtered normal form
  refine S.isStandard_of_derivativesSurjective b fun m hm ↦ ?_
  -- Proposition 5.3, with the brick hypothesis from Lemma 5.2 and Proposition 2.10
  exact meshCorrectionSpaces S.arTranslationQuiver S.hasAtMostOneArrow (S.arCoefficients b)
    (fun x y ↦ S.finiteDimensional_meshHom b x y) hchar (S.brickHypothesis b) m hm

/-- **Corollary 5.5(2)** (`cor:away-from-two-basis`), existence part: a basic
representation-finite algebra over an algebraically closed field of
characteristic different from two has a normed multiplicative basis. The
standard equivalence of Theorem B identifies `A` with `A₀` (restricting to the
projective labels), and `A₀` has a normed multiplicative basis by
Proposition 4.14 and Corollary 3.3. -/
theorem basic_hasNormedBasis (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A)
    (hchar : ringChar k ≠ 2) : HasNormedMultiplicativeBasis k A := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  obtain ⟨S⟩ := exists_indSkeleton hA
  have hstd := theoremB k A hbasic hA hchar S
  obtain ⟨n, e, he, hprim, hb⟩ := hbasic
  exact S.hasNormedBasis_of_isStandard he hprim hb hstd

/-- **Theorem A away from characteristic two** (`main.tex`; Theorem 11.7(1)
for `char k ≠ 2`, via Corollary 5.5(2) and Lemma 2.1): the basic algebra `eAe`
is a representation-finite full corner, it has a normed multiplicative basis,
and Lemma 2.1 lifts it to `A`. -/
theorem theoremA_of_ringChar_ne_two (hA : IsRepresentationFinite k A) (hchar : ringChar k ≠ 2) :
    HasNormedMultiplicativeBasis k A := by
  obtain ⟨e, he, hfull, hbasic⟩ := exists_basic_full_corner k A
  haveI : FiniteDimensional k he.Corner := corner_finite he
  exact nonbasicBasis he hfull hbasic
    (basic_hasNormedBasis k he.Corner hbasic (corner_isRepresentationFinite hA he) hchar)

/-- **Theorem A** (`main.tex`; Theorem 11.7(1), `thm:final-basis`). Every
finite-dimensional representation-finite algebra over an algebraically closed
field has a normed multiplicative basis. Outside characteristic two this is
`theoremA_of_ringChar_ne_two`; in characteristic two the basic corner has one by
Proposition 8.3 with Corollary 10.5 (`basic_hasNormedBasis_char2`), and Lemma 2.1
lifts it to `A`. -/
theorem theoremA (hA : IsRepresentationFinite k A) :
    HasNormedMultiplicativeBasis k A := by
  by_cases hchar : ringChar k = 2
  · haveI : CharP k 2 := ringChar.of_eq hchar
    obtain ⟨e, he, hfull, hbasic⟩ := exists_basic_full_corner k A
    haveI : FiniteDimensional k he.Corner := corner_finite he
    exact nonbasicBasis he hfull hbasic
      (basic_hasNormedBasis_char2 k he.Corner hbasic (corner_isRepresentationFinite hA he))
  · exact theoremA_of_ringChar_ne_two k A hA hchar

/-- Corollary 5.5 (`cor:away-from-two-basis`). Let `A` be basic and
representation-finite, and `char k ≠ 2`. (1) `A ≅ k ray A`, and `A` is
standard. (2) The ray basis is a normed multiplicative basis of `A`, with one
representative of every nonzero ray. -/
theorem awayFromTwoBasis (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (hchar : ringChar k ≠ 2)
    (F : PrimitiveIdempotents A) :
    IsStandard k A ∧
      ∃ b : Module.Basis (F.NonzeroRay k) k A,
        IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b ∧
          F.KillsZeroRayProducts b := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  have hstd := theoremB k A hbasic hA hchar
  obtain ⟨S⟩ := exists_indSkeleton hA
  exact ⟨hstd, S.hasRayBasis_of_isStandard hbasic (hstd S) F⟩

/-- Theorem 11.7(2) (`thm:final-basis`). For a basic algebra, the normed
multiplicative basis can be chosen with one representative of every nonzero
ray, the primitive idempotents representing the identity rays. -/
theorem finalBasis_ray (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A)
    (F : PrimitiveIdempotents A) :
    ∃ b : Module.Basis (F.NonzeroRay k) k A,
      IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b := by
  by_cases hchar : ringChar k = 2
  · haveI : CharP k 2 := ringChar.of_eq hchar
    exact finalBasis_ray_char2 k A hbasic hA F
  · obtain ⟨b, hb, htr, -⟩ := (awayFromTwoBasis k A hbasic hA hchar F).2
    exact ⟨b, hb, htr⟩

/-- Theorem 11.7(3) (`thm:final-basis`). For a basic algebra and
characteristic different from two, these representatives induce an
isomorphism `k ray A ≅ A`. -/
theorem finalBasis_rayLinearization (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (hchar : ringChar k ≠ 2)
    (F : PrimitiveIdempotents A) :
    ∃ b : Module.Basis (F.NonzeroRay k) k A,
      IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b ∧
        F.KillsZeroRayProducts b :=
  (awayFromTwoBasis k A hbasic hA hchar F).2

/-- Theorem 11.8(2) (`thm:final-standardness`). In every characteristic, a
basic representation-finite algebra is standard if and only if
`A ≅ k ray A`, expressed by a multiplicative ray transversal that kills zero
ray products. -/
theorem standard_iff_rayLinearization (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (F : PrimitiveIdempotents A) :
    IsStandard k A ↔
      ∃ b : Module.Basis (F.NonzeroRay k) k A,
        IsMultiplicativeBasis b ∧ F.IsRayTransversal b ∧
          F.KillsZeroRayProducts b := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  constructor
  · intro hstd
    obtain ⟨S⟩ := exists_indSkeleton hA
    obtain ⟨b, hb, htr, hkill⟩ := S.hasRayBasis_of_isStandard hbasic (hstd S) F
    exact ⟨b, hb.multiplicative, htr, hkill⟩
  · rintro ⟨b, hm, ht, hz⟩ S
    by_cases hchar : ringChar k = 2
    · haveI : CharP k 2 := ringChar.of_eq hchar
      obtain ⟨b'⟩ := S.nonempty_arrowBases
      rcases subsingleton_or_nontrivial A with hs | hn
      · exact S.isStandard_of_subsingleton
      · obtain ⟨ψ⟩ := S.algEquivA0_of_rayBasis b' hbasic hA hn F hm ht hz
        exact S.isStandard_of_algEquiv b' ψ
    · exact theoremB k A hbasic hA hchar S

end MultiplicativeBasisDeformations
