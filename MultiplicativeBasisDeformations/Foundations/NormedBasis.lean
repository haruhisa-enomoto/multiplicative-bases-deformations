import Mathlib

/-!
# Normed multiplicative bases and basic algebras

Definition 1.1 of the frozen manuscript (`main.tex:135`): a basis `𝓑` of a
finite-dimensional algebra `A` is *multiplicative* if `bc ∈ 𝓑 ∪ {0}` for all
`b, c ∈ 𝓑`; it is *normed* if it contains a complete set of primitive
orthogonal idempotents and `𝓑 ∩ (rad A)^n` is a basis of `(rad A)^n` for every
`n ≥ 1`.

The algebra radical `rad A` is Mathlib's Jacobson radical `Ring.jacobson A`
(the intersection of the maximal left ideals), regarded as a `k`-subspace.
Its powers are products of `k`-subspaces, which agree with the ideal powers
because `rad A` is a two-sided ideal.
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

universe u v

variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]

/-- The algebra radical `rad A`, as a `k`-subspace of `A`. -/
def algebraRadical : Submodule k A :=
  (Ring.jacobson A).restrictScalars k

/-- The radical power `(rad A)^n`, as a `k`-subspace of `A`. -/
def algebraRadicalPow (n : ℕ) : Submodule k A :=
  algebraRadical k A ^ n

variable {A}

/-- A primitive idempotent: a nonzero idempotent `e` such that the only
idempotents of the corner `eAe` are `0` and `e`. -/
def IsPrimitiveIdempotent (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ f : A, IsIdempotentElem f → e * f = f → f * e = f → f = 0 ∨ f = e

variable {k}

/-- A basis is *multiplicative* if the product of two basis elements is zero
or a basis element. -/
def IsMultiplicativeBasis {ι : Type*} (b : Module.Basis ι k A) : Prop :=
  ∀ i j, b i * b j = 0 ∨ ∃ l, b i * b j = b l

/-- Definition 1.1 (`def:normed-multiplicative-basis`). A *normed
multiplicative basis*: multiplicative, containing a complete set of primitive
orthogonal idempotents, and meeting every radical power `(rad A)^n`, `n ≥ 1`,
in a basis of that power. -/
structure IsNormedMultiplicativeBasis {ι : Type*} (b : Module.Basis ι k A) :
    Prop where
  multiplicative : IsMultiplicativeBasis b
  idempotents :
    ∃ E : Finset ι,
      CompleteOrthogonalIdempotents (fun i : E => b i) ∧
        ∀ i ∈ E, IsPrimitiveIdempotent (b i)
  radicalPow :
    ∀ n : ℕ, 1 ≤ n →
      Submodule.span k (b '' {i | b i ∈ algebraRadicalPow k A n}) =
        algebraRadicalPow k A n

variable (k A)

/-- `A` has a normed multiplicative basis. -/
def HasNormedMultiplicativeBasis : Prop :=
  ∃ (ι : Type v) (b : Module.Basis ι k A), IsNormedMultiplicativeBasis b

/-- `A` is *basic*: it has a complete set of primitive orthogonal idempotents
whose principal right ideals `e_i A` are pairwise nonisomorphic. Here
`e_i A ≅ e_j A` is expressed by elements `x ∈ e_i A e_j`, `y ∈ e_j A e_i` with
`xy = e_i` and `yx = e_j`. -/
def IsBasicAlgebra : Prop :=
  ∃ (n : ℕ) (e : Fin n → A),
    CompleteOrthogonalIdempotents e ∧ (∀ i, IsPrimitiveIdempotent (e i)) ∧
      ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧
        x * y = e i ∧ y * x = e j) → i = j

end MultiplicativeBasisDeformations
