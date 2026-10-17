import MultiplicativeBasisDeformations.Foundations.ObjectValues
import MultiplicativeBasisDeformations.Foundations.ScalSplit

/-!
# Lemma 4.12, last clause: `Scal(L)` is an abelian divisible group

`lem:cover-exhaustion` (`scalar-normalization.tex:517–560`): "Consequently `L` has a
multiplicative basis, and `Scal(L)` is an abelian divisible group."

`Scal(L)` is the group of multiplicative `k*`-valued weights on the nonzero morphism lines of `L`
(`Thin.ScalGroup.Scal` on all objects of the graded covering category). It is a subgroup of a
commutative group, hence abelian. For divisibility we use Lemma 4.13 (`weight_eq_ratio`): every
weight is a ratio of object values `ζ_y / ζ_x`; `n`-th roots of the object values (`k` is
algebraically closed) give an `n`-th root of the weight. The source instead identifies `Scal(L)`
with the inverse limit along the exhaustion, split at each step by Lemma 4.11(2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData Thin.ScalGroup

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {v₀ : V} [IsAlgClosed k] [Infinite k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

variable (Q c v₀ D) in
/-- The category `L` of lifted projective vertices. -/
abbrev LCat := CovObj (grading0 D (deckGrading Q c v₀))

open Classical in
/-- An element of `Scal(L)` as a function of pairs of objects (one off the nonzero lines). -/
def scalFun (d : Scal k (Set.univ : Set (LCat Q c v₀ D))) : LCat Q c v₀ D → LCat Q c v₀ D → k :=
  fun o o' ↦ if h : ∃ f : o ⟶ o', f ≠ 0 then
    ((d : NzLine (Set.univ : Set (LCat Q c v₀ D)) → kˣ) ⟨o, o', trivial, trivial, h⟩ : k) else 1

theorem scalFun_isWeight (d : Scal k (Set.univ : Set (LCat Q c v₀ D))) :
    Thin.IsWeight (Set.univ : Set (LCat Q c v₀ D)) (scalFun d) := by
  refine ⟨fun o _ o' _ f hf ↦ ?_, fun o _ o' _ o'' _ f g hfg ↦ ?_⟩
  · unfold scalFun; rw [dif_pos ⟨f, hf⟩]; exact Units.ne_zero _
  · unfold scalFun
    rw [dif_pos ⟨_, hfg⟩, dif_pos ⟨f, left_ne hfg⟩, dif_pos ⟨g, right_ne hfg⟩, ← Units.val_mul]
    exact congrArg Units.val (scal_mul d trivial trivial trivial f g hfg)

variable (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

include hF in
/-- **`Scal(L)` is an abelian divisible group** (Lemma 4.12, last clause). -/
theorem scal_abelian_divisible :
    (∀ a b : Scal k (Set.univ : Set (LCat Q c v₀ D)), a * b = b * a) ∧
      ∀ (d : Scal k (Set.univ : Set (LCat Q c v₀ D))) (n : ℕ), 0 < n → ∃ e, e ^ n = d := by
  refine ⟨fun a b ↦ mul_comm a b, fun d n hn ↦ ?_⟩
  obtain ⟨ζ, hζ0, hζ⟩ := weight_eq_ratio (Q := Q) (c := c) (v₀ := v₀) hF (scalFun_isWeight d)
  choose η hη using fun z : LCat Q c v₀ D ↦ IsAlgClosed.exists_pow_nat_eq (ζ z) hn
  have hη0 : ∀ z : LCat Q c v₀ D, η z ≠ 0 := fun z h ↦ hζ0 z (by rw [← hη z, h, zero_pow hn.ne'])
  let e : Scal k (Set.univ : Set (LCat Q c v₀ D)) :=
    ⟨fun ℓ ↦ Units.mk0 (η ℓ.o' / η ℓ.o) (div_ne_zero (hη0 _) (hη0 _)), by
      intro o o' o'' _ _ _ f g hfg
      ext
      simp only [mkLine, Units.val_mul, Units.val_mk0]
      field_simp
      rw [mul_div_mul_right _ _ (hη0 _)]⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  funext ℓ
  rw [Subgroup.coe_pow, Pi.pow_apply]
  apply Units.ext
  obtain ⟨o, o', -, -, hnz⟩ := ℓ
  obtain ⟨f, hf⟩ := hnz
  have h1 : scalFun d o o' = ζ o' / ζ o :=
    hζ o o' f.1 f.2 (fun h0 ↦ hf (Subtype.ext h0))
  unfold scalFun at h1
  rw [dif_pos ⟨f, hf⟩] at h1
  rw [Units.val_pow_eq_pow_val]
  simp only [e, Units.val_mk0]
  rw [div_pow, hη, hη, ← h1]

end MeshWalk

end MultiplicativeBasisDeformations
