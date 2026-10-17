import Mathlib
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.RingTheory.LocalRing.Basic
import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd

/-!
# Lemma 5.2 in its abstract form

`mesh-deformations.tex` (`lem:deletion-brick`): "Let `𝒟` be a full additive subcategory
of a finite-length `k`-linear abelian category, closed under images and direct summands. Assume
finite-dimensional Hom spaces and Krull–Schmidt decomposition. For any set `Σ` of indecomposable
isomorphism classes, every nonempty quotient `ind 𝒟/[Σ]` has an object whose endomorphism ring
is a division algebra. If all residue division algebras are `k`, the quotient has a brick."

Proof (as in the source): among the objects of `ind 𝒟` outside `Σ`, take one, `X`, minimal
among subobjects of a fixed object (the descending chain condition, `IsArtinianObject`).
A radical endomorphism `f` of `X` is not epi (an epi endomorphism of an object with
finite-dimensional endomorphisms is invertible, `isUnit_of_epi`), so it factors through its
proper image; the indecomposable summands of the image are smaller, lie in `𝒟` by
image-closure, hence in `Σ`. Conversely a map through `Σ` is a radical endomorphism: an
invertible one would make `X` a summand of an indecomposable object of `Σ`
(`not_isUnit_through`). Hence `End(X)/[Σ](X, X) = End(X)/rad`, the residue division algebra
(`deletionBrick`). Indecomposable objects are those with local endomorphism rings
(Krull–Schmidt); closure under summands is not needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations

namespace AbstractBrick

universe u v w

variable {k : Type u} [Field k] {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] [Linear k 𝒜]

/-- Morphisms factoring through a finite family of objects of `Σ` (the ideal `[Σ]`). -/
def Through (Sg : 𝒜 → Prop) {X Y : 𝒜} (f : X ⟶ Y) : Prop :=
  ∃ (n : ℕ) (Z : Fin n → 𝒜) (g : ∀ i, X ⟶ Z i) (h : ∀ i, Z i ⟶ Y),
    (∀ i, Sg (Z i)) ∧ f = ∑ i, g i ≫ h i

/-- An epi endomorphism of an object with finite-dimensional endomorphisms is invertible. -/
theorem isIso_of_epi_end [∀ X Y : 𝒜, FiniteDimensional k (X ⟶ Y)] {X : 𝒜} (f : X ⟶ X)
    [Epi f] : IsIso f := by
  let L : (X ⟶ X) →ₗ[k] (X ⟶ X) :=
    { toFun := fun g ↦ f ≫ g
      map_add' := fun g g' ↦ by simp
      map_smul' := fun t g ↦ by simp }
  have hinj : Function.Injective L := fun g g' h ↦ (cancel_epi f).1 h
  obtain ⟨g, hg⟩ := (LinearMap.injective_iff_surjective.1 hinj) (𝟙 X)
  have : IsSplitMono f := ⟨⟨g, hg⟩⟩
  exact isIso_of_mono_of_epi f

theorem nontrivial_end {X : 𝒜} [IsLocalRing (End X)] : 𝟙 X ≠ 0 := by
  intro h
  have : (1 : End X) = 0 := h
  exact one_ne_zero this

/-- **An isomorphism cannot factor through an indecomposable object not isomorphic to `X`.** -/
theorem not_isIso_comp {X Z : 𝒜} [IsLocalRing (End X)] [hZ : IsLocalRing (End Z)]
    (g : X ⟶ Z) (h : Z ⟶ X) (hnot : ¬ Nonempty (X ≅ Z)) : ¬ IsIso (g ≫ h) := by
  intro hiso
  set u := inv (g ≫ h)
  have e : g ≫ h ≫ u = 𝟙 X := by rw [← Category.assoc]; exact IsIso.hom_inv_id _
  set p : End Z := h ≫ u ≫ g
  have hp : p * p = p := by
    change (h ≫ u ≫ g) ≫ h ≫ u ≫ g = h ≫ u ≫ g
    simp only [Category.assoc, reassoc_of% e]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := p) (b := 1 - p) (by abel) with hp1 | hp1
  · -- `p` is invertible, hence `p = 1`, and `g` is an isomorphism
    have hp1' : p = 1 := by
      obtain ⟨v, hv⟩ := hp1
      have h2 : (v : End Z) * v = v * 1 := by rw [mul_one, hv]; exact hp
      rw [← hv]; exact (Units.mul_right_inj v).1 h2
    apply hnot
    refine ⟨⟨g, h ≫ u, by rw [e], ?_⟩⟩
    have : (h ≫ u ≫ g : Z ⟶ Z) = 𝟙 Z := hp1'
    rw [Category.assoc]; exact this
  · -- `1 - p` is invertible and idempotent, so `p = 0`, and `g ≫ h = 0`
    have hp0 : p = 0 := by
      obtain ⟨v, hv⟩ := hp1
      have hq : (1 - p) * (1 - p) = 1 - p := by
        rw [sub_mul, mul_sub, mul_sub, hp, one_mul, mul_one, one_mul]; abel
      have h2 : (v : End Z) * v = v * 1 := by rw [mul_one, hv]; exact hq
      have h1 : (1 : End Z) - p = 1 := by rw [← hv]; exact (Units.mul_right_inj v).1 h2
      exact sub_eq_self.1 h1
    have h0 : (g ≫ h) ≫ u ≫ (g ≫ h) = g ≫ h := by
      show (g ≫ h) ≫ (inv (g ≫ h) ≫ (g ≫ h)) = g ≫ h
      rw [IsIso.inv_hom_id, Category.comp_id]
    have : g ≫ p ≫ h = 0 := by rw [show (p : Z ⟶ Z) = 0 from hp0, zero_comp, comp_zero]
    rw [show g ≫ p ≫ h = (g ≫ h) ≫ u ≫ (g ≫ h) by simp [p, Category.assoc], h0] at this
    apply nontrivial_end (X := X)
    have h00 : IsIso (0 : X ⟶ X) := this ▸ hiso
    rw [← IsIso.hom_inv_id (0 : X ⟶ X), zero_comp]

/-- **Maps through `Σ` are radical**, when `X` is not isomorphic to an object of `Σ`. -/
theorem not_isIso_through {Sg : 𝒜 → Prop} (hSloc : ∀ X, Sg X → IsLocalRing (End X))
    (hSiso : ∀ {X Y : 𝒜}, (X ≅ Y) → Sg Y → Sg X) {X : 𝒜} [IsLocalRing (End X)] (hX : ¬ Sg X)
    {f : X ⟶ X} (hf : Through Sg f) : ¬ IsIso f := by
  obtain ⟨n, Z, g, h, hZ, rfl⟩ := hf
  have hterm : ∀ i, (g i ≫ h i : End X) ∈ nonunits (End X) := fun i ↦ by
    have := hSloc _ (hZ i)
    intro hu
    exact not_isIso_comp (g i) (h i) (fun ⟨e⟩ ↦ hX (hSiso e (hZ i)))
      ((CategoryTheory.isUnit_iff_isIso _).1 hu)
  have key : ∀ s : Finset (Fin n), (∑ i ∈ s, g i ≫ h i : End X) ∈ nonunits (End X) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact zero_mem_nonunits.2 zero_ne_one
    | insert i s _ ih =>
        rw [Finset.sum_insert ‹_›]
        exact IsLocalRing.nonunits_add (hterm i) ih
  intro hiso
  exact key Finset.univ ((CategoryTheory.isUnit_iff_isIso _).2 hiso)

/-- Local endomorphism rings are invariant under isomorphism. -/
theorem isLocalRing_of_iso {X Y : 𝒜} (e : X ≅ Y) [IsLocalRing (End Y)] : IsLocalRing (End X) :=
  MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
    { e.symm.conj with
      map_add' := fun f g ↦ by
        simp only [Iso.conj_apply, MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
        rw [Preadditive.add_comp, Preadditive.comp_add] }

/-- **Lemma 5.2** (`lem:deletion-brick`), abstract form. In a `k`-linear abelian category with
finite-dimensional Hom spaces in which every object is Artinian, let `𝒟` be a subcategory closed
under isomorphisms and images, in which every object is a finite direct sum of objects with local
endomorphism rings (Krull–Schmidt), and let `Σ` be a set of objects with local endomorphism
rings, closed under isomorphisms. If some indecomposable object of `𝒟` lies outside `Σ`, there is
one, `X`, such that the endomorphisms of `X` factoring through `Σ` are exactly the
non-invertible ones: the endomorphism ring of `X` in `ind 𝒟/[Σ]` is the residue division algebra
`End(X)/rad`. If that residue algebra is `k`, `X` is a brick of the quotient. -/
theorem deletionBrick [∀ X Y : 𝒜, FiniteDimensional k (X ⟶ Y)] [∀ X : 𝒜, IsArtinianObject X]
    [HasFiniteBiproducts 𝒜]
    (D : 𝒜 → Prop) (hDiso : ∀ {X Y : 𝒜}, (X ≅ Y) → D Y → D X)
    (hDim : ∀ {X Y : 𝒜} (f : X ⟶ Y), D X → D Y → D (image f))
    (hKS : ∀ X, D X → ∃ (n : ℕ) (Y : Fin n → 𝒜), (∀ i, D (Y i) ∧ IsLocalRing (End (Y i))) ∧
      Nonempty (X ≅ ⨁ Y))
    (Sg : 𝒜 → Prop) (hSloc : ∀ X, Sg X → IsLocalRing (End X))
    (hSiso : ∀ {X Y : 𝒜}, (X ≅ Y) → Sg Y → Sg X)
    (hne : ∃ X, D X ∧ IsLocalRing (End X) ∧ ¬ Sg X) :
    ∃ X, D X ∧ IsLocalRing (End X) ∧ ¬ Sg X ∧ (∀ f : X ⟶ X, Through Sg f ↔ ¬ IsIso f) ∧
      ((∀ f : X ⟶ X, ∃ c : k, ¬ IsIso (f - c • 𝟙 X)) →
        ∀ f : X ⟶ X, ∃ c : k, Through Sg (f - c • 𝟙 X)) := by
  classical
  set P : 𝒜 → Prop := fun Y ↦ D Y ∧ IsLocalRing (End Y) ∧ ¬ Sg Y with hP
  have hPiso : ∀ {X Y : 𝒜}, (X ≅ Y) → P Y → P X := fun e ⟨h1, h2, h3⟩ ↦
    ⟨hDiso e h1, isLocalRing_of_iso e, fun h ↦ h3 (hSiso e.symm h)⟩
  obtain ⟨X₀, hX₀⟩ := hne
  set T : Set (Subobject X₀) := {S | P (S : 𝒜)}
  have hS₀ : Subobject.mk (𝟙 X₀) ∈ T := hPiso (Subobject.underlyingIso (𝟙 X₀)) hX₀
  obtain ⟨S, hST, hmin⟩ := (wellFounded_lt (α := Subobject X₀)).has_min T ⟨_, hS₀⟩
  set X : 𝒜 := (S : 𝒜)
  have hX : P X := hST
  obtain ⟨hXD, hXloc, hXS⟩ := hX
  -- minimality: proper subobjects of `X` with `P` do not exist
  have hminY : ∀ {Y : 𝒜} (j : Y ⟶ X) [Mono j], ¬ IsIso j → ¬ P Y := by
    intro Y j _ hj hY
    have hlt : Subobject.mk (j ≫ S.arrow) < S := by
      conv_rhs => rw [← Subobject.mk_arrow S]
      exact Subobject.mk_lt_mk_of_comm j rfl hj
    exact hmin _ (hPiso (Subobject.underlyingIso (j ≫ S.arrow)) hY) hlt
  have hthrough : ∀ f : X ⟶ X, ¬ IsIso f → Through Sg f := by
    intro f hf
    have hne : ¬ Epi f := fun h ↦ hf (isIso_of_epi_end (k := k) f)
    have hι : ¬ IsIso (image.ι f) := by
      intro h
      apply hne
      rw [← image.fac f]
      exact epi_comp _ _
    obtain ⟨n, Y, hY, ⟨e⟩⟩ := hKS _ (hDim f hXD hXD)
    have hYS : ∀ i, Sg (Y i) := by
      intro i
      by_contra hYi
      have hY' := hY i
      have := hY'.2
      apply hminY (biproduct.ι Y i ≫ e.inv ≫ image.ι f) ?_ ⟨hY'.1, hY'.2, hYi⟩
      intro hj
      apply hι
      have hs : (inv (biproduct.ι Y i ≫ e.inv ≫ image.ι f) ≫ biproduct.ι Y i ≫ e.inv) ≫
          image.ι f = 𝟙 X := by
        simp only [Category.assoc, IsIso.inv_hom_id]
      have : IsSplitEpi (image.ι f) := ⟨⟨_, hs⟩⟩
      exact isIso_of_mono_of_epi _
    refine ⟨n, Y, fun i ↦ factorThruImage f ≫ e.hom ≫ biproduct.π Y i,
      fun i ↦ biproduct.ι Y i ≫ e.inv ≫ image.ι f, hYS, ?_⟩
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum, ← Preadditive.comp_sum]
    have : ∑ i, biproduct.π Y i ≫ biproduct.ι Y i ≫ e.inv ≫ image.ι f = e.inv ≫ image.ι f := by
      simp_rw [← Category.assoc (biproduct.π Y _)]
      rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
    rw [this, Iso.hom_inv_id_assoc, image.fac]
  have hiff : ∀ f : X ⟶ X, Through Sg f ↔ ¬ IsIso f :=
    fun f ↦ ⟨not_isIso_through hSloc hSiso hXS, hthrough f⟩
  exact ⟨X, hXD, hXloc, hXS, hiff, fun hres f ↦ by
    obtain ⟨c, hc⟩ := hres f
    exact ⟨c, (hiff _).2 hc⟩⟩

end AbstractBrick

end MultiplicativeBasisDeformations
