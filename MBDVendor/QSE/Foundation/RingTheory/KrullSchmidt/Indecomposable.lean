/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted for the quotient-submodule equidistribution formalization from TauCeti commit
eeb5b4bee8bf17747ded538639102901e2cd1116.
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import MBDVendor.QSE.Foundation.RingTheory.LocalRing.Basic

/-!
# Indecomposable modules and Fitting's lemma

A module is *indecomposable* when it is nonzero and is not the internal direct
sum of two nonzero submodules. This file introduces the predicate, records its
idempotent reformulation, and proves Fitting's lemma: an endomorphism of an
indecomposable module of finite length is either nilpotent or bijective, so the
endomorphism ring of such a module is local.

Mathlib has the Fitting decomposition of an endomorphism of a Noetherian and
Artinian module (`LinearMap.eventually_isCompl_ker_pow_range_pow`) and
`CategoryTheory.Indecomposable` for objects of a category with binary
biproducts, but no module-level indecomposability predicate and no
local-endomorphism-ring theorem. Both are supplied here.
-/

public section

namespace MBDVendor.QSE.Foundation

universe u v w

section Semiring

variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]

/-- A module is **indecomposable** when it is nonzero and is not the internal
direct sum of two nonzero submodules. -/
def IsIndecomposableModule : Prop :=
  Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥

variable {A M}

/-- `IsIndecomposableModule` restated as the conjunction defining it. -/
theorem isIndecomposableModule_iff_nontrivial_and_forall_isCompl :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥ :=
  Iff.rfl

/-- A nontrivial module along none of whose decompositions both summands are
nonzero is indecomposable. -/
theorem isIndecomposableModule_of_forall_isCompl [Nontrivial M]
    (h : ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥) :
    IsIndecomposableModule A M :=
  ⟨‹_›, h⟩

theorem IsIndecomposableModule.nontrivial
    (h : IsIndecomposableModule A M) : Nontrivial M :=
  h.1

theorem IsIndecomposableModule.eq_bot_or_eq_bot
    (h : IsIndecomposableModule A M) {N P : Submodule A M}
    (hNP : IsCompl N P) : N = ⊥ ∨ P = ⊥ :=
  h.2 N P hNP

/-- Indecomposability transfers along a linear equivalence. -/
theorem IsIndecomposableModule.of_linearEquiv
    {N : Type w} [AddCommMonoid N] [Module A N]
    (h : IsIndecomposableModule A M) (e : M ≃ₗ[A] N) :
    IsIndecomposableModule A N := by
  have := h.nontrivial
  refine ⟨e.symm.toEquiv.nontrivial, fun P Q hPQ ↦ ?_⟩
  simpa using h.eq_bot_or_eq_bot ((Submodule.orderIsoMapComap e.symm).isCompl hPQ)

end Semiring

section Ring

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

/-! ### Indecomposability through idempotent endomorphisms -/

/-- The idempotent endomorphisms of an indecomposable module are `0` and `1`. -/
theorem IsIndecomposableModule.eq_zero_or_eq_one_of_isIdempotentElem
    (h : IsIndecomposableModule A M) {f : Module.End A M}
    (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  rcases h.eq_bot_or_eq_bot (LinearMap.IsIdempotentElem.isCompl hf) with hrange | hker
  · exact Or.inl (LinearMap.range_eq_bot.mp hrange)
  · refine Or.inr (LinearMap.ext fun x ↦ ?_)
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have hx : f (f x) = f x := DFunLike.congr_fun hf x
    simpa using hinj hx

/-- A nonzero module whose only idempotent endomorphisms are `0` and `1` is
indecomposable. -/
theorem isIndecomposableModule_of_forall_isIdempotentElem [Nontrivial M]
    (h : ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1) :
    IsIndecomposableModule A M := by
  refine isIndecomposableModule_of_forall_isCompl fun N P hNP ↦ ?_
  rcases h (N.projection P hNP) (Submodule.isIdempotentElem_projection hNP) with h₀ | h₁
  · exact Or.inl (by simpa [h₀] using (Submodule.range_projection hNP).symm)
  · exact Or.inr (by simpa [h₁, Module.End.one_eq_id] using
      (Submodule.ker_projection hNP).symm)

/-- Indecomposability is equivalent to nontriviality together with having no
idempotent endomorphisms besides `0` and `1`. -/
theorem isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1 :=
  ⟨fun h ↦ ⟨h.nontrivial, fun _ hf ↦ h.eq_zero_or_eq_one_of_isIdempotentElem hf⟩,
    fun ⟨_, h⟩ ↦ isIndecomposableModule_of_forall_isIdempotentElem h⟩

/-- A simple module is indecomposable. -/
theorem IsSimpleModule.isIndecomposableModule [IsSimpleModule A M] :
    IsIndecomposableModule A M := by
  refine ⟨IsSimpleModule.nontrivial A M, fun N P hNP ↦ ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · exact Or.inl hN
  · refine Or.inr ?_
    have hdisj : Disjoint (⊤ : Submodule A M) P := hN ▸ hNP.disjoint
    simpa using hdisj

/-! ### Fitting's lemma -/

section Fitting

variable [IsNoetherian A M] [IsArtinian A M]

/-- Fitting's lemma: an endomorphism of an indecomposable Noetherian and
Artinian module is either nilpotent or bijective. -/
theorem IsIndecomposableModule.isNilpotent_or_bijective
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ∨ Function.Bijective f := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  have hcompl := hn (n + 1) (Nat.le_succ n)
  rcases h.eq_bot_or_eq_bot hcompl with hker | hrange
  · refine Or.inr ⟨?_, ?_⟩
    · have hinj : Function.Injective (f ^ (n + 1)) := LinearMap.ker_eq_bot.mp hker
      intro x y hxy
      refine hinj ?_
      have hpow : f ^ (n + 1) = f ^ n * f := pow_succ f n
      simp only [hpow, Module.End.mul_apply, hxy]
    · have htop : LinearMap.range (f ^ (n + 1)) = ⊤ := by
        have hsup := hcompl.sup_eq_top
        rwa [hker, bot_sup_eq] at hsup
      have hle : LinearMap.range (f ^ (n + 1)) ≤ LinearMap.range f := by
        rw [pow_succ' f n]
        exact LinearMap.range_comp_le_range _ _
      exact LinearMap.range_eq_top.mp (top_le_iff.mp (htop ▸ hle))
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩

/-- Fitting's lemma, restated using units of the endomorphism ring. -/
theorem IsIndecomposableModule.isNilpotent_or_isUnit
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ∨ IsUnit f :=
  (h.isNilpotent_or_bijective f).imp id (Module.End.isUnit_iff f).mpr

/-- On an indecomposable Noetherian and Artinian module, the non-units of the
endomorphism ring are exactly its nilpotents. -/
theorem IsIndecomposableModule.isNilpotent_iff_not_isUnit
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ↔ ¬ IsUnit f := by
  have := h.nontrivial
  exact ⟨IsNilpotent.not_isUnit, (h.isNilpotent_or_isUnit f).resolve_right⟩

end Fitting

/-! ### Local endomorphism rings -/

/-- The endomorphism ring of an indecomposable finite-length module is local. -/
theorem isLocalRing_end_of_isIndecomposable
    (hM : IsFiniteLength A M) (h : IsIndecomposableModule A M) :
    IsLocalRing (Module.End A M) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have := h.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  exact (h.isNilpotent_or_isUnit f).symm.imp id IsNilpotent.isUnit_one_sub

/-- A nonzero module with local endomorphism ring is indecomposable. -/
theorem isIndecomposableModule_of_isLocalRing_end [Nontrivial M]
    [IsLocalRing (Module.End A M)] : IsIndecomposableModule A M :=
  isIndecomposableModule_of_forall_isIdempotentElem fun _ hf ↦
    IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hf

/-- For a finite-length module, indecomposability is equivalent to being
nontrivial and having a local endomorphism ring. -/
theorem isIndecomposableModule_iff_nontrivial_and_isLocalRing_end
    (hM : IsFiniteLength A M) :
    IsIndecomposableModule A M ↔ Nontrivial M ∧ IsLocalRing (Module.End A M) := by
  refine ⟨fun h ↦ ⟨h.nontrivial, isLocalRing_end_of_isIndecomposable hM h⟩,
    fun ⟨_, h⟩ ↦ ?_⟩
  have := h
  exact isIndecomposableModule_of_isLocalRing_end

end Ring

end MBDVendor.QSE.Foundation
