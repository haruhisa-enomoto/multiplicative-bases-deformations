module

public import MultiplicativeBasisDeformations.Foundations.TableConf

/-!
# Incidence tables with zero relations

For Case 2 of Lemma 8.11 (`local-ray-geometry.tex`) the paper uses a tree category with
one zero relation (`F = 1` in Lemma 8.8). Here: the incidence table of a finite poset with a
set `Z` of comparable pairs declared zero, closed under extension (`incZ`), and configurations
of it in a ray table (`ConfZ`), which make its linearization representation-finite when `kP`
is (Lemmas 8.9 and C.1 as in `TableConf`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

section IncZ

variable (Q : Type) [PartialOrder Q] [Fintype Q] [DecidableEq Q] [DecidableLE Q]
  (Z : Q → Q → Prop) [DecidableRel Z]

/-- Comparable pairs outside `Z`. -/
abbrev IPZ := {p : Q × Q // p.1 ≤ p.2 ∧ ¬ Z p.1 p.2}

variable {Q Z}

/-- A zero set: closed under extension, and containing no identity pair. -/
structure ZeroSet (Q : Type) [PartialOrder Q] (Z : Q → Q → Prop) : Prop where
  ext : ∀ a b c d, Z b c → a ≤ b → c ≤ d → Z a d
  irrefl : ∀ a, ¬ Z a a

variable (hZ : ZeroSet Q Z)

/-- The product of the bound incidence table. -/
def mulZ (p p' : IPZ Q Z) : Option (IPZ Q Z) :=
  if h : p.1.2 = p'.1.1 ∧ ¬ Z p.1.1 p'.1.2 then
    some ⟨(p.1.1, p'.1.2), p.2.1.trans (h.1 ▸ p'.2.1), h.2⟩ else none

theorem mulZ_eq_some {p p' t : IPZ Q Z} : mulZ p p' = some t ↔
    p.1.2 = p'.1.1 ∧ ¬ Z p.1.1 p'.1.2 ∧ t.1 = (p.1.1, p'.1.2) := by
  unfold mulZ
  split_ifs with h
  · constructor
    · intro e; cases e; exact ⟨h.1, h.2, rfl⟩
    · rintro ⟨-, -, e⟩; congr 1; exact Subtype.ext e.symm
  · constructor
    · intro e; cases e
    · rintro ⟨e1, e2, -⟩; exact absurd ⟨e1, e2⟩ h

include hZ in
theorem mulZ_assoc (p p' p'' : IPZ Q Z) :
    (mulZ p p').bind (fun t ↦ mulZ t p'') = (mulZ p' p'').bind (fun t ↦ mulZ p t) := by
  ext t
  simp only [Option.bind_eq_some_iff, mulZ_eq_some]
  constructor
  · rintro ⟨s, ⟨h1, h2, hs⟩, h3, h4, ht⟩
    rw [hs] at h3 h4 ht
    simp only at h3 h4 ht
    have hz : ¬ Z p'.1.1 p''.1.2 := fun hz ↦ h4 (hZ.ext _ _ _ _ hz (h1 ▸ p.2.1) le_rfl)
    refine ⟨⟨(p'.1.1, p''.1.2), p'.2.1.trans (h3 ▸ p''.2.1), hz⟩, ⟨h3, hz, rfl⟩, h1, h4, ht⟩
  · rintro ⟨s, ⟨h1, h2, hs⟩, h3, h4, ht⟩
    rw [hs] at h3 h4 ht
    simp only at h3 h4 ht
    have hz : ¬ Z p.1.1 p'.1.2 := fun hz ↦ h4 (hZ.ext _ _ _ _ hz le_rfl (h1 ▸ p''.2.1))
    refine ⟨⟨(p.1.1, p'.1.2), p.2.1.trans (h3 ▸ p'.2.1), hz⟩, ⟨h3, hz, rfl⟩, h1, h4, ht⟩

include hZ in
/-- **The bound incidence table.** -/
def incZ : Mult Q (IPZ Q Z) where
  src p := p.1.1
  tgt p := p.1.2
  e a := ⟨(a, a), le_rfl, hZ.irrefl a⟩
  src_e _ := rfl
  tgt_e _ := rfl
  mul := mulZ
  mul_src p p' t h := by
    unfold mulZ at h; split_ifs at h with h'
    · cases h; rfl
  mul_tgt p p' t h := by
    unfold mulZ at h; split_ifs at h with h'
    · cases h; rfl
  mul_mid p p' t h := by
    unfold mulZ at h; split_ifs at h with h'
    · exact h'.1
  e_mul p := by
    unfold mulZ
    rw [dif_pos ⟨rfl, p.2.2⟩]
  mul_e p := by
    unfold mulZ
    rw [dif_pos ⟨rfl, p.2.2⟩]
  assoc := mulZ_assoc hZ

theorem incZ_mul_of (p p' : IPZ Q Z) (h : p.1.2 = p'.1.1) (hz : ¬ Z p.1.1 p'.1.2) :
    (incZ hZ).mul p p' = some ⟨(p.1.1, p'.1.2), p.2.1.trans (h ▸ p'.2.1), hz⟩ := by
  change mulZ p p' = _
  unfold mulZ; rw [dif_pos ⟨h, hz⟩]

theorem incZ_mul_none (p p' : IPZ Q Z) (h : ¬ (p.1.2 = p'.1.1 ∧ ¬ Z p.1.1 p'.1.2)) :
    (incZ hZ).mul p p' = none := by
  change mulZ p p' = _
  unfold mulZ; rw [dif_neg h]

end IncZ

namespace Tab

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)
  {Q : Type} [PartialOrder Q] [Fintype Q] [DecidableEq Q] [DecidableLE Q]
  {Z : Q → Q → Prop} [DecidableRel Z] (hZ : ZeroSet Q Z)

/-- **A configuration of a bound poset** in the graded covering category. -/
structure ConfZ (P : Tab V R L) (Q : Type) [PartialOrder Q] (Z : Q → Q → Prop) where
  v : Q → V
  g : Q → L
  ρ : ∀ a b : Q, a ≤ b → ¬ Z a b → R
  src_ρ : ∀ a b h h', P.src (ρ a b h h') = v a
  tgt_ρ : ∀ a b h h', P.tgt (ρ a b h h') = v b
  wt_ρ : ∀ a b h h', P.wt (ρ a b h h') = g b - g a
  mul_ρ : ∀ a b c h1 h1' h2 h2' (hz : ¬ Z a c),
    P.mul (ρ a b h1 h1') (ρ b c h2 h2') = some (ρ a c (le_trans h1 h2) hz)
  mul_ρ_zero : ∀ a b c h1 h1' h2 h2', Z a c → P.mul (ρ a b h1 h1') (ρ b c h2 h2') = none
  retL : ∀ a b c (hab : a ⋖ b) (hab' : ¬ Z a b) (hac : a ≤ c) (hac' : ¬ Z a c) (h : R),
    P.src h = v b → P.tgt h = v c → P.wt h = g c - g b →
    P.mul (ρ a b hab.le hab') h = some (ρ a c hac hac') → b ≤ c
  retR : ∀ a b c (hab : a ⋖ b) (hab' : ¬ Z a b) (hcb : c ≤ b) (hcb' : ¬ Z c b) (h : R),
    P.src h = v c → P.tgt h = v a → P.wt h = g a - g c →
    P.mul h (ρ a b hab.le hab') = some (ρ c b hcb hcb') → c ≤ a

namespace ConfZ

variable {P} (C : ConfZ P Q Z)

theorem ρ_eq_of {a b : Q} (hab : a ≤ b) (hab' : ¬ Z a b) (h : R) (h1 : P.src h = C.v a)
    (h2 : P.tgt h = C.v b) (h3 : P.wt h = C.g b - C.g a) : h = C.ρ a b hab hab' :=
  P.sep _ _ (by rw [h1, C.src_ρ]) (by rw [h2, C.tgt_ρ]) (by rw [h3, C.wt_ρ])

theorem ρ_self (a : Q) : C.ρ a a le_rfl (hZ.irrefl a) = P.e (C.v a) :=
  (C.ρ_eq_of le_rfl _ (P.e (C.v a)) (P.src_e _) (P.tgt_e _) (by rw [P.wt_e, sub_self])).symm

variable [LocallyFiniteOrder Q]

include hZ in
theorem retL_all (a b c : Q) (hab : a ≤ b) (hab' : ¬ Z a b) (hac : a ≤ c) (hac' : ¬ Z a c)
    (h : R) (h1 : P.src h = C.v b) (h2 : P.tgt h = C.v c) (h3 : P.wt h = C.g c - C.g b)
    (hm : P.mul (C.ρ a b hab hab') h = some (C.ρ a c hac hac')) : b ≤ c := by
  induction hn : (Finset.Icc a b).card using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rcases hab.lt_or_eq with hlt | rfl
    · obtain ⟨a1, haa1, ha1b⟩ := exists_covBy_le_of_lt hlt
      have hz1 : ¬ Z a a1 := fun hz ↦ hab' (hZ.ext _ _ _ _ hz le_rfl ha1b)
      have hz2 : ¬ Z a1 b := fun hz ↦ hab' (hZ.ext _ _ _ _ hz haa1.le le_rfl)
      have hρ := C.mul_ρ a a1 b haa1.le hz1 ha1b hz2 hab'
      obtain ⟨w, hw, hw'⟩ := P.mul_assoc_some hρ hm
      have hw1 : P.src w = C.v a1 := by rw [P.mul_src _ _ _ hw, C.src_ρ]
      have hw2 : P.tgt w = C.v c := by rw [P.mul_tgt _ _ _ hw, h2]
      have hw3 : P.wt w = C.g c - C.g a1 := by rw [P.wt_mul _ _ _ hw, C.wt_ρ, h3]; abel
      have ha1c := C.retL a a1 c haa1 hz1 hac hac' w hw1 hw2 hw3 hw'
      have hz3 : ¬ Z a1 c := fun hz ↦ hac' (hZ.ext _ _ _ _ hz haa1.le le_rfl)
      rw [C.ρ_eq_of ha1c hz3 w hw1 hw2 hw3] at hw
      refine ih (Finset.Icc a1 b).card ?_ a1 ha1b hz2 ha1c hz3 hw rfl
      rw [← hn]
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨Finset.Icc_subset_Icc_left haa1.le, fun he ↦ ?_⟩)
      have : a ∈ Finset.Icc a1 b := he ▸ Finset.mem_Icc.2 ⟨le_rfl, hab⟩
      exact haa1.lt.not_ge (Finset.mem_Icc.1 this).1
    · exact hac

include hZ in
theorem retR_all (a b c : Q) (hab : a ≤ b) (hab' : ¬ Z a b) (hcb : c ≤ b) (hcb' : ¬ Z c b)
    (h : R) (h1 : P.src h = C.v c) (h2 : P.tgt h = C.v a) (h3 : P.wt h = C.g a - C.g c)
    (hm : P.mul h (C.ρ a b hab hab') = some (C.ρ c b hcb hcb')) : c ≤ a := by
  induction hn : (Finset.Icc a b).card using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    rcases hab.lt_or_eq with hlt | rfl
    · obtain ⟨b1, hab1, hb1b⟩ := exists_le_covBy_of_lt hlt
      have hz1 : ¬ Z a b1 := fun hz ↦ hab' (hZ.ext _ _ _ _ hz le_rfl hb1b.le)
      have hz2 : ¬ Z b1 b := fun hz ↦ hab' (hZ.ext _ _ _ _ hz hab1 le_rfl)
      have hρ := C.mul_ρ a b1 b hab1 hz1 hb1b.le hz2 hab'
      obtain ⟨w', hw'1, hw'2⟩ := P.mul_assoc_some' hρ hm
      have hw1 : P.src w' = C.v c := by rw [P.mul_src _ _ _ hw'1, h1]
      have hw2 : P.tgt w' = C.v b1 := by rw [P.mul_tgt _ _ _ hw'1, C.tgt_ρ]
      have hw3 : P.wt w' = C.g b1 - C.g c := by rw [P.wt_mul _ _ _ hw'1, C.wt_ρ, h3]; abel
      have hcb1 := C.retR b1 b c hb1b hz2 hcb hcb' w' hw1 hw2 hw3 hw'2
      have hz3 : ¬ Z c b1 := fun hz ↦ hcb' (hZ.ext _ _ _ _ hz le_rfl hb1b.le)
      rw [C.ρ_eq_of hcb1 hz3 w' hw1 hw2 hw3] at hw'1
      refine ih (Finset.Icc a b1).card ?_ b1 hab1 hz1 hcb1 hz3 hw'1 rfl
      rw [← hn]
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨Finset.Icc_subset_Icc_right hb1b.le, fun he ↦ ?_⟩)
      have : b ∈ Finset.Icc a b1 := he ▸ Finset.mem_Icc.2 ⟨hab, le_rfl⟩
      exact hb1b.lt.not_ge (Finset.mem_Icc.1 this).2
    · exact hcb

/-- The embedded ray of a pair. -/
def emb (p : IPZ Q Z) : Mult.CR P.toMult C.v P.wt C.g :=
  ⟨⟨(p.1.1, p.1.2, C.ρ p.1.1 p.1.2 p.2.1 p.2.2), C.src_ρ _ _ _ _, C.tgt_ρ _ _ _ _⟩, C.wt_ρ _ _ _ _⟩

theorem emb_injective : Function.Injective C.emb := fun p p' h ↦ by
  have := congrArg (fun t : Mult.CR P.toMult C.v P.wt C.g ↦ (t.1.1.1, t.1.1.2.1)) h
  exact Subtype.ext this

/-- **The selected rays embed the bound incidence table into the graded cover.** -/
def mor : Mor (incZ hZ) (P.cover C.v P.wt P.wt_mul C.g) where
  f p := some (C.emb p)
  hmul p p' := by
    simp only [Option.bind_some]
    by_cases h : p.1.2 = p'.1.1 ∧ ¬ Z p.1.1 p'.1.2
    · rw [incZ_mul_of hZ p p' h.1 h.2, Option.bind_some]
      refine (P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).2
        ((P.toMult.mulI_eq_some_iff C.v).2 ⟨h.1, ?_, rfl, rfl⟩)
      change P.mul (C.ρ _ _ _ _) (C.ρ _ _ _ _) = some (C.ρ _ _ _ _)
      obtain ⟨⟨a, b⟩, hab, hab'⟩ := p
      obtain ⟨⟨b', c⟩, hbc, hbc'⟩ := p'
      obtain ⟨e1, e2⟩ := h
      simp only at e1 e2
      subst e1
      exact C.mul_ρ a b c hab hab' hbc hbc' e2
    · rw [incZ_mul_none hZ p p' h, Option.bind_none]
      cases hc : (P.cover C.v P.wt P.wt_mul C.g).mul (C.emb p) (C.emb p') with
      | none => rfl
      | some d =>
        exfalso
        obtain ⟨e1, e2, -, -⟩ := P.toMult.mulI_eq_some _
          ((P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).1 hc)
        apply h
        refine ⟨e1, fun hz ↦ ?_⟩
        obtain ⟨⟨a, b⟩, hab, hab'⟩ := p
        obtain ⟨⟨b', c⟩, hbc, hbc'⟩ := p'
        change b = b' at e1
        subst e1
        change P.mul (C.ρ a b hab hab') (C.ρ b c hbc hbc') = _ at e2
        rw [C.mul_ρ_zero a b c hab hab' hbc hbc' hz] at e2
        exact absurd e2 (by simp)
  hid a := Or.inr ⟨a, by
    simp only [Option.some.injEq]
    apply Subtype.ext; apply Subtype.ext
    change (a, a, C.ρ a a le_rfl (hZ.irrefl a)) = (a, a, P.e (C.v a))
    rw [C.ρ_self hZ]⟩
  hid' a := ⟨a, by
    simp only [Option.some.injEq]
    apply Subtype.ext; apply Subtype.ext
    change (a, a, C.ρ a a le_rfl (hZ.irrefl a)) = (a, a, P.e (C.v a))
    rw [C.ρ_self hZ], fun b h ↦ by
      simp only [Option.some.injEq] at h
      exact congrArg (fun t : Mult.CR P.toMult C.v P.wt C.g ↦ t.1.1.1) h⟩

variable [LocallyFiniteOrder Q]

include hZ in
theorem hL (s : IPZ Q Z) (t : Mult.CR P.toMult C.v P.wt C.g) (t' : IPZ Q Z)
    (hm : (P.cover C.v P.wt P.wt_mul C.g).mul (C.emb s) t = some (C.emb t')) :
    ∃ s', C.emb s' = t := by
  obtain ⟨e1, e2, e3, e4⟩ := P.toMult.mulI_eq_some _
    ((P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).1 hm)
  obtain ⟨⟨⟨b2, c, h⟩, h1, h2⟩, h3⟩ := t
  obtain ⟨⟨a, b⟩, hab, hab'⟩ := s
  obtain ⟨⟨a', c'⟩, hac, hac'⟩ := t'
  change b = b2 at e1
  change a' = a at e3
  change c' = c at e4
  subst b2 a' c'
  change P.mul (C.ρ a b hab hab') h = some (C.ρ a c hac hac') at e2
  have hbc := C.retL_all hZ a b c hab hab' hac hac' h h1 h2 h3 e2
  have hbc' : ¬ Z b c := fun hz ↦ hac' (hZ.ext _ _ _ _ hz hab le_rfl)
  refine ⟨⟨(b, c), hbc, hbc'⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change (b, c, C.ρ b c hbc hbc') = (b, c, h)
  rw [← C.ρ_eq_of hbc hbc' h h1 h2 h3]

include hZ in
theorem hR (s : IPZ Q Z) (t : Mult.CR P.toMult C.v P.wt C.g) (t' : IPZ Q Z)
    (hm : (P.cover C.v P.wt P.wt_mul C.g).mul t (C.emb s) = some (C.emb t')) :
    ∃ s', C.emb s' = t := by
  obtain ⟨e1, e2, e3, e4⟩ := P.toMult.mulI_eq_some _
    ((P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).1 hm)
  obtain ⟨⟨⟨c, a2, h⟩, h1, h2⟩, h3⟩ := t
  obtain ⟨⟨a, b⟩, hab, hab'⟩ := s
  obtain ⟨⟨c', b'⟩, hcb, hcb'⟩ := t'
  change a2 = a at e1
  change c' = c at e3
  change b' = b at e4
  subst a2 c' b'
  change P.mul h (C.ρ a b hab hab') = some (C.ρ c b hcb hcb') at e2
  have hca := C.retR_all hZ a b c hab hab' hcb hcb' h h1 h2 h3 e2
  have hca' : ¬ Z c a := fun hz ↦ hcb' (hZ.ext _ _ _ _ hz le_rfl hab)
  refine ⟨⟨(c, a), hca, hca'⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change (c, a, C.ρ c a hca hca') = (c, a, h)
  rw [← C.ρ_eq_of hca hca' h h1 h2 h3]

include C in
/-- **A bound configuration makes the bound incidence algebra representation-finite.** -/
theorem isRepresentationFinite (k : Type u) [Field k] (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((incZ hZ).Lin k) :=
  Mor.retract_isRepresentationFinite (C.mor hZ) C.emb (fun _ ↦ rfl) C.emb_injective (C.hL hZ)
    (C.hR hZ) k (P.cover_isRepresentationFinite k C.v P.wt P.wt_mul C.g h)

end ConfZ

end Tab

end RaySys

end MultiplicativeBasisDeformations
