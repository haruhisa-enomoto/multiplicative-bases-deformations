module

public import MultiplicativeBasisDeformations.Foundations.TableRetract
public import MultiplicativeBasisDeformations.Foundations.TableSupport

/-!
# Poset configurations in a ray table (Lemmas 8.9 and C.1)

A *configuration* of a finite poset `Q` in a ray table: objects `(v a, g a)` of the graded
covering category, and rays `ρ a b` for `a ≤ b` of weight `g b - g a`, composing as the poset.
The retraction conditions say that a selected ray never factors as a selected arrow times a
non-selected morphism (on either side); they are required only for cover relations of `Q`
(the arrows of its Hasse diagram, `lem:representation-transfer`, `lem:tree-quotient`).
Then the incidence algebra of `Q` is representation-finite when `kP` is.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)
  {Q : Type} [PartialOrder Q] [Fintype Q] [DecidableEq Q] [DecidableLE Q]

/-- **A configuration of a finite poset** in the graded covering category. -/
structure Conf (P : Tab V R L) (Q : Type) [PartialOrder Q] where
  v : Q → V
  g : Q → L
  ρ : ∀ a b : Q, a ≤ b → R
  src_ρ : ∀ a b h, P.src (ρ a b h) = v a
  tgt_ρ : ∀ a b h, P.tgt (ρ a b h) = v b
  wt_ρ : ∀ a b h, P.wt (ρ a b h) = g b - g a
  mul_ρ : ∀ a b c h1 h2, P.mul (ρ a b h1) (ρ b c h2) = some (ρ a c (le_trans h1 h2))
  retL : ∀ a b c (hab : a ⋖ b) (hac : a ≤ c) (h : R), P.src h = v b → P.tgt h = v c →
    P.wt h = g c - g b → P.mul (ρ a b hab.le) h = some (ρ a c hac) → b ≤ c
  retR : ∀ a b c (hab : a ⋖ b) (hcb : c ≤ b) (h : R), P.src h = v c → P.tgt h = v a →
    P.wt h = g a - g c → P.mul h (ρ a b hab.le) = some (ρ c b hcb) → c ≤ a

namespace Conf

variable {P} (C : Conf P Q)

theorem ρ_eq_of {a b : Q} (hab : a ≤ b) (h : R) (h1 : P.src h = C.v a) (h2 : P.tgt h = C.v b)
    (h3 : P.wt h = C.g b - C.g a) : h = C.ρ a b hab :=
  P.sep _ _ (by rw [h1, C.src_ρ]) (by rw [h2, C.tgt_ρ]) (by rw [h3, C.wt_ρ])

theorem ρ_self (a : Q) : C.ρ a a le_rfl = P.e (C.v a) := by
  have := C.ρ_eq_of le_rfl (P.e (C.v a)) (P.src_e _) (P.tgt_e _) (by rw [P.wt_e, sub_self])
  exact this.symm

variable [LocallyFiniteOrder Q]

theorem retL_all (a b c : Q) (hab : a ≤ b) (hac : a ≤ c) (h : R) (h1 : P.src h = C.v b)
    (h2 : P.tgt h = C.v c) (h3 : P.wt h = C.g c - C.g b)
    (hm : P.mul (C.ρ a b hab) h = some (C.ρ a c hac)) : b ≤ c := by
  induction hn : (Finset.Icc a b).card using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rcases hab.lt_or_eq with hlt | rfl
    · obtain ⟨a1, haa1, ha1b⟩ := exists_covBy_le_of_lt hlt
      have hρ := C.mul_ρ a a1 b haa1.le ha1b
      obtain ⟨w, hw, hw'⟩ := P.mul_assoc_some hρ hm
      have hw1 : P.src w = C.v a1 := by rw [P.mul_src _ _ _ hw, C.src_ρ]
      have hw2 : P.tgt w = C.v c := by rw [P.mul_tgt _ _ _ hw, h2]
      have hw3 : P.wt w = C.g c - C.g a1 := by rw [P.wt_mul _ _ _ hw, C.wt_ρ, h3]; abel
      have ha1c := C.retL a a1 c haa1 hac w hw1 hw2 hw3 hw'
      rw [C.ρ_eq_of ha1c w hw1 hw2 hw3] at hw
      refine ih (Finset.Icc a1 b).card ?_ a1 ha1b ha1c hw rfl
      rw [← hn]
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨Finset.Icc_subset_Icc_left haa1.le, fun he ↦ ?_⟩)
      have : a ∈ Finset.Icc a1 b := he ▸ Finset.mem_Icc.2 ⟨le_rfl, hab⟩
      exact haa1.lt.not_ge (Finset.mem_Icc.1 this).1
    · exact hac

theorem retR_all (a b c : Q) (hab : a ≤ b) (hcb : c ≤ b) (h : R) (h1 : P.src h = C.v c)
    (h2 : P.tgt h = C.v a) (h3 : P.wt h = C.g a - C.g c)
    (hm : P.mul h (C.ρ a b hab) = some (C.ρ c b hcb)) : c ≤ a := by
  induction hn : (Finset.Icc a b).card using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    rcases hab.lt_or_eq with hlt | rfl
    · obtain ⟨b1, hab1, hb1b⟩ := exists_le_covBy_of_lt hlt
      have hρ := C.mul_ρ a b1 b hab1 hb1b.le
      obtain ⟨w', hw'1, hw'2⟩ := P.mul_assoc_some' hρ hm
      have hw1 : P.src w' = C.v c := by rw [P.mul_src _ _ _ hw'1, h1]
      have hw2 : P.tgt w' = C.v b1 := by rw [P.mul_tgt _ _ _ hw'1, C.tgt_ρ]
      have hw3 : P.wt w' = C.g b1 - C.g c := by rw [P.wt_mul _ _ _ hw'1, C.wt_ρ, h3]; abel
      have hcb1 := C.retR b1 b c hb1b hcb w' hw1 hw2 hw3 hw'2
      rw [C.ρ_eq_of hcb1 w' hw1 hw2 hw3] at hw'1
      refine ih (Finset.Icc a b1).card ?_ b1 hab1 hcb1 hw'1 rfl
      rw [← hn]
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨Finset.Icc_subset_Icc_right hb1b.le, fun he ↦ ?_⟩)
      have : b ∈ Finset.Icc a b1 := he ▸ Finset.mem_Icc.2 ⟨hab, le_rfl⟩
      exact hb1b.lt.not_ge (Finset.mem_Icc.1 this).2
    · exact hcb

/-- The embedded ray of a comparable pair. -/
def emb (p : IP Q) : Mult.CR P.toMult C.v P.wt C.g :=
  ⟨⟨(p.1.1, p.1.2, C.ρ p.1.1 p.1.2 p.2), C.src_ρ _ _ _, C.tgt_ρ _ _ _⟩, C.wt_ρ _ _ _⟩

theorem emb_injective : Function.Injective C.emb := fun p p' h ↦ by
  have := congrArg (fun t : Mult.CR P.toMult C.v P.wt C.g ↦ (t.1.1.1, t.1.1.2.1)) h
  exact Subtype.ext this

/-- **The selected rays embed the incidence table into the graded cover.** -/
def mor : Mor (inc Q) (P.cover C.v P.wt P.wt_mul C.g) where
  f p := some (C.emb p)
  hmul p p' := by
    simp only [Option.bind_some]
    by_cases h : p.1.2 = p'.1.1
    · rw [inc_mul_of h, Option.bind_some]
      refine (P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).2
        ((P.toMult.mulI_eq_some_iff C.v).2 ⟨h, ?_, rfl, rfl⟩)
      change P.mul (C.ρ _ _ _) (C.ρ _ _ _) = some (C.ρ _ _ _)
      obtain ⟨⟨a, b⟩, hab⟩ := p
      obtain ⟨⟨b', c⟩, hbc⟩ := p'
      simp only at h
      subst h
      exact C.mul_ρ a b c hab hbc
    · rw [show (inc Q).mul p p' = none by simp [inc, h], Option.bind_none]
      cases hc : (P.cover C.v P.wt P.wt_mul C.g).mul (C.emb p) (C.emb p') with
      | none => rfl
      | some d =>
        exact absurd (P.toMult.mulI_eq_some _
          ((P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).1 hc)).1 h
  hid a := Or.inr ⟨a, by
    simp only [Option.some.injEq]
    apply Subtype.ext; apply Subtype.ext
    change (a, a, C.ρ a a le_rfl) = (a, a, P.e (C.v a))
    rw [C.ρ_self]⟩
  hid' a := ⟨a, by
    simp only [Option.some.injEq]
    apply Subtype.ext; apply Subtype.ext
    change (a, a, C.ρ a a le_rfl) = (a, a, P.e (C.v a))
    rw [C.ρ_self], fun b h ↦ by
      simp only [Option.some.injEq] at h
      exact congrArg (fun t : Mult.CR P.toMult C.v P.wt C.g ↦ t.1.1.1) h⟩

theorem hL (s : IP Q) (t : Mult.CR P.toMult C.v P.wt C.g) (t' : IP Q)
    (hm : (P.cover C.v P.wt P.wt_mul C.g).mul (C.emb s) t = some (C.emb t')) :
    ∃ s', C.emb s' = t := by
  obtain ⟨e1, e2, e3, e4⟩ := P.toMult.mulI_eq_some _
    ((P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).1 hm)
  obtain ⟨⟨⟨b2, c, h⟩, h1, h2⟩, h3⟩ := t
  obtain ⟨⟨a, b⟩, hab⟩ := s
  obtain ⟨⟨a', c'⟩, hac⟩ := t'
  change b = b2 at e1
  change a' = a at e3
  change c' = c at e4
  subst b2 a' c'
  change P.mul (C.ρ a b hab) h = some (C.ρ a c hac) at e2
  have hbc := C.retL_all a b c hab hac h h1 h2 h3 e2
  refine ⟨⟨(b, c), hbc⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change (b, c, C.ρ b c hbc) = (b, c, h)
  rw [← C.ρ_eq_of hbc h h1 h2 h3]

theorem hR (s : IP Q) (t : Mult.CR P.toMult C.v P.wt C.g) (t' : IP Q)
    (hm : (P.cover C.v P.wt P.wt_mul C.g).mul t (C.emb s) = some (C.emb t')) :
    ∃ s', C.emb s' = t := by
  obtain ⟨e1, e2, e3, e4⟩ := P.toMult.mulI_eq_some _
    ((P.toMult.mulC_eq_some_iff C.v P.wt P.wt_mul C.g).1 hm)
  obtain ⟨⟨⟨c, a2, h⟩, h1, h2⟩, h3⟩ := t
  obtain ⟨⟨a, b⟩, hab⟩ := s
  obtain ⟨⟨c', b'⟩, hcb⟩ := t'
  change a2 = a at e1
  change c' = c at e3
  change b' = b at e4
  subst a2 c' b'
  change P.mul h (C.ρ a b hab) = some (C.ρ c b hcb) at e2
  have hca := C.retR_all a b c hab hcb h h1 h2 h3 e2
  refine ⟨⟨(c, a), hca⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change (c, a, C.ρ c a hca) = (c, a, h)
  rw [← C.ρ_eq_of hca h h1 h2 h3]

include C in
/-- **A configuration makes the incidence algebra of the poset representation-finite**
(Lemmas 8.9 and C.1). -/
theorem isRepresentationFinite (k : Type u) [Field k] (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k ((inc Q).Lin k) :=
  Mor.retract_isRepresentationFinite C.mor C.emb (fun _ ↦ rfl) C.emb_injective C.hL C.hR k
    (P.cover_isRepresentationFinite k C.v P.wt P.wt_mul C.g h)

end Conf

end Tab

end RaySys

end MultiplicativeBasisDeformations
