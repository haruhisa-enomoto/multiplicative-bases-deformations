module

public import Mathlib

/-!
# Ray tables (Part III, Setting 8.4)

The local arguments of Part III (`local-ray-geometry.tex`, `primitive-ray-equations.tex`,
`integral-partial-lifts.tex`, `local-ray-restrictions.tex`) concern the normed homogeneous ray
basis of `A₀ = kP` (`set:projective-companion`): products of rays are rays or zero, every ray
has a weight in the lattice `L`, the categorical degree is positive on nonidentity rays, and a
ray is determined by its endpoints and weight.

We record this as an abstract finite table `Tab`: rays with source and target, identities,
a partial associative product, weights and a degree. The rays together with a formal unit and
a zero form a monoid with zero `M P`, in which all products of the paper are computed.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

namespace RaySys

/-- A table of rays with a partial associative product and identities. -/
structure Mult (V R : Type) where
  src : R → V
  tgt : R → V
  e : V → R
  src_e : ∀ x, src (e x) = x
  tgt_e : ∀ x, tgt (e x) = x
  mul : R → R → Option R
  mul_src : ∀ r s t, mul r s = some t → src t = src r
  mul_tgt : ∀ r s t, mul r s = some t → tgt t = tgt s
  mul_mid : ∀ r s t, mul r s = some t → tgt r = src s
  e_mul : ∀ r, mul (e (src r)) r = some r
  mul_e : ∀ r, mul r (e (tgt r)) = some r
  assoc : ∀ r s u, (mul r s).bind (fun t ↦ mul t u) = (mul s u).bind (fun t ↦ mul r t)

/-- A finite ray table: a `Mult` with weights in `L` and a positive degree, the weight
determining a ray with given endpoints. -/
structure Tab (V R L : Type) [AddCommGroup L] extends Mult V R where
  wt : R → L
  wt_mul : ∀ r s t, mul r s = some t → wt t = wt r + wt s
  deg : L →+ ℤ
  deg_pos : ∀ r, r ≠ e (src r) → 0 < deg (wt r)
  sep : ∀ r r', src r = src r' → tgt r = tgt r' → wt r = wt r' → r = r'

/-- Rays with a formal unit and a zero. -/
inductive Elt (R : Type)
  | one : Elt R
  | zero : Elt R
  | ray : R → Elt R
  deriving DecidableEq

variable {V R : Type} (P : Mult V R)

/-- The monoid with zero of a ray table. -/
def M (_P : Mult V R) : Type := Elt R

instance [DecidableEq R] : DecidableEq (M P) := inferInstanceAs (DecidableEq (Elt R))

namespace Mult

/-- The product of the monoid with zero. -/
def emul : Elt R → Elt R → Elt R
  | Elt.one, a => a
  | Elt.zero, _ => Elt.zero
  | Elt.ray r, Elt.one => Elt.ray r
  | Elt.ray _, Elt.zero => Elt.zero
  | Elt.ray r, Elt.ray s => match P.mul r s with
    | some t => Elt.ray t
    | none => Elt.zero

theorem emul_ray (r s : R) :
    P.emul (Elt.ray r) (Elt.ray s) = (P.mul r s).elim Elt.zero Elt.ray := by
  simp only [emul]; cases P.mul r s <;> rfl

theorem emul_one (a : Elt R) : P.emul a Elt.one = a := by cases a <;> rfl

theorem emul_zero (a : Elt R) : P.emul a Elt.zero = Elt.zero := by cases a <;> rfl

theorem emul_assoc (a b c : Elt R) : P.emul (P.emul a b) c = P.emul a (P.emul b c) := by
  cases a with
  | one => rfl
  | zero => rfl
  | ray r =>
    cases b with
    | one => rw [emul_one]; rfl
    | zero => cases c <;> rfl
    | ray s =>
      cases c with
      | one => rw [emul_one, emul_one]
      | zero => rw [emul_zero, emul_zero, emul_zero]
      | ray u =>
        have h := P.assoc r s u
        rw [emul_ray, emul_ray]
        cases hrs : P.mul r s with
        | none =>
          rw [hrs] at h
          cases hsu : P.mul s u with
          | none => rfl
          | some t =>
            rw [hsu] at h
            simp only [Option.bind_none, Option.bind_some] at h
            simp only [Option.elim_none, Option.elim_some, emul_ray, ← h]
            rfl
        | some t =>
          rw [hrs] at h
          simp only [Option.bind_some] at h
          simp only [Option.elim_some, emul_ray, h]
          cases hsu : P.mul s u with
          | none => rfl
          | some w => simp [emul_ray]

end Mult

instance : MonoidWithZero (M P) where
  mul := P.emul
  one := Elt.one
  zero := Elt.zero
  mul_assoc := P.emul_assoc
  one_mul _ := rfl
  mul_one := P.emul_one
  zero_mul _ := rfl
  mul_zero := P.emul_zero

namespace Mult

/-- A ray as an element of the monoid with zero. -/
def rr (r : R) : M P := Elt.ray r

theorem one_def : (1 : M P) = Elt.one := rfl

theorem zero_def : (0 : M P) = Elt.zero := rfl

theorem rr_mul_rr (r s : R) : P.rr r * P.rr s = (P.mul r s).elim 0 P.rr :=
  P.emul_ray r s

theorem rr_ne_zero (r : R) : P.rr r ≠ 0 := fun h ↦ by cases h

theorem rr_ne_one (r : R) : P.rr r ≠ 1 := fun h ↦ by cases h

theorem rr_injective : Function.Injective P.rr := fun _ _ h ↦ Elt.ray.inj h

theorem rr_mul_rr_eq_rr {r s t : R} : P.rr r * P.rr s = P.rr t ↔ P.mul r s = some t := by
  rw [rr_mul_rr]
  cases h : P.mul r s with
  | none => exact ⟨fun h' ↦ absurd h'.symm (P.rr_ne_zero t), fun h' ↦ by cases h'⟩
  | some u => exact ⟨fun h' ↦ by rw [P.rr_injective h'], fun h' ↦ by cases h'; rfl⟩

theorem rr_mul_rr_eq_zero {r s : R} : P.rr r * P.rr s = 0 ↔ P.mul r s = none := by
  rw [rr_mul_rr]
  cases h : P.mul r s with
  | none => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | some u => exact ⟨fun h' ↦ absurd h' (P.rr_ne_zero u), fun h' ↦ by cases h'⟩

theorem rr_inj {r s : R} : P.rr r = P.rr s ↔ r = s := P.rr_injective.eq_iff

/-- Every element is the unit, zero, or a ray. -/
theorem cases_elt (a : M P) : a = 1 ∨ a = 0 ∨ ∃ r, a = P.rr r := by
  cases a with
  | one => exact Or.inl rfl
  | zero => exact Or.inr (Or.inl rfl)
  | ray r => exact Or.inr (Or.inr ⟨r, rfl⟩)

theorem rr_mul_rr_ne_zero {r s : R} (h : P.rr r * P.rr s ≠ 0) :
    ∃ t, P.mul r s = some t ∧ P.rr r * P.rr s = P.rr t := by
  cases ht : P.mul r s with
  | none => exact absurd (P.rr_mul_rr_eq_zero.2 ht) h
  | some t => exact ⟨t, rfl, P.rr_mul_rr_eq_rr.2 ht⟩

theorem mul_eq_rr_of {r s t : R} (h : P.rr r * P.rr s = P.rr t) :
    P.src t = P.src r ∧ P.tgt t = P.tgt s ∧ P.tgt r = P.src s := by
  have h' := P.rr_mul_rr_eq_rr.1 h
  exact ⟨P.mul_src _ _ _ h', P.mul_tgt _ _ _ h', P.mul_mid _ _ _ h'⟩

theorem e_mul_rr (r : R) : P.rr (P.e (P.src r)) * P.rr r = P.rr r :=
  P.rr_mul_rr_eq_rr.2 (P.e_mul r)

theorem rr_mul_e (r : R) : P.rr r * P.rr (P.e (P.tgt r)) = P.rr r :=
  P.rr_mul_rr_eq_rr.2 (P.mul_e r)

theorem rr_mul_rr_eq_zero_of_ne {r s : R} (h : P.tgt r ≠ P.src s) : P.rr r * P.rr s = 0 := by
  by_contra h'
  obtain ⟨t, -, ht⟩ := P.rr_mul_rr_ne_zero h'
  exact h (P.mul_eq_rr_of ht).2.2

end Mult

namespace Tab

variable {L : Type} [AddCommGroup L] (P : Tab V R L)

/-! ### Weights and degrees -/

theorem wt_of_mul {r s t : R} (h : P.rr r * P.rr s = P.rr t) : P.wt t = P.wt r + P.wt s :=
  P.wt_mul _ _ _ (P.rr_mul_rr_eq_rr.1 h)

theorem wt_e (x : V) : P.wt (P.e x) = 0 := by
  have := P.wt_mul _ _ _ (P.e_mul (P.e x))
  rw [P.src_e] at this
  exact (add_eq_left.1 this.symm)

theorem deg_nonneg (r : R) : 0 ≤ P.deg (P.wt r) := by
  by_cases h : r = P.e (P.src r)
  · rw [h, wt_e, map_zero]
  · exact (P.deg_pos r h).le

theorem eq_e_of_deg {r : R} (h : P.deg (P.wt r) = 0) : r = P.e (P.src r) := by
  by_contra h'
  exact (P.deg_pos r h').ne' h

theorem eq_e_of_wt {r : R} (h : P.wt r = 0) : r = P.e (P.src r) :=
  P.eq_e_of_deg (by rw [h, map_zero])

theorem tgt_of_eq_e {r : R} (h : r = P.e (P.src r)) : P.tgt r = P.src r := by
  rw [h, P.tgt_e, P.src_e]

/-- A nonidentity ray: its degree is positive. -/
def IsId (r : R) : Prop := r = P.e (P.src r)

end Tab

end RaySys

end MultiplicativeBasisDeformations
