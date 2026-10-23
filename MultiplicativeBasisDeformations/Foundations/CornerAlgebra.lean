module

public import Mathlib

/-!
# Corner algebras

For an idempotent `e` of a `k`-algebra `A`, Mathlib's corner ring
`IsIdempotentElem.Corner` is `eAe` with identity `e`. This file makes it a
`k`-algebra, with `c ↦ c • e` as structure map.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A]
  {e : A} (idem : IsIdempotentElem e)

/-- The underlying element of `A` of an element of the corner. -/
def cornerVal (x : idem.Corner) : A := (show ↥(Subsemigroup.corner e) from x).1

/-- An element of `A` lying in the corner, as an element of the corner. -/
def cornerMk (a : A) (ha : a ∈ Subsemigroup.corner e) : idem.Corner :=
  show ↥(Subsemigroup.corner e) from ⟨a, ha⟩

theorem cornerVal_mem (x : idem.Corner) : cornerVal idem x ∈ Subsemigroup.corner e :=
  (show ↥(Subsemigroup.corner e) from x).2

@[ext]
theorem corner_ext {x y : idem.Corner} (h : cornerVal idem x = cornerVal idem y) : x = y :=
  Subtype.ext (p := (· ∈ Subsemigroup.corner e)) h

@[simp]
theorem cornerVal_mk (a : A) (ha : a ∈ Subsemigroup.corner e) :
    cornerVal idem (cornerMk idem a ha) = a := rfl

theorem corner_smul_mem (c : k) (x : idem.Corner) :
    c • cornerVal idem x ∈ Subsemigroup.corner e := by
  obtain ⟨r, hr⟩ := cornerVal_mem idem x
  exact ⟨c • r, by
    simp only at hr ⊢
    rw [← hr, mul_smul_comm, smul_mul_assoc]⟩

instance cornerSMul : SMul k idem.Corner where
  smul c x := cornerMk idem (c • cornerVal idem x) (corner_smul_mem idem c x)

@[simp]
theorem corner_smul_val (c : k) (x : idem.Corner) :
    cornerVal idem (c • x) = c • cornerVal idem x := rfl

@[simp]
theorem corner_one_val : cornerVal idem (1 : idem.Corner) = e := rfl

@[simp]
theorem corner_mul_val (x y : idem.Corner) : cornerVal idem (x * y) = cornerVal idem x * cornerVal idem y :=
  rfl

@[simp]
theorem corner_add_val (x y : idem.Corner) : cornerVal idem (x + y) = cornerVal idem x + cornerVal idem y :=
  rfl

@[simp]
theorem corner_zero_val : cornerVal idem (0 : idem.Corner) = 0 := rfl

theorem corner_mul_left (x : idem.Corner) : e * cornerVal idem x = cornerVal idem x :=
  ((Subsemigroup.mem_corner_iff idem).mp (cornerVal_mem idem x)).1

theorem corner_mul_right (x : idem.Corner) : cornerVal idem x * e = cornerVal idem x :=
  ((Subsemigroup.mem_corner_iff idem).mp (cornerVal_mem idem x)).2

/-- The corner `eAe` is a `k`-algebra. -/
instance cornerAlgebra : Algebra k idem.Corner where
  algebraMap :=
    { toFun c := c • (1 : idem.Corner)
      map_one' := corner_ext idem (by simp)
      map_mul' c d := corner_ext idem (by
        simp only [corner_smul_val, corner_one_val, corner_mul_val]
        rw [smul_mul_smul_comm, idem.eq, mul_comm])
      map_zero' := corner_ext idem (by simp)
      map_add' c d := corner_ext idem (by simp [add_smul]) }
  commutes' c x := corner_ext idem (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, corner_mul_val,
      corner_smul_val, corner_one_val, smul_mul_assoc, mul_smul_comm,
      corner_mul_left, corner_mul_right])
  smul_def' c x := corner_ext idem (by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, corner_mul_val,
      corner_smul_val, corner_one_val, smul_mul_assoc, corner_mul_left])

end MultiplicativeBasisDeformations
