import MultiplicativeBasisDeformations.Foundations.PositiveDeformation

/-!
# Fibre algebras of deformation families (toward Proposition 12.8)

A scalar fibre of a family `m + Σ_i t_i μ_i` (`characteristic-two-construction.tex`) is
the underlying space of `Λ` with an associative unital bilinear product. `Fib A` is that algebra
(`AssocMul`). When the product agrees with that of `Λ` up to terms raising the length degree,
the length filtration of `Λ` makes `Fib A` a positive filtered deformation of `Λ`
(`Fib.posFiltration`, Definition 6.2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ]

variable (k Λ) in
/-- An associative unital `k`-bilinear product on `Λ`. -/
structure AssocMul where
  mm : Λ →ₗ[k] Λ →ₗ[k] Λ
  assoc : ∀ a b c, mm (mm a b) c = mm a (mm b c)
  one_left : ∀ a, mm 1 a = a
  one_right : ∀ a, mm a 1 = a

/-- **The fibre algebra**: `Λ` with the product `A.mm`. -/
def Fib (_A : AssocMul k Λ) : Type v := Λ

namespace Fib

variable (A : AssocMul k Λ)

instance : AddCommGroup (Fib A) := inferInstanceAs (AddCommGroup Λ)

instance : Module k (Fib A) := inferInstanceAs (Module k Λ)

/-- The identification with `Λ` as a `k`-module. -/
def toΛ : Fib A ≃ₗ[k] Λ := LinearEquiv.refl k Λ

instance : Ring (Fib A) :=
  { (inferInstance : AddCommGroup (Fib A)) with
    mul := fun a b ↦ (toΛ A).symm (A.mm (toΛ A a) (toΛ A b))
    one := (toΛ A).symm 1
    mul_assoc := fun a b c ↦ A.assoc (toΛ A a) (toΛ A b) (toΛ A c)
    one_mul := fun a ↦ A.one_left (toΛ A a)
    mul_one := fun a ↦ A.one_right (toΛ A a)
    left_distrib := fun a b c ↦ (A.mm (toΛ A a)).map_add (toΛ A b) (toΛ A c)
    right_distrib := fun a b c ↦ LinearMap.congr_fun (A.mm.map_add (toΛ A a) (toΛ A b)) (toΛ A c)
    zero_mul := fun a ↦ LinearMap.congr_fun A.mm.map_zero (toΛ A a)
    mul_zero := fun a ↦ (A.mm (toΛ A a)).map_zero }

theorem toΛ_mul (a b : Fib A) : toΛ A (a * b) = A.mm (toΛ A a) (toΛ A b) := rfl

theorem toΛ_one : toΛ A (1 : Fib A) = 1 := rfl

instance : Algebra k (Fib A) :=
  Algebra.ofModule (fun t a b ↦ by
      change (toΛ A).symm (A.mm (toΛ A (t • a)) (toΛ A b)) = t • (toΛ A).symm _
      rw [map_smul, map_smul, LinearMap.smul_apply, map_smul])
    (fun t a b ↦ by
      change (toΛ A).symm (A.mm (toΛ A a) (toΛ A (t • b))) = t • (toΛ A).symm _
      rw [map_smul, map_smul, map_smul])

variable {A} (G : LenGrading k Λ)
  (hdef : ∀ d e a b, G.IsHom d a → G.IsHom e b → G.Ge (d + e + 1) (A.mm a b - a * b))

include hdef in
theorem ge_mm_sub_hom {d e : ℕ} {a b : Λ} (ha : G.Ge d a) (hb : G.Ge e b) :
    G.Ge (d + e + 1) (A.mm a b - a * b) := by
  rw [G.eq_sum_proj_of_ge ha, G.eq_sum_proj_of_ge hb]
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine G.geSub (d + e + 1) |>.sum_mem fun d' hd' ↦ G.geSub (d + e + 1) |>.sum_mem fun e' he' ↦ ?_
  have h1 := (Finset.mem_Ico.1 hd').1
  have h2 := (Finset.mem_Ico.1 he').1
  exact G.ge_mono (by omega) (hdef _ _ _ _ (G.isHom_proj _ _) (G.isHom_proj _ _))

include hdef in
theorem ge_mm {d e : ℕ} {a b : Λ} (ha : G.Ge d a) (hb : G.Ge e b) : G.Ge (d + e) (A.mm a b) := by
  have h := G.ge_add (G.ge_mono (by omega) (ge_mm_sub_hom G hdef ha hb)) (G.ge_mul ha hb)
  rwa [sub_add_cancel] at h

include hdef in
theorem proj_mm {d e : ℕ} {a b : Λ} (ha : G.Ge d a) (hb : G.Ge e b) :
    G.proj (d + e) (A.mm a b) = G.proj d a * G.proj e b := by
  have hsplit : A.mm a b = G.proj d a * G.proj e b + (G.proj d a * (b - G.proj e b) +
      (a - G.proj d a) * b) + (A.mm a b - a * b) := by noncomm_ring
  have hhom : G.IsHom (d + e) (G.proj d a * G.proj e b) :=
    G.isHom_mul (G.isHom_proj d a) (G.isHom_proj e b)
  have hge : G.Ge (d + e + 1) (G.proj d a * (b - G.proj e b) + (a - G.proj d a) * b) := by
    refine G.ge_add ?_ ?_
    · have := G.ge_mul (G.ge_of_isHom (G.isHom_proj d a)) (G.ge_sub_proj hb)
      rwa [show d + (e + 1) = d + e + 1 by omega] at this
    · have := G.ge_mul (G.ge_sub_proj ha) hb
      rwa [show d + 1 + e = d + e + 1 by omega] at this
  rw [hsplit, map_add, map_add, hhom, hge (d + e) (by omega),
    ge_mm_sub_hom G hdef ha hb (d + e) (by omega), add_zero, add_zero]

include hdef in
/-- **A fibre is a positive filtered deformation** (Definition 6.2), filtered by length. -/
def posFiltration : PosFiltration G (Fib A) where
  F d := (G.geSub d).comap (toΛ A).toLinearMap
  F_zero := by ext a; simp [LenGrading.mem_geSub, G.ge_zero]
  F_succ_le d a ha := G.ge_mono (Nat.le_succ d) ha
  F_mul d e a b ha hb := ge_mm G hdef (A := A) ha hb
  M := G.N
  F_M := by
    ext a
    simp only [Submodule.mem_comap, LenGrading.mem_geSub, Submodule.mem_bot]
    exact ⟨fun h ↦ G.eq_zero_of_ge h le_rfl, fun h ↦ by rw [h]; exact fun _ _ ↦ by simp⟩
  σ d := G.proj d ∘ₗ (toΛ A).toLinearMap
  σ_hom d a := G.isHom_proj d _
  σ_ker d a ha := by
    change G.proj d (toΛ A a) = 0 ↔ G.Ge (d + 1) (toΛ A a)
    constructor
    · intro h e he
      rcases Nat.lt_or_ge e d with h' | h'
      · exact ha e h'
      · obtain rfl : e = d := by omega
        exact h
    · intro h; exact h d (by omega)
  σ_surj d x hx := ⟨(toΛ A).symm x, G.ge_of_isHom hx, hx⟩
  σ_mul d e a b ha hb := proj_mm G hdef (A := A) ha hb

end Fib

end MultiplicativeBasisDeformations
