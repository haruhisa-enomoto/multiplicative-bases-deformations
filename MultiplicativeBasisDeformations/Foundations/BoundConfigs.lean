import MultiplicativeBasisDeformations.Foundations.PosetRepBound
import MultiplicativeBasisDeformations.Foundations.RayConfigs

/-!
# Forbidden bound configurations

A configuration (`Tab.ConfZ`) of a table poset with one zero relation `p → m → r` of length
two, whose dimension count `∑ d_v² + d_p d_r ≤ ∑_{x → y} d_x d_y` holds (checked by
`decide`), contradicts finite representation type (Lemmas 8.8 and 8.9).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

open PosetRep

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)

/-- **A forbidden bound configuration.** -/
theorem bound_false (k : Type u) [Field k] [IsAlgClosed k]
    (hfin : IsRepresentationFinite k (P.Lin k)) {n : ℕ} {le : Fin n → Fin n → Bool}
    [Fact (Ax le)] (hu : UniqOK le) {p m r : Fin n} (hpm : covB le p m = true)
    (hmr : covB le m r = true) (d : Fin n → ℕ) (hd : ∃ i, 0 < d i)
    (hN : ∑ i, d i ^ 2 + d r * d p ≤ ∑ i, ∑ j, if covB le i j then d i * d j else 0)
    (C : P.ConfZ (Pos n le) (Zr (⟨p⟩ : Pos n le) ⟨r⟩)) : False := by
  have hpm' : (⟨p⟩ : Pos n le) ⋖ ⟨m⟩ := (pos_covBy_iff _ _).2 hpm
  have hmr' : (⟨m⟩ : Pos n le) ⋖ ⟨r⟩ := (pos_covBy_iff _ _).2 hmr
  have hE : ∀ x y : Pos n le, x ⋖ y → x < y := fun _ _ h ↦ h.lt
  have hinf := not_isRepresentationFinite_bound (k := k) (fun v : Pos n le ↦ d v.v) hE
    (pos_uniq hu) nonempty_ePath hpm' hmr' (by obtain ⟨i, hi⟩ := hd; exact ⟨⟨i⟩, hi⟩)
    (by rw [pos_sq_eq, pos_arr_eq]; exact hN)
  exact hinf (C.isRepresentationFinite (zr_zeroSet hE hpm' hmr') k hfin)

section Table

variable {n : ℕ} {le : Fin n → Fin n → Bool} [Fact (Ax le)] (p r : Fin n)

/-- The zero condition of a table relation. -/
abbrev ZT (le : Fin n → Fin n → Bool) (p r i j : Fin n) : Prop := le i p = true ∧ le r j = true

variable (v : Fin n → V) (g : Fin n → L) (ρt : Fin n → Fin n → R)
  (hsrc : ∀ i j, le i j = true → ¬ ZT le p r i j → P.src (ρt i j) = v i)
  (htgt : ∀ i j, le i j = true → ¬ ZT le p r i j → P.tgt (ρt i j) = v j)
  (hwt : ∀ i j, le i j = true → ¬ ZT le p r i j → P.wt (ρt i j) = g j - g i)
  (hρe : ∀ i, ρt i i = P.e (v i))
  (hmul' : ∀ i j l, le i j = true → le j l = true → i ≠ j → j ≠ l → ¬ ZT le p r i l →
    P.mul (ρt i j) (ρt j l) = some (ρt i l))
  (hmulZ : ∀ i j l, le i j = true → le j l = true → ¬ ZT le p r i j → ¬ ZT le p r j l →
    ZT le p r i l → P.mul (ρt i j) (ρt j l) = none)
  (hretL : ∀ i j l (h : R), covB le i j = true → le i l = true → ¬ ZT le p r i l →
    P.src h = v j → P.tgt h = v l → P.wt h = g l - g j → P.mul (ρt i j) h = some (ρt i l) →
    le j l = true)
  (hretR : ∀ i j l (h : R), covB le i j = true → le l j = true → ¬ ZT le p r l j →
    P.src h = v l → P.tgt h = v i → P.wt h = g i - g l → P.mul h (ρt i j) = some (ρt l j) →
    le l i = true)

include hsrc htgt hρe hmul' in
theorem hmulZ_strict : ∀ i j l, le i j = true → le j l = true → ¬ ZT le p r i l →
    P.mul (ρt i j) (ρt j l) = some (ρt i l) := by
  intro i j l h1 h2 hz
  by_cases hij : i = j
  · subst hij
    rw [hρe, ← hsrc i l h2 hz]
    exact P.e_mul _
  · by_cases hjl : j = l
    · subst hjl
      rw [hρe, ← htgt i j h1 hz]
      exact P.mul_e _
    · exact hmul' i j l h1 h2 hij hjl hz

theorem zt_iff (i j : Fin n) :
    Zr (⟨p⟩ : Pos n le) ⟨r⟩ ⟨i⟩ ⟨j⟩ ↔ ZT le p r i j := Iff.rfl

include hsrc htgt hwt hρe hmul' hmulZ hretL hretR in
/-- **The bound configuration of a table poset given by a table of rays.** -/
def ConfZ.ofTable : P.ConfZ (Pos n le) (Zr (⟨p⟩ : Pos n le) ⟨r⟩) where
  v a := v a.v
  g a := g a.v
  ρ a b _ _ := ρt a.v b.v
  src_ρ a b h h' := hsrc _ _ h h'
  tgt_ρ a b h h' := htgt _ _ h h'
  wt_ρ a b h h' := hwt _ _ h h'
  mul_ρ a b c h1 _ h2 _ hz := P.hmulZ_strict p r v ρt hsrc htgt hρe hmul' _ _ _ h1 h2 hz
  mul_ρ_zero a b c h1 h1' h2 h2' hz := hmulZ _ _ _ h1 h2 h1' h2' hz
  retL a b c hab _ hac hac' h h1 h2 h3 hm :=
    hretL _ _ _ h ((pos_covBy_iff a b).1 hab) hac hac' h1 h2 h3 hm
  retR a b c hab _ hcb hcb' h h1 h2 h3 hm :=
    hretR _ _ _ h ((pos_covBy_iff a b).1 hab) hcb hcb' h1 h2 h3 hm

end Table

end Tab

end RaySys

end MultiplicativeBasisDeformations
