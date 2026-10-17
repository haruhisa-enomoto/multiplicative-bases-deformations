import MultiplicativeBasisDeformations.Refinements.LiftedRadical

/-!
# Proposition 6.5(3): regular lifts at projective labels

`positive-deformations.tex`: "If `M_i = e_xΛ` for a primitive idempotent `e_x` of `Λ₀`,
we may choose `M_i^B = e_xB` for a lift `e_x ∈ B` of that idempotent. […] At a projective
label, the actual regular module `e_xB` has the required associated grading."

We give `eΛ` (`e` of degree zero) its graded right module structure (`rightIdeal`), and show
that the regular module `e B`, identified with `eΛ` through a splitting `φ` multiplicative on
the left by `e` (Lemma 6.4), is a filtered lift of `eΛ` (`regularLift`). By the uniqueness of
Proposition 6.5(1) it is then isomorphic to any other filtered lift.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] (G : LenGrading k Λ)

theorem proj_mul_left {e : Λ} (he : G.IsHom 0 e) (d : ℕ) (a : Λ) :
    G.proj d (e * a) = e * G.proj d a := by
  conv_lhs => rw [G.sum a, Finset.mul_sum, map_sum]
  by_cases hd : d < G.N
  · rw [Finset.sum_eq_single d]
    · have := G.isHom_mul he (G.isHom_proj d a)
      rw [zero_add] at this
      exact this
    · intro d' _ hd'
      have := G.isHom_mul he (G.isHom_proj d' a)
      rw [zero_add] at this
      rw [G.proj_of_isHom this, if_neg hd']
    · intro h; exact absurd (Finset.mem_range.2 hd) h
  · simp [G.proj_ge d (by omega)]

end LenGrading

namespace GExt

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  (h1 : G.IsHom 0 (1 : Λ)) {e : Λ} (he : G.IsHom 0 e) (hidem : IsIdempotentElem e)

variable (k) in
/-- The right ideal `eΛ`. -/
abbrev RI (e : Λ) : Submodule k Λ := LinearMap.range (LinearMap.mulLeft k e)

include hidem in
theorem mem_RI {x : Λ} : x ∈ RI k e ↔ e * x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, hidem.eq]
  · intro h; exact ⟨x, h⟩

include he hidem in
theorem proj_mem_RI {x : Λ} (hx : x ∈ RI k e) (p : ℤ) : (ZGr.ofLen G).proj p x ∈ RI k e := by
  rw [mem_RI hidem] at hx ⊢
  simp only [ZGr.ofLen]
  split_ifs
  · rw [← hx, G.proj_mul_left he, ← mul_assoc, hidem.eq]
  · simp

include he hidem in
/-- The grading of `eΛ`. -/
def riGr : ZGr (R := k) (RI k e) where
  proj p := ((ZGr.ofLen G).proj p).restrict fun x hx ↦ proj_mem_RI he hidem hx p
  supp := (ZGr.ofLen G).supp
  proj_proj p q m := by
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, (ZGr.ofLen G).proj_proj]
    split_ifs <;> rfl
  proj_out p hp := by
    ext m
    simp only [LinearMap.restrict_apply, (ZGr.ofLen G).proj_out p hp, LinearMap.zero_apply]
    rfl
  sum m := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, LinearMap.restrict_apply]
    exact (ZGr.ofLen G).sum m

include h1 he hidem in
/-- **The graded right module `eΛ`.** -/
def rightIdeal : GMod (GAlg.ofLen G h1) (RI k e) where
  act := LinearMap.mk₂ k (fun m a ↦ ⟨m.1 * a, by
      rw [mem_RI hidem, ← mul_assoc, (mem_RI hidem).1 m.2]⟩)
    (fun m m' a ↦ Subtype.ext (add_mul _ _ _)) (fun c m a ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun m a a' ↦ Subtype.ext (mul_add _ _ _)) (fun c m a ↦ Subtype.ext (mul_smul_comm _ _ _))
  act_one m := Subtype.ext (mul_one _)
  act_mul m a b := Subtype.ext (mul_assoc _ _ _)
  gr := riGr he hidem
  act_hom p q m a hm ha := by
    have := (GAlg.ofLen G h1).mul_hom p q m.1 a (congrArg Subtype.val hm) ha
    exact Subtype.ext this

end GExt

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

namespace PosFiltration

universe u v w

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)

/-- **Lemma 6.4 with the left `S`-linearity** of the splitting. -/
theorem exists_split_left (V : Vertices G) :
    ∃ S : Split P, ∀ i a, S.φ (V.e i * a) = S.φ (V.e i) * S.φ a := by
  obtain ⟨φ, hc, hl, -, hσ, hF⟩ := P.exists_split V
  exact ⟨⟨φ, by rw [← V.complete.complete, map_sum, hc.complete], hσ, hF⟩, hl⟩

variable {P} (h1 : G.IsHom 0 (1 : Λ)) {e : Λ} (he : G.IsHom 0 e) (hidem : IsIdempotentElem e)

/-- **The regular module `eB` is a filtered lift of `eΛ`** (Proposition 6.5(3), last
sentence): its action, transported along the splitting, is `m · y = φ⁻¹(φ(m) y)`. -/
def Split.regularLift (S : Split P) (hleft : ∀ a, S.φ (e * a) = S.φ e * S.φ a) :
    FLift P h1 (GExt.rightIdeal h1 he hidem) where
  act := LinearMap.mk₂ k
    (fun m y ↦ ⟨S.φ.symm (S.φ m.1 * y), by
      rw [GExt.mem_RI hidem]
      apply S.φ.injective
      rw [hleft, LinearEquiv.apply_symm_apply, ← mul_assoc, ← hleft,
        (GExt.mem_RI hidem).1 m.2]⟩)
    (fun m m' y ↦ Subtype.ext (by simp [add_mul]))
    (fun c m y ↦ Subtype.ext (by simp [smul_mul_assoc]))
    (fun m y y' ↦ Subtype.ext (by simp [mul_add]))
    (fun c m y ↦ Subtype.ext (by simp [mul_smul_comm]))
  mul m x y := Subtype.ext (by
    simp only [LinearMap.mk₂_apply, LinearEquiv.apply_symm_apply, mul_assoc])
  one m := Subtype.ext (by simp)
  filt d p m x hx hm f hf := by
    apply Subtype.ext
    simp only [LinearMap.mk₂_apply]
    change (GExt.ZGr.ofLen G).proj f (S.φ.symm (S.φ m.1 * x)) = 0
    rcases lt_or_ge p 0 with hp | hp
    · have hm0 : m.1 = 0 := (GExt.ZGr.ofLen_isHom_neg G hp m.1).1 (congrArg Subtype.val hm)
      rw [hm0]; simp
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have hm' : G.IsHom p' m.1 := (GExt.ZGr.ofLen_isHom G p' m.1).1 (congrArg Subtype.val hm)
    have hge : G.Ge (p' + d) (S.φ.symm (S.φ m.1 * x)) :=
      (S.mem_F_iff).1 (by
        rw [LinearEquiv.apply_symm_apply]
        exact P.F_mul p' d _ _ ((S.mem_F_iff).2 (G.ge_of_isHom hm')) hx)
    simp only [GExt.ZGr.ofLen]
    split_ifs with hf0
    · exact hge f.toNat (by omega)
    · rfl
  lead d p m x hx hm := by
    apply Subtype.ext
    simp only [LinearMap.mk₂_apply]
    change (GExt.ZGr.ofLen G).proj (p + d) (S.φ.symm (S.φ m.1 * x)) = m.1 * P.σ d x
    rcases lt_or_ge p 0 with hp | hp
    · have hm0 : m.1 = 0 := (GExt.ZGr.ofLen_isHom_neg G hp m.1).1 (congrArg Subtype.val hm)
      rw [hm0]; simp
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have hm' : G.IsHom p' m.1 := (GExt.ZGr.ofLen_isHom G p' m.1).1 (congrArg Subtype.val hm)
    have hmF : S.φ m.1 ∈ P.F p' := (S.mem_F_iff).2 (G.ge_of_isHom hm')
    have hge : G.Ge (p' + d) (S.φ.symm (S.φ m.1 * x)) :=
      (S.mem_F_iff).1 (by rw [LinearEquiv.apply_symm_apply]; exact P.F_mul p' d _ _ hmF hx)
    simp only [GExt.ZGr.ofLen, show (0 : ℤ) ≤ (p' : ℤ) + d by omega, if_true]
    rw [show ((p' : ℤ) + d).toNat = p' + d by omega, ← S.σ_ge hge, LinearEquiv.apply_symm_apply,
      P.σ_mul p' d _ _ hmF hx, S.σφ p' _ hm']

end PosFiltration

end MultiplicativeBasisDeformations
