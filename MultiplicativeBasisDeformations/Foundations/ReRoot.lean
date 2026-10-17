import MultiplicativeBasisDeformations.Foundations.DeckData
import MultiplicativeBasisDeformations.Foundations.ZTransport

/-!
# Changing the root of a star model

`periodic-mesh-calculations.tex`: "for odd `A`, root it at its middle
vertex". A covering `π : ℤΔ → Q` and its deck data transport along an
isomorphism `e : Δ ≃ Δ'` of star models (any graph isomorphism; the heights
shift by `δ` to match the two-colourings).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u w

namespace ReRoot

open OrientedTree StarGauge

variable {t t' : ℕ} {L : Fin t → ℕ} {L' : Fin t' → ℕ}
  (e : StarV L ≃ StarV L') (he : ∀ a b, (starTree L).G.Adj a b ↔ (starTree L').G.Adj (e a) (e b))
  (δ : ℤ) (hδ : ∀ d, (starTree L').par (e d) = (starTree L).par d + δ)

/-- The isomorphism of repetitions. -/
abbrev zE : (starTree L).ZVert ≃ (starTree L').ZVert := zEquiv (starTree L) (starTree L') e δ hδ

include he in
theorem zE_hom (X Y : (starTree L).ZVert) :
    Nonempty (zE e δ hδ X ⟶ zE e δ hδ Y) ↔ Nonempty (X ⟶ Y) :=
  nonempty_hom_zMap_iff (starTree L) (starTree L') e he δ hδ X Y

theorem zE_ztau (X : (starTree L).ZVert) :
    zE e δ hδ ((starTree L).ztau X) = (starTree L').ztau (zE e δ hδ X) := by
  apply ZVert.ext
  · rfl
  · change X.t - 2 + δ = X.t + δ - 2; ring

variable {V : Type u} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)

include he in
theorem nonempty_map {Y Y' : (starTree L').ZVert} (a : Y ⟶ Y') :
    Nonempty (π.obj ((zE e δ hδ).symm Y) ⟶ π.obj ((zE e δ hδ).symm Y')) := by
  have : Nonempty ((zE e δ hδ).symm Y ⟶ (zE e δ hδ).symm Y') := by
    rw [← zE_hom e he δ hδ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact ⟨a⟩
  obtain ⟨b⟩ := this
  exact ⟨π.map b⟩

/-- The transported covering. -/
def π' : (starTree L').ZVert ⥤q V where
  obj Y := π.obj ((zE e δ hδ).symm Y)
  map a := Classical.choice (nonempty_map e he δ hδ π a)

theorem π'_obj (Y : (starTree L').ZVert) : (π' e he δ hδ π).obj Y = π.obj ((zE e δ hδ).symm Y) :=
  rfl

theorem π'_isCovering (hπ : π.IsCovering) : (π' e he δ hδ π).IsCovering :=
  isCovering_transport (zE e δ hδ) (zE_hom e he δ hδ) π hπ _ fun _ ↦ rfl

theorem π'_tau (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
    (Y : (starTree L').ZVert) :
    (π' e he δ hδ π).obj ((starTree L').ztau Y) = hQ.tauE ((π' e he δ hδ π).obj Y) := by
  rw [π'_obj, π'_obj, ← hτ]
  congr 1
  apply (zE e δ hδ).injective
  rw [zE_ztau, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem π'_surj (hsurj : ∀ x : V, ∃ X, π.obj X = x) (x : V) : ∃ Y, (π' e he δ hδ π).obj Y = x := by
  obtain ⟨X, hX⟩ := hsurj x
  exact ⟨zE e δ hδ X, by rw [π'_obj, Equiv.symm_apply_apply, hX]⟩

/-! ### Transport of the deck data -/

variable (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))

/-- The transported deck automorphism `e ρ e⁻¹`. -/
def ρ' : StarV L' ≃ StarV L' := e.symm.trans (ρ.trans e)

include he hρ in
theorem ρ'_adj (a b : StarV L') :
    (starTree L').G.Adj (ρ' e ρ a) (ρ' e ρ b) ↔ (starTree L').G.Adj a b := by
  simp only [ρ', Equiv.trans_apply]
  rw [← he, hρ, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

include hδ hρp in
theorem ρ'_par (v : StarV L') :
    (starTree L').par (ρ' e ρ v) = (starTree L').par v + ((c0 : ℤ) : ZMod 2) := by
  simp only [ρ', Equiv.trans_apply]
  have h1 := hδ (ρ (e.symm v))
  have h2 := hδ (e.symm v)
  rw [Equiv.apply_symm_apply] at h2
  rw [h1, hρp, h2]; ring

theorem zE_zAct (X : (starTree L).ZVert) :
    zE e δ hδ (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj X) =
      ((starTree L').zAct (ρ' e ρ) (ρ'_adj e he ρ hρ) (c0 : ℤ) (ρ'_par e δ hδ ρ c0 hρp)).obj
        (zE e δ hδ X) := by
  apply ZVert.ext
  · change e (ρ X.v) = e (ρ (e.symm (e X.v))); rw [Equiv.symm_apply_apply]
  · change X.t + c0 + δ = X.t + δ + c0; ring

theorem zE_symm_zAct (Y : (starTree L').ZVert) :
    (zE e δ hδ).symm (((starTree L').zAct (ρ' e ρ) (ρ'_adj e he ρ hρ) (c0 : ℤ)
      (ρ'_par e δ hδ ρ c0 hρp)).obj Y) =
        ((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj ((zE e δ hδ).symm Y) := by
  apply (zE e δ hδ).injective
  rw [Equiv.apply_symm_apply, zE_zAct e he δ hδ ρ hρ c0 hρp, Equiv.apply_symm_apply]

theorem π'_deck (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
    (Y : (starTree L').ZVert) :
    (π' e he δ hδ π).obj (((starTree L').zAct (ρ' e ρ) (ρ'_adj e he ρ hρ) (c0 : ℤ)
      (ρ'_par e δ hδ ρ c0 hρp)).obj Y) = (π' e he δ hδ π).obj Y := by
  rw [π'_obj, π'_obj, zE_symm_zAct e he δ hδ ρ hρ c0 hρp, hdeck]

theorem zE_iter (n : ℕ) (X : (starTree L).ZVert) :
    zE e δ hδ ((gZ ρ hρ c0 hρp)^[n] X) =
      (gZ (ρ' e ρ) (ρ'_adj e he ρ hρ) c0 (ρ'_par e δ hδ ρ c0 hρp))^[n] (zE e δ hδ X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
      zE_zAct e he δ hδ ρ hρ c0 hρp]

theorem π'_fib
    (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
      ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)
    (X Y : (starTree L').ZVert) (h : (π' e he δ hδ π).obj X = (π' e he δ hδ π).obj Y) :
    ∃ n : ℕ, Y = (gZ (ρ' e ρ) (ρ'_adj e he ρ hρ) c0 (ρ'_par e δ hδ ρ c0 hρp))^[n] X ∨
      X = (gZ (ρ' e ρ) (ρ'_adj e he ρ hρ) c0 (ρ'_par e δ hδ ρ c0 hρp))^[n] Y := by
  obtain ⟨n, hn | hn⟩ := hfib _ _ h
  · refine ⟨n, Or.inl ?_⟩
    have := congrArg (zE e δ hδ) hn
    rwa [Equiv.apply_symm_apply, zE_iter e he δ hδ ρ hρ c0 hρp, Equiv.apply_symm_apply] at this
  · refine ⟨n, Or.inr ?_⟩
    have := congrArg (zE e δ hδ) hn
    rwa [Equiv.apply_symm_apply, zE_iter e he δ hδ ρ hρ c0 hρp, Equiv.apply_symm_apply] at this

/-! ### An odd path rooted at its middle vertex -/

section Middle

/-- The signed position on a two-armed star: arm `0` positive, arm `1` negative. -/
def pos {L' : Fin 2 → ℕ} : StarV L' → ℤ
  | none => 0
  | some ⟨i, j⟩ => if i = 0 then (j : ℤ) + 1 else -((j : ℤ) + 1)

theorem adj_two {L' : Fin 2 → ℕ} (a b : StarV L') :
    starAdj a b ↔ (pos b = pos a + 1 ∨ pos a = pos b + 1) := by
  rcases a with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases b with _ | ⟨i', ⟨j', hj'⟩⟩
  · simp [starAdj, pos]
  · fin_cases i' <;> simp [starAdj, pos] <;> omega
  · fin_cases i <;> simp [starAdj, pos] <;> omega
  · fin_cases i <;> fin_cases i' <;> simp [starAdj, pos] <;> omega

theorem pos_injective {L' : Fin 2 → ℕ} : Function.Injective (pos (L' := L')) := by
  intro a b h
  rcases a with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases b with _ | ⟨i', ⟨j', hj'⟩⟩
  · rfl
  · fin_cases i' <;> simp [pos] at h <;> omega
  · fin_cases i <;> simp [pos] at h <;> omega
  · fin_cases i <;> fin_cases i' <;> simp [pos] at h <;> first | omega | (subst h; rfl)

theorem adj_one {L : Fin 1 → ℕ} (a b : StarV L) :
    starAdj a b ↔ (starDepth b = starDepth a + 1 ∨ starDepth a = starDepth b + 1) := by
  rcases a with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases b with _ | ⟨i', ⟨j', hj'⟩⟩
  · simp [starAdj, starDepth]
  · simp [starAdj, starDepth]
  · simp [starAdj, starDepth]
  · have : i = i' := Subsingleton.elim _ _
    subst this
    simp only [starAdj, starDepth, true_and]; omega

variable (h : ℕ)

/-- The two arms of the re-rooted path. -/
def Lmid : Fin 2 → ℕ := fun _ ↦ h - 1

/-- The vertex of the re-rooted path at a signed position. -/
def ofPos (p : ℤ) (hp : -(h : ℤ) ≤ p ∧ p ≤ h) : StarV (Lmid h) :=
  if h0 : p = 0 then none
  else if hpos : 0 < p then some ⟨0, ⟨(p - 1).toNat, by simp only [Lmid]; omega⟩⟩
  else some ⟨1, ⟨(-p - 1).toNat, by simp only [Lmid]; omega⟩⟩

theorem pos_ofPos (p : ℤ) (hp : -(h : ℤ) ≤ p ∧ p ≤ h) : pos (ofPos h p hp) = p := by
  unfold ofPos
  split_ifs with h0 hpos
  · simp [pos, h0]
  · simp [pos]; omega
  · simp [pos]; omega

theorem pos_bound (hh : 1 ≤ h) (v : StarV (Lmid h)) : -(h : ℤ) ≤ pos v ∧ pos v ≤ h := by
  rcases v with _ | ⟨i, ⟨j, hj⟩⟩
  · simp [pos]
  · have hj' : j < h - 1 + 1 := hj
    fin_cases i <;> simp [pos] <;> omega

variable (hh : 1 ≤ h) (L : Fin 1 → ℕ) (hL : L 0 = 2 * h - 1)

include hh hL in
/-- **The re-rooting isomorphism**: depth `d` goes to position `d - h`. -/
def midEquiv : StarV L ≃ StarV (Lmid h) where
  toFun v := ofPos h ((starDepth v : ℤ) - h) (by have := depth_le v; rw [hL] at this; omega)
  invFun w := ofDep L ((pos w + h).toNat) (by have := pos_bound h hh w; rw [hL]; omega)
  left_inv v := by
    apply depth_injective
    rw [starDepth_ofDep, pos_ofPos]; omega
  right_inv w := by
    apply pos_injective
    rw [pos_ofPos, starDepth_ofDep]; have := pos_bound h hh w; omega

theorem pos_midEquiv (v : StarV L) :
    pos (midEquiv h hh L hL v) = (starDepth v : ℤ) - h := by
  simp only [midEquiv, Equiv.coe_fn_mk]; exact pos_ofPos h _ _

include hh hL in
theorem midEquiv_adj (a b : StarV L) :
    (starTree L).G.Adj a b ↔ (starTree (Lmid h)).G.Adj (midEquiv h hh L hL a) (midEquiv h hh L hL b) := by
  change starAdj a b ↔ starAdj _ _
  rw [adj_one, adj_two, pos_midEquiv, pos_midEquiv]
  omega

theorem depth_eq_abs_pos (w : StarV (Lmid h)) : (starDepth w : ℤ) = |pos w| := by
  rcases w with _ | ⟨i, ⟨j, hj⟩⟩
  · simp [pos, starDepth]
  · fin_cases i
    · simp only [pos, starDepth, Fin.zero_eta, Fin.isValue, if_true]
      rw [abs_of_pos (by positivity)]; push_cast; ring
    · simp only [pos, starDepth, Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
      rw [abs_neg, abs_of_pos (by positivity)]; push_cast; ring

theorem cast_abs (a : ℤ) : ((|a| : ℤ) : ZMod 2) = (a : ZMod 2) := by
  rcases abs_choice a with h | h <;> rw [h]
  push_cast; exact ZMod.neg_eq_self_mod_two _

include hh hL in
theorem midEquiv_par (d : StarV L) :
    (starTree (Lmid h)).par (midEquiv h hh L hL d) = (starTree L).par d + ((h : ℤ) : ZMod 2) := by
  change ((starDepth _ : ℕ) : ZMod 2) = ((starDepth d : ℕ) : ZMod 2) + ((h : ℤ) : ZMod 2)
  have e1 := depth_eq_abs_pos h (midEquiv h hh L hL d)
  rw [pos_midEquiv] at e1
  have e2 := congrArg (fun z : ℤ ↦ (z : ZMod 2)) e1
  simp only [cast_abs] at e2
  push_cast at e2 ⊢
  rw [e2, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

end Middle

end ReRoot

end MultiplicativeBasisDeformations
