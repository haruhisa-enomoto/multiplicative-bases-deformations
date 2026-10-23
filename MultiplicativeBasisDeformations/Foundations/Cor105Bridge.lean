module

public import MultiplicativeBasisDeformations.Foundations.Bockstein
public import MultiplicativeBasisDeformations.Foundations.TransportFamily
public import MultiplicativeBasisDeformations.Foundations.GradedBasis

/-!
# Relative cochains of character `χ` and their coefficients

`integral-deformations.tex`: "all cochains are normalized relative to the vertex
identities and respect the categorical grading and the integer ray weights." A normalized
relative two-cochain of character `χ` on `Λ ≅ kP` is `Φ₂` of its coefficients (`realize`);
it is a coboundary exactly when its coefficients are `d₁` of coefficients (`coef_of_isCobdry`,
`isCobdry_of_coef`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (χ : L)

local notation:max "⌜" r "⌝" => Sys.rr S r

section Ring

variable (k : Type u) [CommRing k] [Nontrivial k]

/-! ### Coordinates of products -/

theorem repr_b_mul (u : R) (y : S.P.Lin k) (t : R) :
    (S.P.basis k).repr (S.P.b k u * y) t =
      ∑ s, (S.P.basis k).repr y s * (if S.P.mul u s = some t then 1 else 0) := by
  conv_lhs => rw [← (S.P.basis k).sum_repr y]
  rw [Finset.mul_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, Mult.basis_apply, Mult.b_mul]
  cases h : S.P.mul u s with
  | none => simp
  | some t' =>
    simp only [Option.elim_some, Mult.basis_repr_b, Option.some.injEq]

theorem repr_mul_b (v : R) (y : S.P.Lin k) (t : R) :
    (S.P.basis k).repr (y * S.P.b k v) t =
      ∑ s, (S.P.basis k).repr y s * (if S.P.mul s v = some t then 1 else 0) := by
  conv_lhs => rw [← (S.P.basis k).sum_repr y]
  rw [Finset.sum_mul, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul, Mult.basis_apply, Mult.b_mul]
  cases h : S.P.mul s v with
  | none => simp
  | some t' =>
    simp only [Option.elim_some, Mult.basis_repr_b, Option.some.injEq]

theorem sum_single_of_unique {f g : R → k} {s₀ : R} (h : ∀ s, g s ≠ 0 → s = s₀) :
    ∑ s, f s * g s = f s₀ * g s₀ := by
  rw [Finset.sum_eq_single s₀ (fun s _ hs ↦ by
    by_cases hg : g s = 0
    · rw [hg, mul_zero]
    · exact absurd (h s hg) hs) (fun h ↦ absurd (Finset.mem_univ _) h)]

theorem repr_e_mul (x : V) (y : S.P.Lin k) (t : R) :
    (S.P.basis k).repr (S.P.b k (S.P.e x) * y) t =
      if S.P.src t = x then (S.P.basis k).repr y t else 0 := by
  rw [repr_b_mul, sum_single_of_unique k (s₀ := t)]
  · split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd (by have := S.P.mul_src _ _ _ h1; rwa [S.P.src_e] at this) h2
    · exact absurd (by rw [← h2]; exact S.P.e_mul t) h1
    · rw [mul_zero]
  · intro s hs
    by_contra hne
    apply hs
    rw [if_neg]
    intro h
    have := S.P.e_mul s
    have hx : S.P.src s = x := by
      have := S.P.mul_mid _ _ _ h; rwa [S.P.tgt_e, eq_comm] at this
    rw [hx] at this
    rw [this] at h
    exact hne (Option.some_inj.1 h)

theorem repr_mul_e (y : S.P.Lin k) (x : V) (t : R) :
    (S.P.basis k).repr (y * S.P.b k (S.P.e x)) t =
      if S.P.tgt t = x then (S.P.basis k).repr y t else 0 := by
  rw [repr_mul_b, sum_single_of_unique k (s₀ := t)]
  · split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd (by have := S.P.mul_tgt _ _ _ h1; rwa [S.P.tgt_e] at this) h2
    · exact absurd (by rw [← h2]; exact S.P.mul_e t) h1
    · rw [mul_zero]
  · intro s hs
    by_contra hne
    apply hs
    rw [if_neg]
    intro h
    have := S.P.mul_e s
    have hx : S.P.tgt s = x := by
      have := S.P.mul_mid _ _ _ h; rwa [S.P.src_e] at this
    rw [hx] at this
    rw [this] at h
    exact hne (Option.some_inj.1 h)

/-! ### Coboundaries in coefficients -/

section CobdryRing

variable {χ}

open Classical in
theorem coef_left (y : S.P.Lin k) {u v t₀ : R} (hI : S.I2 χ (u, v)) (ht₀ : S.w2 χ u v = some t₀) :
    (S.P.basis k).repr (S.P.b k u * y) t₀ =
      if S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome then (S.P.basis k).repr y (S.succ χ v)
        else 0 := by
  classical
  obtain ⟨e1, e2, e3⟩ := (S.w2_eq_some χ).1 ht₀
  have huniq : ∀ s, S.P.mul u s = some t₀ → S.Shift χ v ∧ s = S.succ χ v := by
    intro s hs
    have h1 : S.P.src s = S.P.src v := by rw [← S.P.mul_mid _ _ _ hs]; exact hI.1
    have h2 : S.P.tgt s = S.P.tgt v := by rw [← S.P.mul_tgt _ _ _ hs, e2]
    have h3 : S.P.wt s = S.P.wt v + χ := by
      have := S.P.wt_mul _ _ _ hs; rw [e3, add_assoc] at this
      exact (add_left_cancel this).symm
    have hsh : S.Shift χ v := ⟨hI.2.2.1, s, h1, h2, h3⟩
    exact ⟨hsh, S.eq_succ χ hsh h1 h2 h3⟩
  rw [repr_b_mul]
  split_ifs with h
  · obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 h.2
    have htt : t' = t₀ := Option.some_inj.1 ((S.w2_of_mul_succ_right h.1 ht').symm.trans ht₀)
    subst htt
    rw [sum_single_of_unique k (s₀ := S.succ χ v), if_pos ht', mul_one]
    intro s hs
    have : S.P.mul u s = some t' := by by_contra hc; exact hs (if_neg hc)
    exact (huniq s this).2
  · refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [if_neg, mul_zero]
    intro hs
    obtain ⟨hsh, rfl⟩ := huniq s hs
    exact h ⟨hsh, by rw [hs]; rfl⟩

open Classical in
theorem coef_right (y : S.P.Lin k) {u v t₀ : R} (hI : S.I2 χ (u, v)) (ht₀ : S.w2 χ u v = some t₀) :
    (S.P.basis k).repr (y * S.P.b k v) t₀ =
      if S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome then (S.P.basis k).repr y (S.succ χ u)
        else 0 := by
  classical
  obtain ⟨e1, e2, e3⟩ := (S.w2_eq_some χ).1 ht₀
  have huniq : ∀ s, S.P.mul s v = some t₀ → S.Shift χ u ∧ s = S.succ χ u := by
    intro s hs
    have h1 : S.P.src s = S.P.src u := by rw [← S.P.mul_src _ _ _ hs, e1]
    have h2 : S.P.tgt s = S.P.tgt u := by rw [S.P.mul_mid _ _ _ hs]; exact hI.1.symm
    have h3 : S.P.wt s = S.P.wt u + χ := by
      have := S.P.wt_mul _ _ _ hs; rw [e3, add_right_comm] at this
      exact (add_right_cancel this).symm
    have hsh : S.Shift χ u := ⟨hI.2.1, s, h1, h2, h3⟩
    exact ⟨hsh, S.eq_succ χ hsh h1 h2 h3⟩
  rw [repr_mul_b]
  split_ifs with h
  · obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 h.2
    have htt : t' = t₀ := Option.some_inj.1 ((S.w2_of_mul_succ_left h.1 ht').symm.trans ht₀)
    subst htt
    rw [sum_single_of_unique k (s₀ := S.succ χ u), if_pos ht', mul_one]
    intro s hs
    have : S.P.mul s v = some t' := by by_contra hc; exact hs (if_neg hc)
    exact (huniq s this).2
  · refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [if_neg, mul_zero]
    intro hs
    obtain ⟨hsh, rfl⟩ := huniq s hs
    exact h ⟨hsh, by rw [hs]; rfl⟩

open Classical in
theorem coef_mid (H : S.P.Lin k →ₗ[k] S.P.Lin k) {u v t₀ : R} (hI : S.I2 χ (u, v))
    (ht₀ : S.w2 χ u v = some t₀) :
    (S.P.basis k).repr (H (S.P.b k u * S.P.b k v)) t₀ =
      match S.P.mul u v with
      | some t => if S.Shift χ t then (S.P.basis k).repr (H (S.P.b k t)) (S.succ χ t) else 0
      | none => 0 := by
  classical
  rw [Mult.b_mul]
  cases hm : S.P.mul u v with
  | none => simp
  | some t =>
    simp only [Option.elim_some]
    obtain ⟨e1, e2, e3⟩ := (S.w2_eq_some χ).1 ht₀
    have hp : ⌜u⌝ * ⌜v⌝ = ⌜t⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    have hsh : S.Shift χ t := ⟨S.prod_ne_e hI.2.1 hp, t₀, by rw [e1, S.P.mul_src _ _ _ hm],
      by rw [e2, S.P.mul_tgt _ _ _ hm], by rw [e3, S.P.wt_mul _ _ _ hm]⟩
    rw [if_pos hsh, Option.some_inj.1 (ht₀.symm.trans (S.w2_of_mul hm hsh))]

/-- The coefficients of a linear map on the shiftable rays. -/
def coef1 (H : S.P.Lin k →ₗ[k] S.P.Lin k) : S.C1 χ k := fun r ↦
  (S.P.basis k).repr (H (S.P.b k r.1)) (S.succ χ r.1)

/-- **A coboundary has coefficients `d₁` of coefficients.** -/
theorem coef_of_hcobdry (c : S.C2 χ k) (H : S.P.Lin k →ₗ[k] S.P.Lin k)
    (h : S.Φ2 χ k c = GExt.hcobdry H) : c = S.d1 χ k (S.coef1 k H) := by
  classical
  funext p
  obtain ⟨⟨u, v⟩, hI⟩ := p
  obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.1 hI.2.2.2
  have h1 : c ⟨(u, v), hI⟩ = (S.P.basis k).repr (S.P.b k u * H (S.P.b k v) -
      H (S.P.b k u * S.P.b k v) + H (S.P.b k u) * S.P.b k v) t₀ := by
    have := congrArg (fun φ ↦ (S.P.basis k).repr (φ (S.P.b k u) (S.P.b k v)) t₀) h
    simp only [Φ2_b, dif_pos hI, ht₀, vecW_some, map_smul, Finsupp.smul_apply, Mult.basis_repr_b,
      smul_eq_mul, GExt.hcobdry_apply] at this
    simpa using this
  rw [h1, map_add, map_sub, Finsupp.add_apply, Finsupp.sub_apply, S.coef_left k _ hI ht₀,
    S.coef_right k _ hI ht₀, S.coef_mid k H hI ht₀]
  change _ = S.d1raw χ k (S.coef1 k H) u v
  unfold d1raw
  congr 1

end CobdryRing

end Ring

variable (k : Type u) [Field k] [IsAlgClosed k]

/-! ### Realization of relative cochains of character `χ` -/

section Realize

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)

/-- The coefficients of a two-cochain on `Λ ≅ kP`: the coordinate of `φ(r, s)` at `w₂(r, s)`. -/
def coefOf (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) : S.C2 χ k := fun p ↦
  (S.P.basis k).repr (Θ.symm (φ (Θ (S.P.b k p.1.1)) (Θ (S.P.b k p.1.2))))
    ((S.w2 χ p.1.1 p.1.2).get p.2.2.2.2)

theorem basisΛ_repr (x : Λ) (t : R) :
    (S.basisΛ k Θ).repr x t = (S.P.basis k).repr (Θ.symm x) t := by
  rw [basisΛ, Module.Basis.map_repr]; rfl

theorem eq_smul_of_repr {z : S.P.Lin k} {t₀ : R}
    (h : ∀ t, (S.P.basis k).repr z t ≠ 0 → t = t₀) :
    z = (S.P.basis k).repr z t₀ • S.P.b k t₀ := by
  refine (S.P.basis k).ext_elem fun t ↦ ?_
  rw [map_smul, Finsupp.smul_apply, Mult.basis_repr_b, smul_eq_mul]
  by_cases ht : t₀ = t
  · subst ht; rw [if_pos rfl, mul_one]
  · rw [if_neg ht, mul_zero]
    by_contra hne
    exact ht (h t hne).symm

theorem eq_zero_of_repr {z : S.P.Lin k} (h : ∀ t, (S.P.basis k).repr z t = 0) : z = 0 :=
  (S.P.basis k).ext_elem fun t ↦ by rw [h t, map_zero, Finsupp.zero_apply]

/-- **A normalized relative two-cochain of character `χ` is `Φ₂` of its coefficients.** -/
theorem realize {G : LenGrading k Λ} {W : LatGrading k Λ L}
    (hW : ∀ r, W.IsHom (S.P.wt r) (Θ (S.P.b k r))) (Vx : LenGrading.Vertices G)
    (hVx : ∀ x, ∃ i, Vx.e i = Θ (S.P.b k (S.P.e x))) {φ : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (hr : LenGrading.IsRel₂ Vx φ) (hc : W.Char₂ χ φ) :
    φ = S.transp k Θ (S.Φ2 χ k (S.coefOf χ k Θ φ)) := by
  classical
  refine (S.basisΛ k Θ).ext fun u ↦ (S.basisΛ k Θ).ext fun v ↦ ?_
  rw [basisΛ_apply, basisΛ_apply, transp_apply, Θ.symm_apply_apply, Θ.symm_apply_apply, Φ2_b]
  set z := Θ.symm (φ (Θ (S.P.b k u)) (Θ (S.P.b k v))) with hz
  suffices hzz : z = if h : S.I2 χ (u, v) then S.coefOf χ k Θ φ ⟨(u, v), h⟩ •
      S.vecW k (S.w2 χ u v) else 0 by
    rw [← hzz, hz, Θ.apply_symm_apply]
  -- weight
  have hzw : ∀ t, (S.P.basis k).repr z t ≠ 0 → S.P.wt t = S.P.wt u + S.P.wt v + χ := by
    intro t ht
    by_contra hne
    apply ht
    rw [hz, ← basisΛ_repr]
    exact W.repr_eq_zero_of_isHom (S.basisΛ k Θ) S.P.wt (fun r ↦ by rw [basisΛ_apply]; exact hW r)
      (hc _ _ _ _ (hW u) (hW v)) hne
  -- endpoints
  have hzs : ∀ t, (S.P.basis k).repr z t ≠ 0 → S.P.src t = S.P.src u := by
    intro t ht
    obtain ⟨i, hi⟩ := hVx (S.P.src u)
    have h1 := hr.left i (Θ (S.P.b k u)) (Θ (S.P.b k v))
    rw [hi, ← map_mul, Mult.b_e_mul, if_pos rfl] at h1
    have h2 : z = S.P.b k (S.P.e (S.P.src u)) * z := by
      have := congrArg Θ.symm h1
      rwa [map_mul, Θ.symm_apply_apply, ← hz] at this
    rw [h2, repr_e_mul] at ht
    by_contra hne
    exact ht (if_neg hne)
  have hzt : ∀ t, (S.P.basis k).repr z t ≠ 0 → S.P.tgt t = S.P.tgt v := by
    intro t ht
    obtain ⟨i, hi⟩ := hVx (S.P.tgt v)
    have h1 := hr.right i (Θ (S.P.b k u)) (Θ (S.P.b k v))
    rw [hi, ← map_mul, Mult.b_mul_e, if_pos rfl] at h1
    have h2 : z = z * S.P.b k (S.P.e (S.P.tgt v)) := by
      have := congrArg Θ.symm h1
      rwa [map_mul, Θ.symm_apply_apply, ← hz] at this
    rw [h2, repr_mul_e] at ht
    by_contra hne
    exact ht (if_neg hne)
  have hzw2 : ∀ t, (S.P.basis k).repr z t ≠ 0 → S.w2 χ u v = some t := fun t ht ↦
    (S.w2_eq_some χ).2 ⟨hzs t ht, hzt t ht, hzw t ht⟩
  split_ifs with hI
  · obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.1 hI.2.2.2
    have hc0 : S.coefOf χ k Θ φ ⟨(u, v), hI⟩ = (S.P.basis k).repr z t₀ := by
      simp only [coefOf, ht₀, Option.get_some]; rfl
    rw [hc0, ht₀, vecW_some]
    exact S.eq_smul_of_repr k fun t ht ↦ Option.some_inj.1 ((hzw2 t ht).symm.trans ht₀)
  · unfold I2 at hI
    simp only [not_and_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
      at hI
    rcases hI with hmid | hu | hv | hw
    · obtain ⟨i, hi⟩ := hVx (S.P.tgt u)
      have h1 := hr.mid i (Θ (S.P.b k u)) (Θ (S.P.b k v))
      rw [hi, ← map_mul, ← map_mul, Mult.b_mul_e, if_pos rfl, Mult.b_e_mul, if_neg hmid,
        map_zero, map_zero] at h1
      rw [hz, h1, map_zero]
    · obtain ⟨i, hi⟩ := hVx (S.P.src u)
      have h1 := hr.unitL i (Θ (S.P.b k v))
      rw [hi, ← not_not.1 hu] at h1
      rw [hz, h1, map_zero]
    · obtain ⟨i, hi⟩ := hVx (S.P.src v)
      have h1 := hr.unitR i (Θ (S.P.b k u))
      rw [hi, ← not_not.1 hv] at h1
      rw [hz, h1, map_zero]
    · refine S.eq_zero_of_repr k fun t ↦ ?_
      by_contra ht
      rw [hzw2 t ht] at hw
      exact absurd hw (by simp)

end Realize

section Cobdry

variable {χ}

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)

/-- **A coboundary on `Λ` has coefficients `d₁` of coefficients.** -/
theorem coef_of_isCobdry {G : LenGrading k Λ} {q : ℕ} (c : S.C2 χ k)
    (h : IsCobdry k G q (S.transp k Θ (S.Φ2 χ k c))) : ∃ f, c = S.d1 χ k f := by
  obtain ⟨H, -, hH⟩ := h
  set H' : S.P.Lin k →ₗ[k] S.P.Lin k := Θ.symm.toLinearMap ∘ₗ H ∘ₗ Θ.toLinearMap
  refine ⟨S.coef1 k H', S.coef_of_hcobdry k c H' ?_⟩
  ext a b
  have := congrArg (fun φ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ Θ.symm (φ (Θ a) (Θ b))) hH
  simp only [transp_apply, Θ.symm_apply_apply, LenGrading.cobdry_apply] at this
  rw [this, GExt.hcobdry_apply]
  simp [H', map_add, map_sub, map_mul]

theorem transp_hcobdry (h : S.P.Lin k →ₗ[k] S.P.Lin k) :
    S.transp k Θ (GExt.hcobdry h) =
      LenGrading.cobdry k (Θ.toLinearMap ∘ₗ h ∘ₗ Θ.symm.toLinearMap) := by
  ext a b
  simp [transp_apply, GExt.hcobdry_apply, LenGrading.cobdry_apply, map_add, map_sub, map_mul]

/-- **`d₁` of coefficients is a coboundary of degree `deg χ` on `Λ`.** -/
theorem isCobdry_of_d1 {G : LenGrading k Λ}
    (hG : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (Θ (S.P.b k r))) (hχ : 0 ≤ S.P.deg χ)
    (f : S.C1 χ k) : IsCobdry k G (S.P.deg χ).toNat (S.transp k Θ (S.Φ2 χ k (S.d1 χ k f))) := by
  classical
  rw [← S.hcobdry_Φ1 χ k f, transp_hcobdry]
  refine ⟨_, fun d a ha ↦ ?_, rfl⟩
  have hβ : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (S.basisΛ k Θ r) := fun r ↦ by
    rw [basisΛ_apply]; exact hG r
  have ha' := (S.basisΛ k Θ).sum_repr a
  rw [← ha', map_sum]
  refine LenGrading.isHom_sum G _ _ fun r _ ↦ ?_
  rw [map_smul]
  by_cases hr : (S.P.deg (S.P.wt r)).toNat = d
  · refine G.isHom_smul' _ ?_
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, basisΛ_apply,
      Θ.symm_apply_apply, Φ1_b]
    split_ifs with hs
    · rw [map_smul]
      refine G.isHom_smul' _ ?_
      have h1 := hG (S.succ χ r)
      have e : (S.P.deg (S.P.wt (S.succ χ r))).toNat = d + (S.P.deg χ).toNat := by
        rw [(S.succ_spec χ hs).2.2, map_add, ← hr]
        have := S.P.deg_nonneg r
        omega
      rwa [e] at h1
    · rw [map_zero]; exact G.isHom_zero' _
  · rw [G.repr_eq_zero_of_isHom (S.basisΛ k Θ) _ hβ ha hr, zero_smul]
    exact G.isHom_zero' _

end Cobdry

/-! ### Corollary 10.5 on `Λ ≅ kP`, given Proposition 10.3 -/

section Cor

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)

theorem isHCocycle_of_transp {μ : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k}
    (h : LenGrading.IsCocycle₂ (S.transp k Θ μ)) : GExt.IsHCocycle μ := by
  intro a b c
  have := congrArg Θ.symm (h (Θ a) (Θ b) (Θ c))
  simpa [transp_apply, map_mul, map_add, map_sub] using this

open Classical in
/-- The indicator coefficients of a supported coefficient cochain. -/
def indOf (u : S.C2 χ k) (x y : R) : k := if h : S.I2 χ (x, y) then u ⟨(x, y), h⟩ else 0

theorem coch_indOf (hfin : IsRepresentationFinite k (S.P.Lin k)) {u : S.C2 χ k}
    (hu : u ∈ S.Usub χ k) : S.coch k (S.indOf χ k u) = S.Φ2 χ k u := by
  classical
  refine (S.P.basis k).ext fun x ↦ (S.P.basis k).ext fun y ↦ ?_
  simp only [Mult.basis_apply, coch_b, Φ2_b, indOf]
  split_ifs with hI
  · by_cases hU : S.UC χ (x, y)
    · obtain ⟨-, t, ht, he⟩ := hU
      rw [he, ht, vecM_rr, vecW_some]
    · rw [hu ⟨(x, y), hI⟩ hU, zero_smul, zero_smul]
  · rw [zero_smul]

/-- **Corollary 10.5** (`cor:zero-supported-coverage`) on `Λ ≅ kP`, given Proposition 10.3. -/
theorem cor105_of_IStar [CharP k 2] (hfin : IsRepresentationFinite k (S.P.Lin k))
    (hχ : 0 < S.P.deg χ) (hprim : Prim χ)
    (hWl : ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r)
    (hI : S.IStar χ) {G : LenGrading k Λ} {W : LatGrading k Λ L}
    (hG : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (Θ (S.P.b k r)))
    (hW : ∀ r, W.IsHom (S.P.wt r) (Θ (S.P.b k r))) (Vx : LenGrading.Vertices G)
    (hVx : ∀ x, ∃ i, Vx.e i = Θ (S.P.b k (S.P.e x))) {q : ℕ} {φ : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (hr : LenGrading.IsRel₂ Vx φ) (hd : LenGrading.HasDeg₂ G q φ)
    (hcoc : LenGrading.IsCocycle₂ φ) (hc : W.Char₂ χ φ) (hnc : ¬ IsCobdry k G q φ) :
    ∃ a : R → R → k, S.EdgeOK k a ∧
      (∀ z : R × R, a z.1 z.2 ≠ 0 → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ) ∧
      ¬ IsCobdry k G (S.P.deg χ).toNat (S.transp k Θ (S.coch k a)) := by
  classical
  set c := S.coefOf χ k Θ φ
  have hφ : φ = S.transp k Θ (S.Φ2 χ k c) := S.realize χ k Θ hW Vx hVx hr hc
  have hc2 : S.d2L χ k c = 0 := by
    have h := (S.isHCocycle_Φ2_iff χ k c).1 (S.isHCocycle_of_transp k Θ (hφ ▸ hcoc))
    funext t; exact h _ _ _ t.2
  have hφ0 : φ ≠ 0 := by rintro rfl; exact hnc (isCobdry_zero k G q)
  have hq : S.P.deg χ = q := S.deg_eq_of_ne_zero k Θ hG hW hφ0 hd hc
  have hnc' : ¬ ∃ f, c = S.d1 χ k f := by
    rintro ⟨f, hf⟩
    apply hnc
    have := S.isCobdry_of_d1 k Θ hG hχ.le f
    rw [← hf, ← hφ, hq, Int.toNat_natCast] at this
    exact this
  obtain ⟨u, hu, hu2, hun⟩ := S.cor105_coeff χ k hfin hχ hprim hWl hI c hc2 hnc'
  have hcoch := S.coch_indOf χ k hfin hu
  refine ⟨S.indOf χ k u, ?_, ?_, ?_⟩
  · refine (S.coch_isCocycle_iff k k hfin _).1 ?_
    rw [hcoch]
    intro a b c'
    exact (S.isHCocycle_Φ2_iff χ k u).2 (fun x y z hw ↦ congrFun hu2 ⟨(x, y, z), hw⟩) a b c'
  · rintro ⟨x, y⟩ ha -
    simp only [indOf] at ha
    split_ifs at ha with hI2
    swap
    · exact absurd rfl ha
    by_cases hU : S.UC χ (x, y)
    · obtain ⟨-, t, ht, he⟩ := hU
      obtain ⟨-, -, e3⟩ := (S.w2_eq_some χ).1 ht
      simp only [pairChar, he, wtM_rr, e3]
      abel
    · exact absurd (hu ⟨(x, y), hI2⟩ hU) ha
  · intro h
    rw [hcoch] at h
    exact hun (S.coef_of_isCobdry k Θ u h)

end Cor

end Sys

end RaySys

end MultiplicativeBasisDeformations
