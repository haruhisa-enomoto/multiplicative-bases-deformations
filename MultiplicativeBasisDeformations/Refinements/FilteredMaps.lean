module

public import MultiplicativeBasisDeformations.Refinements.LiftedRadical

/-!
# Filtered maps with surjective or injective leading terms (toward Corollary 12.1)

Linear maps between finite graded spaces are filtered by the degrees they raise (`OrderGe`).
A filtered map whose leading term is surjective (injective) is itself surjective (injective),
and has a filtered right inverse; a graded map killed by the leading term of a filtered map
with surjective leading term corrects to a filtered map killed by the map itself
(`exists_kernel_lift`). These are the finite-filtration arguments of
`deformation-refinements.tex` ("graded surjectivity supplies `p_d`... The finite
filtration makes the process terminate").
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ] {GΛ : GAlg (R := k) Λ}
  {M N U : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup U] [Module k U] {MM : GMod GΛ M} {NN : GMod GΛ N} {UU : GMod GΛ U}

/-- The filtration level `≥ t`: all components below `t` vanish. -/
def ZGr.GeAt (g : ZGr (R := k) M) (t : ℤ) (m : M) : Prop := ∀ e, e < t → g.proj e m = 0

namespace ZGr

variable (g : ZGr (R := k) M)

theorem geAt_zero (t : ℤ) : g.GeAt t 0 := fun _ _ ↦ map_zero _

variable {g}

theorem GeAt.add {t : ℤ} {m m' : M} (h : g.GeAt t m) (h' : g.GeAt t m') : g.GeAt t (m + m') :=
  fun e he ↦ by rw [map_add, h e he, h' e he, add_zero]

theorem GeAt.neg {t : ℤ} {m : M} (h : g.GeAt t m) : g.GeAt t (-m) :=
  fun e he ↦ by rw [map_neg, h e he, neg_zero]

theorem GeAt.sub {t : ℤ} {m m' : M} (h : g.GeAt t m) (h' : g.GeAt t m') : g.GeAt t (m - m') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem GeAt.smul {t : ℤ} (c : k) {m : M} (h : g.GeAt t m) : g.GeAt t (c • m) :=
  fun e he ↦ by rw [map_smul, h e he, smul_zero]

theorem GeAt.mono {t t' : ℤ} {m : M} (h : g.GeAt t m) (ht : t' ≤ t) : g.GeAt t' m :=
  fun e he ↦ h e (by omega)

theorem geAt_of_isHom {p t : ℤ} {m : M} (hm : g.IsHom p m) (ht : t ≤ p) : g.GeAt t m :=
  fun e he ↦ by rw [g.proj_of_isHom hm, if_neg (by omega)]

theorem eq_zero_of_geAt {t : ℤ} {m : M} (h : g.GeAt t m) (ht : (degBound g : ℤ) < t) : m = 0 := by
  rw [g.sum m]
  refine Finset.sum_eq_zero fun p hp ↦ h p ?_
  have := le_degBound hp
  rw [abs_le] at this
  omega

variable (g) in
theorem geAt_bot (m : M) : g.GeAt (-(degBound g : ℤ)) m := fun e he ↦ by
  by_cases hp : e ∈ g.supp
  · have := le_degBound hp
    rw [abs_le] at this
    omega
  · rw [g.proj_out e hp]; rfl

theorem GeAt.sub_proj {t : ℤ} {m : M} (h : g.GeAt t m) : g.GeAt (t + 1) (m - g.proj t m) :=
  fun e he ↦ by
    rw [map_sub, g.proj_proj]
    rcases lt_or_eq_of_le (show e ≤ t by omega) with h' | rfl
    · rw [if_neg (by omega), h e h', sub_zero]
    · rw [if_pos rfl, sub_self]

/-- The degree-`r` component commutes with the projections. -/
theorem comp_proj (gX : ZGr (R := k) M) (gY : ZGr (R := k) N) (r : ℤ) (u : M →ₗ[k] N) (d : ℤ)
    (m : M) : ZGr.comp gX gY r u (gX.proj d m) = gY.proj (d + r) (ZGr.comp gX gY r u m) := by
  classical
  rw [ZGr.comp_hom gX gY u (gX.isHom_proj d m)]
  simp only [ZGr.comp, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, gY.proj_proj]
  by_cases hd : d ∈ gX.supp
  · rw [Finset.sum_eq_single d]
    · rw [if_pos rfl]
    · intro p _ hp; rw [if_neg (by omega)]
    · intro h; exact absurd hd h
  · rw [gX.proj_out d hd, LinearMap.zero_apply, map_zero, map_zero]
    refine (Finset.sum_eq_zero fun p hp ↦ ?_).symm
    rw [if_neg (by rintro h; exact hd (by rwa [show p = d by omega] at hp))]

end ZGr

/-! ### Filtration levels and filtered maps -/

theorem OrderGe.geAt {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g) {t : ℤ} {m : M}
    (hm : MM.gr.GeAt t m) : NN.gr.GeAt (t + r) (g m) := by
  intro e he
  rw [MM.gr.sum m, map_sum, map_sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  by_cases hp : p < t
  · rw [hm p hp, map_zero, map_zero]
  · exact hg p _ (MM.gr.isHom_proj p m) e (by omega)

theorem OrderGe.sub_comp_geAt {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g) {p : ℤ} {m : M}
    (hm : MM.gr.IsHom p m) : NN.gr.GeAt (p + r + 1) (g m - ZGr.comp MM.gr NN.gr r g m) := by
  intro e he
  rw [map_sub, ZGr.comp_hom _ _ _ hm, NN.gr.proj_proj]
  rcases lt_or_eq_of_le (show e ≤ p + r by omega) with h | rfl
  · rw [hg p m hm e h, if_neg (by omega), sub_zero]
  · rw [if_pos rfl, sub_self]

theorem OrderGe.sub_comp {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g) :
    OrderGe MM NN (r + 1) (g - ZGr.comp MM.gr NN.gr r g) := by
  intro p m hm e he
  exact hg.sub_comp_geAt hm e (by omega)

theorem orderGe_comp (r : ℤ) (g : M →ₗ[k] N) :
    OrderGe MM NN r (ZGr.comp MM.gr NN.gr r g) := by
  intro p m hm e he
  rw [ZGr.comp_hom _ _ _ hm, NN.gr.proj_proj, if_neg (by omega)]

/-- **A filtered map with surjective leading term is surjective.** -/
theorem surjective_of_lead {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g)
    (hlead : Function.Surjective (ZGr.comp MM.gr NN.gr r g)) : Function.Surjective g := by
  have key : ∀ K : ℕ, ∀ n : N, NN.gr.GeAt ((degBound NN.gr : ℤ) + 1 - K) n →
      n ∈ LinearMap.range g := by
    intro K
    induction K with
    | zero =>
      intro n hn
      rw [NN.gr.eq_zero_of_geAt hn (by push_cast; omega)]
      exact zero_mem _
    | succ K ih =>
      intro n hn
      set t : ℤ := (degBound NN.gr : ℤ) + 1 - (K + 1) with ht
      obtain ⟨m, hm⟩ := hlead (NN.gr.proj t n)
      set m' := MM.gr.proj (t - r) m
      have hcm : ZGr.comp MM.gr NN.gr r g m' = NN.gr.proj t n := by
        rw [ZGr.comp_proj, hm, NN.gr.proj_proj, show t - r + r = t by ring, if_pos rfl]
      have hrest : NN.gr.GeAt ((degBound NN.gr : ℤ) + 1 - K) (n - g m') := by
        intro e he
        rcases lt_or_eq_of_le (show e ≤ t by push_cast at he; omega) with h | h
        · have h2 := hg.geAt (MM.gr.geAt_of_isHom (MM.gr.isHom_proj (t - r) m) le_rfl) e
            (by omega)
          rw [map_sub, hn e (by push_cast; omega), h2, sub_zero]
        · have h3 : NN.gr.proj t (g m') = ZGr.comp MM.gr NN.gr r g m' := by
            rw [ZGr.comp_hom _ _ _ (MM.gr.isHom_proj (t - r) m), show t - r + r = t by ring]
          rw [h, map_sub, h3, hcm, sub_self]
      obtain ⟨u, hu⟩ := ih _ hrest
      exact ⟨m' + u, by rw [map_add, hu]; abel⟩
  intro n
  exact key (2 * degBound NN.gr + 1) n ((NN.gr.geAt_bot n).mono (by push_cast; omega))

/-- **A filtered map with injective leading term is injective.** -/
theorem injective_of_lead {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g)
    (hinj : Function.Injective (ZGr.comp MM.gr NN.gr r g)) : Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  rw [Submodule.mem_bot]
  have key : ∀ K : ℕ, MM.gr.GeAt (-(degBound MM.gr : ℤ) + K) m := by
    intro K
    induction K with
    | zero => simpa using MM.gr.geAt_bot m
    | succ K ih =>
      set t : ℤ := -(degBound MM.gr : ℤ) + K
      have h0 : MM.gr.proj t m = 0 := by
        apply hinj
        rw [map_zero, ZGr.comp_hom _ _ _ (MM.gr.isHom_proj t m)]
        have h2 := hg.geAt ih.sub_proj (t + r) (by omega)
        rw [map_sub, hm, zero_sub, map_neg, neg_eq_zero] at h2
        exact h2
      intro e he
      push_cast at he
      rcases lt_or_eq_of_le (show e ≤ t by omega) with h | rfl
      · exact ih e h
      · exact h0
  exact MM.gr.eq_zero_of_geAt (key (2 * degBound MM.gr + 1)) (by push_cast; omega)

theorem one_add_mul_geom {R : Type*} [Ring R] (x : R) (n : ℕ) :
    (1 + x) * ∑ j ∈ Finset.range n, (-x) ^ j = 1 - (-x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : x * (-x) ^ n = (-x) ^ n * x := ((Commute.refl x).neg_right.pow_right n).eq
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ, add_mul, one_mul, hc, mul_neg]
    abel

/-- **A filtered right inverse** of a filtered map with surjective leading term. -/
theorem exists_section {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g)
    (hlead : Function.Surjective (ZGr.comp MM.gr NN.gr r g)) :
    ∃ s : N →ₗ[k] M, g ∘ₗ s = LinearMap.id ∧ OrderGe NN MM (-r) s := by
  classical
  set cg := ZGr.comp MM.gr NN.gr r g
  obtain ⟨s₁, hs₁⟩ := cg.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hlead)
  set s₀ : N →ₗ[k] M := ∑ e ∈ NN.gr.supp, MM.gr.proj (e - r) ∘ₗ s₁ ∘ₗ NN.gr.proj e
  have hs₀ : ∀ e n, NN.gr.IsHom e n → s₀ n = MM.gr.proj (e - r) (s₁ n) := by
    intro e n hn
    simp only [s₀, LinearMap.sum_apply, LinearMap.comp_apply, NN.gr.proj_of_isHom hn]
    by_cases he : e ∈ NN.gr.supp
    · rw [Finset.sum_eq_single e (fun e' _ he' ↦ by rw [if_neg (Ne.symm he'), map_zero, map_zero])
        (fun h ↦ absurd he h), if_pos rfl]
    · rw [NN.gr.eq_zero_of_isHom_out hn he]; simp
  have hcs₀ : cg ∘ₗ s₀ = LinearMap.id := by
    refine NN.gr.ext_of_hom fun e n hn ↦ ?_
    rw [LinearMap.comp_apply, hs₀ e n hn, ZGr.comp_proj, show e - r + r = e by ring,
      ← LinearMap.comp_apply cg s₁, hs₁]
    exact hn
  have hos₀ : OrderGe NN MM (-r) s₀ := by
    intro e n hn d hd
    rw [hs₀ e n hn, MM.gr.proj_proj, if_neg (by omega)]
  set E : N →ₗ[k] N := (g - cg) ∘ₗ s₀
  have hE : OrderGe NN NN 1 E := by
    have := hos₀.comp hg.sub_comp
    rwa [show -r + (r + 1) = 1 by ring] at this
  have hgs₀ : g ∘ₗ s₀ = LinearMap.id + E := by
    rw [← hcs₀]; ext n; simp [E]
  set K := 2 * degBound NN.gr + 1
  have hEK : E ^ K = 0 := (hE.raisesBy.pow K).eq_zero (by push_cast; omega)
  set u : N →ₗ[k] N := ∑ j ∈ Finset.range K, (-E) ^ j
  have hu : (LinearMap.id + E) ∘ₗ u = LinearMap.id := by
    change (1 + E) * u = 1
    rw [one_add_mul_geom, neg_pow, hEK, mul_zero, sub_zero]
  have hou : OrderGe NN NN 0 u := by
    simp only [u]
    refine Finset.sum_induction _ (OrderGe NN NN 0) (fun a b ha hb ↦ ha.add hb)
      (OrderGe.zero 0) fun j _ ↦ ?_
    have h1 : OrderGe NN NN 1 (-E) := by
      have := hE.smul (-1 : k); rwa [neg_one_smul] at this
    exact OrderGe.mono (MM := NN) (NN := NN) (h1.raisesBy.pow j) (by omega)
  refine ⟨s₀ ∘ₗ u, ?_, ?_⟩
  · rw [← LinearMap.comp_assoc, hgs₀, hu]
  · have := hou.comp hos₀
    rwa [zero_add] at this

/-- **Correcting a graded map into the kernel**: if the leading term of `g` is surjective and kills
the graded map `ι₁`, a filtered correction of `ι₁` is killed by `g`. -/
theorem exists_kernel_lift {r r' : ℤ} {g : U →ₗ[k] N} (hg : OrderGe UU NN r g)
    (hlead : Function.Surjective (ZGr.comp UU.gr NN.gr r g)) {ι₁ : M →ₗ[k] U}
    (hι₁ : ∀ p m, MM.gr.IsHom p m → UU.gr.IsHom (p + r') (ι₁ m))
    (hz : ZGr.comp UU.gr NN.gr r g ∘ₗ ι₁ = 0) :
    ∃ ι : M →ₗ[k] U, g ∘ₗ ι = 0 ∧ OrderGe MM UU r' ι ∧ ZGr.comp MM.gr UU.gr r' ι = ι₁ := by
  obtain ⟨s, hs, hos⟩ := exists_section hg hlead
  have hoι₁ : OrderGe MM UU r' ι₁ := by
    intro p m hm e he
    rw [UU.gr.proj_of_isHom (hι₁ p m hm), if_neg (by omega)]
  have hgι : OrderGe MM NN (r' + (r + 1)) (g ∘ₗ ι₁) := by
    have h := hoι₁.comp hg.sub_comp
    have e : g ∘ₗ ι₁ = (g - ZGr.comp UU.gr NN.gr r g) ∘ₗ ι₁ := by
      rw [LinearMap.sub_comp, hz, sub_zero]
    rw [e]; exact h
  have hc : OrderGe MM UU (r' + 1) (s ∘ₗ g ∘ₗ ι₁) := by
    have := hgι.comp hos
    rwa [show r' + (r + 1) + -r = r' + 1 by ring] at this
  have hc' : OrderGe MM UU r' (s ∘ₗ g ∘ₗ ι₁) := hc.mono (by omega)
  have esub : ι₁ - s ∘ₗ g ∘ₗ ι₁ = ι₁ + (-1 : k) • (s ∘ₗ g ∘ₗ ι₁) := by
    rw [neg_one_smul, sub_eq_add_neg]
  refine ⟨ι₁ - s ∘ₗ g ∘ₗ ι₁, ?_, by rw [esub]; exact hoι₁.add (hc'.smul (-1)), ?_⟩
  · rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, hs, LinearMap.id_comp, sub_self]
  · refine MM.gr.ext_of_hom fun p m hm ↦ ?_
    rw [ZGr.comp_hom _ _ _ hm, LinearMap.sub_apply, map_sub, hc p m hm (p + r') (by omega),
      sub_zero, UU.gr.proj_of_isHom (hι₁ p m hm), if_pos rfl]

end GExt

end MultiplicativeBasisDeformations
