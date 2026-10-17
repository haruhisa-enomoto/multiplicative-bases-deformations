import MultiplicativeBasisDeformations.Foundations.SquareZero
import MultiplicativeBasisDeformations.Foundations.WeightExt
import MultiplicativeBasisDeformations.Foundations.WeightExtGroup

/-!
# Lemma 6.6, the additional gradings

`lem:square-zero-selected-lifts` (`positive-deformations.tex:339–355`), last sentence: "If `Λ` and
the `M_i` carry an additional grading by an abelian group, preserved by the multiplication and the
actions, and `μ` is homogeneous for it, then all these choices may be made homogeneous for this
grading."

For a grading by an arbitrary abelian group `Γ` (`GrΓ`, gradings of the modules compatible with
the actions; `exists_actLiftΓ`, `ActLift.exists_isoΓ`, `exists_mapLiftΓ`, through
`WeightExtGroup.lean`), and also for finitely many additional `ℤ`-gradings (`GΛw i`, `MMw i`, `NNw i`; e.g. the coordinates of the
integer weights of Section 7), compatible with the actions and the internal degree as in
`WeightExt.lean`, and `μ` of weight `χ i` for each: the lifted actions can be chosen of weight `χ`
(`exists_actLiftW`), two such lifts differ by a coordinate change of weight `χ`
(`ActLift.exists_isoW`), and a map of weight `ω` lifts with correction of weight `ω + χ`
(`exists_mapLiftW`). The corrections are the weight components of `WeightExt.lean`
(`extVanish_weights1`, `extVanish_weights0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {MM : GMod GΛ M} {NN : GMod GΛ N}
  {r : ℕ} {GΛw : Fin r → GAlg (R := R) Λ} (MMw : ∀ i, GMod (GΛw i) M) (NNw : ∀ i, GMod (GΛw i) N)
  (hMa : ∀ i, (MMw i).act = MM.act) (hNa : ∀ i, (NNw i).act = NN.act)
  (hΛ : ∀ i v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p ((GΛw i).gr.proj v a))
  (hMp : ∀ i u p m, MM.gr.IsHom p m → MM.gr.IsHom p ((MMw i).gr.proj u m))
  (hNp : ∀ i x p n, NN.gr.IsHom p n → NN.gr.IsHom p ((NNw i).gr.proj x n))
  (hΛw : ∀ i j v p a, (GΛw j).gr.IsHom p a → (GΛw j).gr.IsHom p ((GΛw i).gr.proj v a))
  (hMw : ∀ i j u p m, (MMw j).gr.IsHom p m → (MMw j).gr.IsHom p ((MMw i).gr.proj u m))
  (hNw : ∀ i j x p n, (NNw j).gr.IsHom p n → (NNw j).gr.IsHom p ((NNw i).gr.proj x n))
  {μ : Λ →ₗ[R] Λ →ₗ[R] Λ}

/-- The degree of a weight-good one-cochain on homogeneous inputs. -/
theorem Good.one_deg {GΛ' : GAlg (R := R) Λ} {MM' : GMod GΛ' M} {NN' : GMod GΛ' N} {t : ℤ}
    {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM' NN' 1 t F) {u v : ℤ} {m : M} {a : Λ}
    (hm : MM'.gr.IsHom u m) (ha : GΛ'.gr.IsHom v a) :
    NN'.gr.IsHom (u + v + t) (F (single a) m) := by
  have := hF.deg (single a) (fun _ ↦ v) u m (fun i hi ↦ by
    obtain rfl : i = 0 := by omega
    simpa [single, Bar.cons] using ha) hm
  simpa using this

include hMa in
theorem muCochain_goodW {χ : Fin r → ℤ} (hχ : ∀ i, HDeg (GΛw i) μ (χ i)) (i : Fin r) :
    Good (MMw i) (MMw i) 2 (χ i) (muCochain μ MM) := by
  have e : muCochain μ MM = muCochain μ (MMw i) := by
    funext a; ext m; rw [muCochain_apply, muCochain_apply, hMa i]
  rw [e]; exact muCochain_good μ (hχ i) (MMw i)

include hMa hΛ hMp hΛw hMw in
/-- **Lifted actions of weight `χ`**. -/
theorem exists_actLiftW {q : ℤ} (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ)
    (h : ExtVanish MM MM 1 q) {χ : Fin r → ℤ} (hχ : ∀ i, HDeg (GΛw i) μ (χ i)) :
    ∃ L : ActLift μ q MM, ∀ i, Good (MMw i) (MMw i) 1 (χ i) L.ν := by
  obtain ⟨H, hH, hHw, hd⟩ := extVanish_weights1 (MM := MM) (NN := MM) MMw MMw hMa hMa hΛ hMp hMp
    hΛw hMw hMw h χ (muCochain μ MM) (muCochain_good μ hq MM) (muCochain_goodW MMw hMa hχ)
    (muCochain_d μ hμ MM)
  exact ⟨⟨H, hH, hd⟩, hHw⟩

/-- A lifted action of weight `χ` raises the weight by `χ`. -/
theorem ActLift.act_degW {q : ℤ} (L : ActLift μ q MM) {χ : Fin r → ℤ}
    (hL : ∀ i, Good (MMw i) (MMw i) 1 (χ i) L.ν) (i : Fin r) {u v : ℤ} {m : M} {a : Λ}
    (hm : (MMw i).gr.IsHom u m) (ha : (GΛw i).gr.IsHom v a) :
    (MMw i).gr.IsHom (u + v + χ i) (L.act m a) :=
  (hL i).one_deg hm ha

include hMa hMp hMw in
/-- **Uniqueness of weight-`χ` lifts** up to a coordinate change `1 + εh` of degree `q` and
weight `χ`. -/
theorem ActLift.exists_isoW {q : ℤ} (L L' : ActLift μ q MM) {χ : Fin r → ℤ}
    (hL : ∀ i, Good (MMw i) (MMw i) 1 (χ i) L.ν) (hL' : ∀ i, Good (MMw i) (MMw i) 1 (χ i) L'.ν)
    (h : ExtVanish MM MM 0 q) :
    ∃ φ : M →ₗ[R] M, (∀ p m, MM.gr.IsHom p m → MM.gr.IsHom (p + q) (φ m)) ∧
      (∀ i u m, (MMw i).gr.IsHom u m → (MMw i).gr.IsHom (u + χ i) (φ m)) ∧
      ∀ m a, L'.act m a - L.act m a = φ (MM.act m a) - MM.act (φ m) a := by
  have hg : Good MM MM (0 + 1) q (L'.ν - L.ν) := by
    have := L'.good.add' (L.good.zsmul' (-1))
    simpa [sub_eq_add_neg] using this
  have hgw : ∀ i, Good (MMw i) (MMw i) 1 (χ i) (L'.ν - L.ν) := fun i ↦ by
    have := (hL' i).add' ((hL i).zsmul' (-1))
    simpa [sub_eq_add_neg] using this
  obtain ⟨H, hH, hHw, hd⟩ := extVanish_weights0 (MM := MM) (NN := MM) MMw MMw hMa hMa hMp hMp
    hMw hMw h χ (L'.ν - L.ν) hg hgw (by rw [map_sub, L'.eq, L.eq, sub_self])
  refine ⟨H (fun _ ↦ 0), fun p m hm ↦ ?_, fun i u m hm ↦ ?_, fun m a ↦ ?_⟩
  · simpa using hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
  · simpa using (hHw i).deg (fun _ ↦ 0) (fun _ ↦ 0) u m (fun i hi ↦ absurd hi (by omega)) hm
  · have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] M) ↦ G (single a) m) hd
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r, Pi.sub_apply] at h1
    rw [hH.tr (Bar.sh _), hH.tr (Bar.tr 0 _)] at h1
    have ht : ∀ x : ℕ → Λ, Bar.tr 0 x = fun _ ↦ 0 := fun x ↦ funext fun _ ↦ by simp [Bar.tr]
    rw [ht, ht] at h1
    simpa [ActLift.act, single, Bar.cons] using h1.symm

include hMa hNa hMp hNp hMw hNw in
/-- **Lifts of maps of weight `ω`** with corrections of weight `ω + χ`. -/
theorem exists_mapLiftW {q s : ℤ} (L : ActLift μ q MM) (L' : ActLift μ q NN) {χ : Fin r → ℤ}
    (hL : ∀ i, Good (MMw i) (MMw i) 1 (χ i) L.ν) (hL' : ∀ i, Good (NNw i) (NNw i) 1 (χ i) L'.ν)
    (f : M →ₗ[R] N) (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfdeg : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + s) (f m))
    {ω : Fin r → ℤ} (hfw : ∀ i u m, (MMw i).gr.IsHom u m → (NNw i).gr.IsHom (u + ω i) (f m))
    (h : ExtVanish MM NN 0 (s + q)) :
    ∃ g : M →ₗ[R] N, (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + (s + q)) (g m)) ∧
      (∀ i u m, (MMw i).gr.IsHom u m → (NNw i).gr.IsHom (u + (ω i + χ i)) (g m)) ∧
      IsLiftHom L L' f g := by
  let E : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦ L'.ν a ∘ₗ f - f ∘ₗ L.ν a
  have hE : ∀ a m, E a m = L'.act (f m) (a 0) - f (L.act m (a 0)) := fun a m ↦ by
    simp [E, L.ν_eq, L'.ν_eq]
  have htr : ∀ a, E a = E (Bar.tr (0 + 1) a) := fun a ↦ by
    ext m; simp only [hE, Bar.tr]; simp
  have hadd : ∀ a i x y, i < 0 + 1 → E (Function.update a i (x + y)) =
      E (Function.update a i x) + E (Function.update a i y) := fun a i x y hi ↦ by
    obtain rfl : i = 0 := by omega
    ext m
    simp only [hE, Function.update_self, LinearMap.add_apply, L.act_add', L'.act_add', map_add]
    abel
  have hsmul : ∀ a i (c : R) x, i < 0 + 1 → E (Function.update a i (c • x)) =
      c • E (Function.update a i x) := fun a i c x hi ↦ by
    obtain rfl : i = 0 := by omega
    ext m
    simp only [hE, Function.update_self, LinearMap.smul_apply]
    simp [ActLift.act, L.good.single_smul, L'.good.single_smul, smul_sub]
  have hgood : Good MM NN (0 + 1) (s + q) E := by
    refine ⟨htr, hadd, hsmul, fun a ds p m ha hm ↦ ?_⟩
    rw [hE]
    have ha0 := ha 0 (by norm_num)
    have h1 := L'.act_deg (hfdeg p m hm) ha0
    have h2 := hfdeg _ _ (L.act_deg hm ha0)
    rw [show ∑ i ∈ Finset.range (0 + 1), ds i = ds 0 by simp]
    rw [sub_eq_add_neg]
    refine NN.gr.isHom_add ?_ (NN.gr.isHom_neg ?_)
    · convert h1 using 1; ring
    · convert h2 using 1; ring
  have hgoodw : ∀ i, Good (MMw i) (NNw i) 1 (ω i + χ i) E := by
    intro i
    refine ⟨htr, hadd, hsmul, fun a ds u m ha hm ↦ ?_⟩
    rw [hE]
    have ha0 := ha 0 (by norm_num)
    have h1 := (hL' i).one_deg (hfw i u m hm) ha0
    have h2 := hfw i _ _ ((hL i).one_deg hm ha0)
    rw [show ∑ i ∈ Finset.range 1, ds i = ds 0 by simp, sub_eq_add_neg]
    refine (NNw i).gr.isHom_add ?_ ((NNw i).gr.isHom_neg ?_)
    · change (NNw i).gr.IsHom _ (L'.ν (single (a 0)) (f m))
      convert h1 using 1; ring
    · change (NNw i).gr.IsHom _ (f (L.ν (single (a 0)) m))
      convert h2 using 1; ring
  have hd : Bar.d (homAct MM NN) (0 + 1) E = 0 := by
    funext a
    ext m
    simp only [zero_add, Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l,
      homAct_r, hE, Pi.zero_apply, LinearMap.zero_apply]
    simp only [Bar.sh, Bar.ct, Bar.tr]
    norm_num
    have e1 := L'.equation (f m) (a 0) (a 1)
    have e2 := congrArg f (L.equation m (a 0) (a 1))
    rw [map_add, map_sub, hf, hf] at e2
    rw [hf]
    linear_combination (norm := abel) e1 - e2
  obtain ⟨H, hH, hHw, hdH⟩ := extVanish_weights0 (MM := MM) (NN := NN) MMw NNw hMa hNa hMp hNp
    hMw hNw h (fun i ↦ ω i + χ i) E hgood hgoodw hd
  refine ⟨H (fun _ ↦ 0), fun p m hm ↦ ?_, fun i u m hm ↦ ?_, hf, fun m a ↦ ?_⟩
  · simpa using hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
  · simpa using (hHw i).deg (fun _ ↦ 0) (fun _ ↦ 0) u m (fun i hi ↦ absurd hi (by omega)) hm
  · have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (single a) m) hdH
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r] at h1
    rw [hH.tr (Bar.sh _), hH.tr (Bar.tr 0 _)] at h1
    have ht : ∀ x : ℕ → Λ, Bar.tr 0 x = fun _ ↦ 0 := fun x ↦ funext fun _ ↦ by simp [Bar.tr]
    rw [ht, ht, hE] at h1
    simpa [single, Bar.cons] using h1

/-! ### A grading by an arbitrary abelian group -/

section Group

variable {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] (gΛ : GrΓ (R := R) Λ Γ)
  (gM : MGr R Γ M) (gN : MGr R Γ N)
  (hMa' : ∀ u v m a, gM.IsHom u m → gΛ.g.IsHom v a → gM.IsHom (u + v) (MM.act m a))
  (hNa' : ∀ u v n a, gN.IsHom u n → gΛ.g.IsHom v a → gN.IsHom (u + v) (NN.act n a))
  (hΛ' : ∀ v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p (gΛ.g.proj v a))
  (hMp' : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (gM.proj u m))
  (hNp' : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (gN.proj x n))

/-- `μ` raises the `Γ`-weight by `χ`. -/
def HDegΓ (χ : Γ) : Prop :=
  ∀ a b x y, gΛ.g.IsHom a x → gΛ.g.IsHom b y → gΛ.g.IsHom (a + b + χ) (μ x y)

include hMa' in
theorem muCochain_goodΓ {χ : Γ} (hχ : HDegΓ gΛ (μ := μ) χ) :
    GoodΓ gΛ gM gM 2 χ (muCochain μ MM) := by
  intro a ds u m ha hm
  rw [muCochain_apply]
  have h := hMa' _ _ _ _ hm (hχ _ _ _ _ (ha 0 (by norm_num)) (ha 1 (by norm_num)))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  convert h using 1
  abel

include hMa' hΛ' hMp' in
/-- **Lemma 6.6, the lifted actions homogeneous for a grading by an abelian group.** -/
theorem exists_actLiftΓ {q : ℤ} (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ)
    (h : ExtVanish MM MM 1 q) {χ : Γ} (hχ : HDegΓ gΛ (μ := μ) χ) :
    ∃ L : ActLift μ q MM, GoodΓ gΛ gM gM 1 χ L.ν := by
  obtain ⟨H, hH, hHw, hd⟩ := extVanishΓ1 (MM := MM) (NN := MM) gΛ gM gM hMa' hMa' hΛ' hMp' hMp' h
    χ (muCochain μ MM) (muCochain_good μ hq MM) (muCochain_goodΓ gΛ gM hMa' hχ)
    (muCochain_d μ hμ MM)
  exact ⟨⟨H, hH, hd⟩, hHw⟩

include hMa' hMp' in
/-- **Lemma 6.6, uniqueness of `Γ`-homogeneous lifts** up to a coordinate change of weight `χ`. -/
theorem ActLift.exists_isoΓ {q : ℤ} (L L' : ActLift μ q MM) {χ : Γ}
    (hL : GoodΓ gΛ gM gM 1 χ L.ν) (hL' : GoodΓ gΛ gM gM 1 χ L'.ν) (h : ExtVanish MM MM 0 q) :
    ∃ φ : M →ₗ[R] M, (∀ p m, MM.gr.IsHom p m → MM.gr.IsHom (p + q) (φ m)) ∧
      (∀ u m, gM.IsHom u m → gM.IsHom (u + χ) (φ m)) ∧
      ∀ m a, L'.act m a - L.act m a = φ (MM.act m a) - MM.act (φ m) a := by
  have hg : Good MM MM (0 + 1) q (L'.ν - L.ν) := by
    have := L'.good.add' (L.good.zsmul' (-1))
    simpa [sub_eq_add_neg] using this
  have hgw : GoodΓ gΛ gM gM 1 χ (L'.ν - L.ν) := fun a ds u m ha hm ↦ by
    simp only [Pi.sub_apply, sub_eq_add_neg]
    exact gM.isHom_add (hL' a ds u m ha hm) (gM.isHom_neg (hL a ds u m ha hm))
  obtain ⟨H, hH, hHw, hd⟩ := extVanishΓ0 (MM := MM) (NN := MM) gΛ gM gM hMa' hMa' hMp' hMp' h χ
    (L'.ν - L.ν) hg hgw (by rw [map_sub, L'.eq, L.eq, sub_self])
  refine ⟨H (fun _ ↦ 0), fun p m hm ↦ ?_, fun u m hm ↦ ?_, fun m a ↦ ?_⟩
  · simpa using hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
  · simpa using hHw (fun _ ↦ 0) (fun _ ↦ 0) u m (fun i hi ↦ absurd hi (by omega)) hm
  · have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] M) ↦ G (single a) m) hd
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r, Pi.sub_apply] at h1
    rw [hH.tr (Bar.sh _), hH.tr (Bar.tr 0 _)] at h1
    have ht : ∀ x : ℕ → Λ, Bar.tr 0 x = fun _ ↦ 0 := fun x ↦ funext fun _ ↦ by simp [Bar.tr]
    rw [ht, ht] at h1
    simpa [ActLift.act, single, Bar.cons] using h1.symm

include hMa' hNa' hMp' hNp' in
/-- **Lemma 6.6, lifts of maps of `Γ`-weight `ω`** with corrections of weight `ω + χ`. -/
theorem exists_mapLiftΓ {q s : ℤ} (L : ActLift μ q MM) (L' : ActLift μ q NN) {χ : Γ}
    (hL : GoodΓ gΛ gM gM 1 χ L.ν) (hL' : GoodΓ gΛ gN gN 1 χ L'.ν)
    (f : M →ₗ[R] N) (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfdeg : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + s) (f m))
    {ω : Γ} (hfw : ∀ u m, gM.IsHom u m → gN.IsHom (u + ω) (f m))
    (h : ExtVanish MM NN 0 (s + q)) :
    ∃ g : M →ₗ[R] N, (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + (s + q)) (g m)) ∧
      (∀ u m, gM.IsHom u m → gN.IsHom (u + (ω + χ)) (g m)) ∧ IsLiftHom L L' f g := by
  let E : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦ L'.ν a ∘ₗ f - f ∘ₗ L.ν a
  have hE : ∀ a m, E a m = L'.act (f m) (a 0) - f (L.act m (a 0)) := fun a m ↦ by
    simp [E, L.ν_eq, L'.ν_eq]
  have hgood : Good MM NN (0 + 1) (s + q) E := by
    refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds p m ha hm ↦ ?_⟩
    · ext m; simp only [hE, Bar.tr]; simp
    · obtain rfl : i = 0 := by omega
      ext m
      simp only [hE, Function.update_self, LinearMap.add_apply, L.act_add', L'.act_add', map_add]
      abel
    · obtain rfl : i = 0 := by omega
      ext m
      simp only [hE, Function.update_self, LinearMap.smul_apply]
      simp [ActLift.act, L.good.single_smul, L'.good.single_smul, smul_sub]
    · rw [hE]
      have ha0 := ha 0 (by norm_num)
      have h1 := L'.act_deg (hfdeg p m hm) ha0
      have h2 := hfdeg _ _ (L.act_deg hm ha0)
      rw [show ∑ i ∈ Finset.range (0 + 1), ds i = ds 0 by simp]
      rw [sub_eq_add_neg]
      refine NN.gr.isHom_add ?_ (NN.gr.isHom_neg ?_)
      · convert h1 using 1; ring
      · convert h2 using 1; ring
  have hgoodw : GoodΓ gΛ gM gN 1 (ω + χ) E := by
    intro a ds u m ha hm
    rw [hE]
    have ha0 := ha 0 (by norm_num)
    have h1 := hL' (single (a 0)) (fun _ ↦ ds 0) (u + ω) (f m) (fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simpa [single, Bar.cons] using ha0) (hfw u m hm)
    have h2 := hfw _ _ (hL (single (a 0)) (fun _ ↦ ds 0) u m (fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simpa [single, Bar.cons] using ha0) hm)
    rw [show ∑ i ∈ Finset.range 1, ds i = ds 0 by simp, sub_eq_add_neg]
    simp only [Finset.sum_range_one] at h1 h2
    refine gN.isHom_add ?_ (gN.isHom_neg ?_)
    · change gN.IsHom _ (L'.ν (single (a 0)) (f m))
      convert h1 using 1; abel
    · change gN.IsHom _ (f (L.ν (single (a 0)) m))
      convert h2 using 1; abel
  have hd : Bar.d (homAct MM NN) (0 + 1) E = 0 := by
    funext a
    ext m
    simp only [zero_add, Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l,
      homAct_r, hE, Pi.zero_apply, LinearMap.zero_apply]
    simp only [Bar.sh, Bar.ct, Bar.tr]
    norm_num
    have e1 := L'.equation (f m) (a 0) (a 1)
    have e2 := congrArg f (L.equation m (a 0) (a 1))
    rw [map_add, map_sub, hf, hf] at e2
    rw [hf]
    linear_combination (norm := abel) e1 - e2
  obtain ⟨H, hH, hHw, hdH⟩ := extVanishΓ0 (MM := MM) (NN := NN) gΛ gM gN hMa' hNa' hMp' hNp' h
    (ω + χ) E hgood hgoodw hd
  refine ⟨H (fun _ ↦ 0), fun p m hm ↦ ?_, fun u m hm ↦ ?_, hf, fun m a ↦ ?_⟩
  · simpa using hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
  · simpa using hHw (fun _ ↦ 0) (fun _ ↦ 0) u m (fun i hi ↦ absurd hi (by omega)) hm
  · have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (single a) m) hdH
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r] at h1
    rw [hH.tr (Bar.sh _), hH.tr (Bar.tr 0 _)] at h1
    have ht : ∀ x : ℕ → Λ, Bar.tr 0 x = fun _ ↦ 0 := fun x ↦ funext fun _ ↦ by simp [Bar.tr]
    rw [ht, ht, hE] at h1
    simpa [single, Bar.cons] using h1

end Group

end GExt

end MultiplicativeBasisDeformations
