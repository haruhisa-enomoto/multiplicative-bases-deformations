import MultiplicativeBasisDeformations.Foundations.GradedExt

/-!
# Square-zero lifts of modules and maps (Lemma 6.6)

`positive-deformations.tex` (`lem:square-zero-selected-lifts`): for a
Hochschild two-cocycle `μ` of internal degree `q > 0` of a graded algebra `Λ`
over `R` (a field or `ℤ/4`), put `Λ_μ = (Λ ⊗ R[ε]/(ε²), m + εμ)`. "Write a
lifted action as `ma + εν_i(m,a)`. Its equation is
`ν_i(ma,b) − ν_i(m,ab) + ν_i(m,a)b = mμ(a,b)`. […] The degree-`q` `Ext²`
vanishing supplies `ν_i`. […] The difference of two solutions is a bar
one-cocycle of degree `q`; the `Ext¹` vanishing makes it the coboundary of a
degree-`q` coordinate change. […] For a degree-`r` map `f`, write its lift as
`f + εg`. Its equation is `g(ma) − g(m)a = ν_j(f(m),a) − f(ν_i(m,a))`. […] Since
`r ≥ 0`, the `Ext¹` vanishing supplies `g`. […] Let `F_1, …, F_h` lift a basis
`f_1, …, f_h` of an original Hom module […] This proves freeness."

Formalization: the lifted module and maps are recorded by their first-order
equations (`ActLift`, `IsLiftHom`), with `R[ε]`-linear structure
`ε·(f, g) = (0, f)`; the regular lift at a cyclic projective is `ν = μ`
(`CycProj.actLift`, the paper's "If `M_i = e_xΛ`, the regular module `e_xΛ_μ`
is such a lift"). The additional gradings of the lemma are in `SquareZeroWeight.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

variable (μ : Λ →ₗ[R] Λ →ₗ[R] Λ)

/-- The Hochschild cocycle equation `aμ(b,c) − μ(ab,c) + μ(a,bc) − μ(a,b)c = 0`. -/
def IsHCocycle : Prop := ∀ a b c : Λ, a * μ b c - μ (a * b) c + μ a (b * c) - μ a b * c = 0

variable (GΛ) in
/-- A two-cochain of internal degree `q`. -/
def HDeg (q : ℤ) : Prop :=
  ∀ p p' a b, GΛ.gr.IsHom p a → GΛ.gr.IsHom p' b → GΛ.gr.IsHom (p + p' + q) (μ a b)

/-- The bar two-cochain `(m, a, b) ↦ m μ(a, b)`. -/
def muCochain (MM : GMod GΛ M) : Bar.Cochain Λ (M →ₗ[R] M) := fun a ↦ MM.act.flip (μ (a 0) (a 1))

theorem muCochain_apply (MM : GMod GΛ M) (a : ℕ → Λ) (m : M) :
    muCochain μ MM a m = MM.act m (μ (a 0) (a 1)) := rfl

theorem muCochain_good {q : ℤ} (hq : HDeg GΛ μ q) (MM : GMod GΛ M) :
    Good MM MM 2 q (muCochain μ MM) where
  tr a := by ext m; simp [muCochain_apply, Bar.tr]
  add a i x y hi := by
    ext m
    interval_cases i <;> simp [muCochain_apply, Function.update, map_add]
  smul a i c x hi := by
    ext m
    interval_cases i <;> simp [muCochain_apply, Function.update, map_smul]
  deg a ds p m ha hm := by
    rw [muCochain_apply]
    have := MM.act_hom _ _ _ _ hm (hq _ _ _ _ (ha 0 (by norm_num)) (ha 1 (by norm_num)))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    convert this using 1
    ring

theorem muCochain_d (hμ : IsHCocycle μ) (MM : GMod GΛ M) :
    Bar.d (homAct MM MM) 2 (muCochain μ MM) = 0 := by
  funext a
  ext m
  rw [Bar.d_two_apply]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, homAct_l, homAct_r, muCochain_apply,
    Pi.zero_apply, LinearMap.zero_apply, MM.act_mul]
  simp only [Bar.sh, Bar.ct, Bar.tr]
  norm_num
  rw [← map_sub, ← map_add, ← map_sub, hμ (a 0) (a 1) (a 2), map_zero]

/-! ### Lifted actions -/

/-- **A first-order lift of the action** of `M` to `Λ_μ`: `m * a = ma + εν(m,a)`. -/
structure ActLift (q : ℤ) (MM : GMod GΛ M) where
  ν : Bar.Cochain Λ (M →ₗ[R] M)
  good : Good MM MM 1 q ν
  eq : Bar.d (homAct MM MM) 1 ν = muCochain μ MM

theorem exists_actLift {q : ℤ} (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ) (MM : GMod GΛ M)
    (h : ExtVanish MM MM 1 q) : Nonempty (ActLift μ q MM) := by
  obtain ⟨H, hH, hd⟩ := h _ (muCochain_good μ hq MM) (muCochain_d μ hμ MM)
  exact ⟨⟨H, hH, hd⟩⟩

variable {μ}

/-- The correction `ν(m, a)`. -/
def ActLift.act {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (m : M) (a : Λ) : M :=
  L.ν (single a) m

theorem ActLift.act_add {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (m m' : M) (a : Λ) :
    L.act (m + m') a = L.act m a + L.act m' a := map_add _ _ _

theorem ActLift.act_add' {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (m : M) (a a' : Λ) :
    L.act m (a + a') = L.act m a + L.act m a' := by
  simp [ActLift.act, L.good.single_add]

@[simp] theorem ActLift.act_zero {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (a : Λ) :
    L.act 0 a = 0 := map_zero _

theorem ActLift.ν_eq {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (a : ℕ → Λ) (m : M) :
    L.ν a m = L.act m (a 0) := by
  rw [ActLift.act, L.good.one_eq]

theorem ActLift.act_deg {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) {p d : ℤ} {m : M} {a : Λ}
    (hm : MM.gr.IsHom p m) (ha : GΛ.gr.IsHom d a) : MM.gr.IsHom (p + d + q) (L.act m a) := by
  have := L.good.deg (single a) (fun _ ↦ d) p m (fun i hi ↦ by
    obtain rfl : i = 0 := by omega
    simpa [single, Bar.cons] using ha) hm
  simpa [ActLift.act] using this

/-- **The lifted action equation** `ν(ma,b) − ν(m,ab) + ν(m,a)b = mμ(a,b)`. -/
theorem ActLift.equation {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (m : M) (a b : Λ) :
    L.act (MM.act m a) b - L.act m (a * b) + MM.act (L.act m a) b = MM.act m (μ a b) := by
  have h := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] M) ↦ G (Bar.cons a (single b)) m) L.eq
  simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r,
    muCochain_apply, L.ν_eq] at h
  simpa [Bar.sh, Bar.ct, Bar.tr, Bar.cons, single] using h

/-- **Uniqueness of lifted actions** up to a coordinate change `1 + εh` of degree `q`. -/
theorem ActLift.exists_iso {q : ℤ} {MM : GMod GΛ M} (L L' : ActLift μ q MM)
    (h : ExtVanish MM MM 0 q) :
    ∃ φ : M →ₗ[R] M, (∀ p m, MM.gr.IsHom p m → MM.gr.IsHom (p + q) (φ m)) ∧
      ∀ m a, L'.act m a - L.act m a = φ (MM.act m a) - MM.act (φ m) a := by
  have hg : Good MM MM (0 + 1) q (L'.ν - L.ν) := by
    have := L'.good.add' (L.good.zsmul' (-1))
    simpa [sub_eq_add_neg] using this
  obtain ⟨H, hH, hd⟩ := h (L'.ν - L.ν) hg (by rw [map_sub, L'.eq, L.eq, sub_self])
  refine ⟨H (fun _ ↦ 0), fun p m hm ↦ ?_, fun m a ↦ ?_⟩
  · simpa using hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
  · have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] M) ↦ G (single a) m) hd
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r, Pi.sub_apply] at h1
    rw [hH.tr (Bar.sh _), hH.tr (Bar.tr 0 _)] at h1
    have ht : ∀ x : ℕ → Λ, Bar.tr 0 x = fun _ ↦ 0 := fun x ↦ funext fun _ ↦ by simp [Bar.tr]
    rw [ht, ht] at h1
    simpa [ActLift.act, single, Bar.cons] using h1.symm

/-! ### Linearity in the cocycle -/

theorem d_homAct_smul {MM : GMod GΛ M} {NN : GMod GΛ N} (n : ℕ) (t : R)
    (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    Bar.d (homAct MM NN) n (t • F) = t • Bar.d (homAct MM NN) n F := by
  rw [Bar.d_apply, Bar.d_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_comm]
  congr 1
  funext a
  ext m
  simp only [Bar.coface, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply]
  split_ifs <;> simp [homAct_l, homAct_r, map_smul]

theorem muCochain_add (μ' : Λ →ₗ[R] Λ →ₗ[R] Λ) (MM : GMod GΛ M) :
    muCochain (μ + μ') MM = muCochain μ MM + muCochain μ' MM := by
  funext a; ext m; simp [muCochain_apply, map_add]

theorem muCochain_smul (t : R) (MM : GMod GΛ M) :
    muCochain (t • μ) MM = t • muCochain μ MM := by
  funext a; ext m; simp [muCochain_apply, map_smul]

/-- The sum of lifted actions for `μ` and `μ'` is one for `μ + μ'`. -/
def ActLift.add {μ' : Λ →ₗ[R] Λ →ₗ[R] Λ} {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM)
    (L' : ActLift μ' q MM) : ActLift (μ + μ') q MM where
  ν := L.ν + L'.ν
  good := L.good.add' L'.good
  eq := by rw [map_add, L.eq, L'.eq, muCochain_add]

theorem ActLift.add_act {μ' : Λ →ₗ[R] Λ →ₗ[R] Λ} {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM)
    (L' : ActLift μ' q MM) (m : M) (a : Λ) : (L.add L').act m a = L.act m a + L'.act m a := rfl

/-- A scalar multiple of a lifted action. -/
def ActLift.smul {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (t : R) : ActLift (t • μ) q MM where
  ν := t • L.ν
  good := by
    refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds p m ha hm ↦ ?_⟩
    · simp only [Pi.smul_apply]; rw [L.good.tr a]
    · simp only [Pi.smul_apply]; rw [L.good.add a i x y hi, smul_add]
    · simp only [Pi.smul_apply]; rw [L.good.smul a i c x hi, smul_comm]
    · simp only [Pi.smul_apply, LinearMap.smul_apply]
      exact MM.gr.isHom_smul t (L.good.deg a ds p m ha hm)
  eq := by rw [d_homAct_smul, L.eq, muCochain_smul]

theorem ActLift.smul_act {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM) (t : R) (m : M) (a : Λ) :
    (L.smul t).act m a = t • L.act m a := rfl

variable (h : Λ →ₗ[R] Λ)

/-- The coboundary `dh(a,b) = a h(b) − h(ab) + h(a) b`. -/
def hcobdry : Λ →ₗ[R] Λ →ₗ[R] Λ :=
  LinearMap.mk₂ R (fun a b ↦ a * h b - h (a * b) + h a * b)
    (fun a a' b ↦ by simp only [add_mul, map_add]; abel)
    (fun c a b ↦ by simp only [smul_mul_assoc, map_smul, smul_sub, smul_add])
    (fun a b b' ↦ by simp only [mul_add, map_add]; abel)
    (fun c a b ↦ by simp only [mul_smul_comm, map_smul, smul_sub, smul_add])

theorem hcobdry_apply (a b : Λ) : hcobdry h a b = a * h b - h (a * b) + h a * b := rfl

/-- **Transport of a lifted action along a coboundary**: `ν'(m, a) = ν(m, a) + m h(a)`. -/
def ActLift.cobdry {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM)
    (hdeg : ∀ p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom (p + q) (h a)) :
    ActLift (μ + hcobdry h) q MM where
  ν := L.ν + fun a ↦ MM.act.flip (h (a 0))
  good := by
    refine L.good.add' ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_,
      fun a ds p m ha hm ↦ ?_⟩
    · simp [Bar.tr]
    · obtain rfl : i = 0 := by omega
      ext m; simp [map_add]
    · obtain rfl : i = 0 := by omega
      ext m; simp [map_smul]
    · simp only [LinearMap.flip_apply, Finset.sum_range_one]
      have := MM.act_hom _ _ _ _ hm (hdeg _ _ (ha 0 (by norm_num)))
      convert this using 1; ring
  eq := by
    rw [map_add, L.eq, muCochain_add]
    congr 1
    funext a
    ext m
    simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r,
      LinearMap.flip_apply, muCochain_apply, hcobdry_apply, MM.act_mul, map_add, map_sub]
    simp only [Bar.sh, Bar.ct, Bar.tr]
    norm_num

theorem ActLift.cobdry_act {q : ℤ} {MM : GMod GΛ M} (L : ActLift μ q MM)
    (hdeg : ∀ p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom (p + q) (h a)) (m : M) (a : Λ) :
    (L.cobdry h hdeg).act m a = L.act m a + MM.act m (h a) := by
  simp [ActLift.act, ActLift.cobdry, single, Bar.cons]

/-! ### Regular lifts of cyclic projectives -/

/-- **The regular lift** `ν(m, a) = g·μ(ψ m, a)` of a cyclic projective `eΛ⟨b⟩`. -/
def CycProj.actLift {q : ℤ} (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ) {PP : GMod GΛ P}
    (C : CycProj PP) : ActLift μ q PP where
  ν a := (PP.act C.g).comp ((μ.flip (a 0)).comp C.ψ)
  good := by
    refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds p m ha hm ↦ ?_⟩
    · simp [Bar.tr]
    · obtain rfl : i = 0 := by omega
      ext m; simp
    · obtain rfl : i = 0 := by omega
      ext m; simp
    · simp only [LinearMap.comp_apply, LinearMap.flip_apply, Finset.sum_range_one]
      have h1 := hq _ _ _ _ (C.ψ_deg p m hm) (ha 0 (by norm_num))
      have := PP.act_hom _ _ _ _ C.hg h1
      convert this using 1
      ring
  eq := by
    funext a
    ext m
    simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r,
      muCochain_apply, LinearMap.comp_apply, LinearMap.flip_apply, C.ψ_act]
    simp only [Bar.sh, Bar.ct, Bar.tr, show (0 : ℕ) < 1 from Nat.one_pos, if_true,
      lt_self_iff_false, if_false, zero_add]
    norm_num
    rw [PP.act_mul, ← map_sub, ← map_add]
    have hc := hμ (C.ψ m) (a 0) (a 1)
    have : μ (C.ψ m * a 0) (a 1) - μ (C.ψ m) (a 0 * a 1) + μ (C.ψ m) (a 0) * a 1 =
        C.ψ m * μ (a 0) (a 1) := by
      rw [← sub_eq_zero, ← neg_eq_zero, ← hc]; abel
    rw [this, ← PP.act_mul, C.act_ψ]

theorem CycProj.actLift_act {q : ℤ} (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ) {PP : GMod GΛ P}
    (C : CycProj PP) (m : P) (a : Λ) : (C.actLift hq hμ).act m a = PP.act C.g (μ (C.ψ m) a) := by
  simp [ActLift.act, CycProj.actLift, single, Bar.cons]

/-! ### Lifted maps -/

variable {MM : GMod GΛ M} {NN : GMod GΛ N} {PP : GMod GΛ P}

/-- **A lifted map** `f + εg : M^μ → N^μ`. -/
def IsLiftHom {q : ℤ} (L : ActLift μ q MM) (L' : ActLift μ q NN) (f g : M →ₗ[R] N) : Prop :=
  (∀ m a, f (MM.act m a) = NN.act (f m) a) ∧
    ∀ m a, g (MM.act m a) - NN.act (g m) a = L'.act (f m) a - f (L.act m a)

theorem isLiftHom_zero_iff {q : ℤ} (L : ActLift μ q MM) (L' : ActLift μ q NN) (g : M →ₗ[R] N) :
    IsLiftHom L L' 0 g ↔ ∀ m a, g (MM.act m a) = NN.act (g m) a := by
  simp only [IsLiftHom, LinearMap.zero_apply, map_zero, implies_true, true_and,
    ActLift.act_zero, sub_zero, sub_eq_zero]

theorem IsLiftHom.add {q : ℤ} {L : ActLift μ q MM} {L' : ActLift μ q NN} {f g f' g' : M →ₗ[R] N}
    (h : IsLiftHom L L' f g) (h' : IsLiftHom L L' f' g') : IsLiftHom L L' (f + f') (g + g') := by
  refine ⟨fun m a ↦ by simp [h.1, h'.1], fun m a ↦ ?_⟩
  have e := h.2 m a
  have e' := h'.2 m a
  simp only [LinearMap.add_apply, map_add, LinearMap.add_apply, L'.act_add]
  rw [show g (MM.act m a) + g' (MM.act m a) - (NN.act (g m) a + NN.act (g' m) a) =
    (g (MM.act m a) - NN.act (g m) a) + (g' (MM.act m a) - NN.act (g' m) a) by abel, e, e']
  abel

theorem IsLiftHom.smul {q : ℤ} {L : ActLift μ q MM} {L' : ActLift μ q NN} {f g : M →ₗ[R] N}
    (h : IsLiftHom L L' f g) (c : R) : IsLiftHom L L' (c • f) (c • g) := by
  refine ⟨fun m a ↦ by simp [h.1], fun m a ↦ ?_⟩
  simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
  have hc : L'.act (c • f m) a = c • L'.act (f m) a := by
    simp [ActLift.act]
  rw [hc, ← smul_sub, ← smul_sub, h.2]

/-- **Composition of lifted maps**: `(f' + εg')(f + εg) = f'f + ε(f'g + g'f)`. -/
theorem IsLiftHom.comp {q : ℤ} {L : ActLift μ q MM} {L' : ActLift μ q NN} {L'' : ActLift μ q PP}
    {f g : M →ₗ[R] N} {f' g' : N →ₗ[R] P} (h' : IsLiftHom L' L'' f' g') (h : IsLiftHom L L' f g) :
    IsLiftHom L L'' (f' ∘ₗ f) (f' ∘ₗ g + g' ∘ₗ f) := by
  refine ⟨fun m a ↦ by simp [h.1, h'.1], fun m a ↦ ?_⟩
  have e1 := congrArg f' (h.2 m a)
  rw [map_sub, map_sub, h'.1] at e1
  have e2 := h'.2 (f m) a
  have hsplit : (f' ∘ₗ g + g' ∘ₗ f) (MM.act m a) - PP.act ((f' ∘ₗ g + g' ∘ₗ f) m) a =
      (f' (g (MM.act m a)) - PP.act (f' (g m)) a) + (g' (NN.act (f m) a) - PP.act (g' (f m)) a) := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, h.1, map_add, LinearMap.add_apply]
    abel
  rw [hsplit, e1, e2]
  simp only [LinearMap.comp_apply]
  abel

/-- **Existence of map lifts** (`r ≥ 0`, using `Ext¹_{r+q} = 0`). -/
theorem exists_mapLift {q r : ℤ} (L : ActLift μ q MM) (L' : ActLift μ q NN) (f : M →ₗ[R] N)
    (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfdeg : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))
    (h : ExtVanish MM NN 0 (r + q)) :
    ∃ g : M →ₗ[R] N, (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + (r + q)) (g m)) ∧
      IsLiftHom L L' f g := by
  let E : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦ L'.ν a ∘ₗ f - f ∘ₗ L.ν a
  have hE : ∀ a m, E a m = L'.act (f m) (a 0) - f (L.act m (a 0)) := fun a m ↦ by
    simp [E, L.ν_eq, L'.ν_eq]
  have hgood : Good MM NN (0 + 1) (r + q) E := by
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
  obtain ⟨H, hH, hdH⟩ := h E hgood hd
  refine ⟨H (fun _ ↦ 0), fun p m hm ↦ ?_, hf, fun m a ↦ ?_⟩
  · simpa using hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
  · have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (single a) m) hdH
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r] at h1
    rw [hH.tr (Bar.sh _), hH.tr (Bar.tr 0 _)] at h1
    have ht : ∀ x : ℕ → Λ, Bar.tr 0 x = fun _ ↦ 0 := fun x ↦ funext fun _ ↦ by simp [Bar.tr]
    rw [ht, ht, hE] at h1
    simpa [single, Bar.cons] using h1

/-- **Freeness of lifted Hom modules**: lifts `(f_l, g_l)` of a basis `f_l` of the
original Hom module form an `R[ε]`-basis, i.e. every lifted map is uniquely
`Σ c_l (f_l, g_l) + Σ c'_l ε(f_l, g_l)` with `ε(f, g) = (0, f)`. -/
theorem liftHom_basis {q : ℤ} {L : ActLift μ q MM} {L' : ActLift μ q NN} {ι : Type*}
    [Fintype ι] (fs gs : ι → M →ₗ[R] N)
    (hbasis : ∀ f : M →ₗ[R] N, (∀ m a, f (MM.act m a) = NN.act (f m) a) →
      ∃! c : ι → R, f = ∑ l, c l • fs l)
    (hgs : ∀ l, IsLiftHom L L' (fs l) (gs l)) {f g : M →ₗ[R] N} (hfg : IsLiftHom L L' f g) :
    ∃! cc : (ι → R) × (ι → R),
      f = ∑ l, cc.1 l • fs l ∧ g = ∑ l, cc.1 l • gs l + ∑ l, cc.2 l • fs l := by
  classical
  have hsum : ∀ c : ι → R, IsLiftHom L L' (∑ l, c l • fs l) (∑ l, c l • gs l) := fun c ↦ by
    have key : ∀ s : Finset ι, IsLiftHom L L' (∑ l ∈ s, c l • fs l) (∑ l ∈ s, c l • gs l) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp [ActLift.act]⟩
      | insert l s hl ih =>
        rw [Finset.sum_insert hl, Finset.sum_insert hl]
        exact ((hgs l).smul (c l)).add ih
    exact key Finset.univ
  obtain ⟨c, hc, hcu⟩ := hbasis f hfg.1
  have hres : IsLiftHom L L' 0 (g - ∑ l, c l • gs l) := by
    have := hfg.add ((hsum c).smul (-1))
    rw [← hc] at this
    simpa [sub_eq_add_neg] using this
  obtain ⟨c', hc', hc'u⟩ := hbasis _ ((isLiftHom_zero_iff L L' _).1 hres)
  refine ⟨(c, c'), ⟨hc, by rw [← hc']; abel⟩, fun ⟨d, d'⟩ ⟨hd, hd'⟩ ↦ ?_⟩
  obtain rfl := hcu d hd
  have : g - ∑ l, d l • gs l = ∑ l, d' l • fs l := by rw [hd']; abel
  obtain rfl := hc'u d' this
  rfl

/-! ### Trivializing derivations

The algebra step of the injectivity in Proposition 7.6 (`weights-and-parameters.tex`):
a lift of the left multiplications to the lifted regular module, written through its value
`Δ` on the regular module and split by a complete family of idempotents, makes `μ` a
coboundary. -/

theorem hcocycle_sum_one {ι : Type*} [Fintype ι] (e : ι → Λ) (he : ∀ i, e i * e i = e i)
    (h1 : ∑ i, e i = 1) (hμ : IsHCocycle μ) (a b : Λ) :
    ∑ i, (μ (e i) (e i * (a * b)) - μ (e i) (e i * a) * b + e i * μ (e i * a) b) = μ a b := by
  have : ∀ i, μ (e i) (e i * (a * b)) - μ (e i) (e i * a) * b + e i * μ (e i * a) b =
      μ (e i * a) b := by
    intro i
    have h := hμ (e i) (e i * a) b
    rw [← mul_assoc (e i) (e i) a, he, mul_assoc] at h
    rw [← sub_eq_zero, ← h]
    abel
  rw [Finset.sum_congr rfl fun i _ ↦ this i, ← LinearMap.sum_apply, ← map_sum, ← Finset.sum_mul,
    h1, one_mul]

theorem hcocycle_sum_two {ι : Type*} [Fintype ι] (e : ι → Λ) (he : ∀ i, e i * e i = e i)
    (h1 : ∑ i, e i = 1) (hμ : IsHCocycle μ) (b : Λ) :
    ∑ i, (μ (e i) (e i * b) + e i * μ (e i) b) = (μ 1 1 + ∑ i, μ (e i) (e i)) * b := by
  have hi : ∀ i, μ (e i) (e i * b) + e i * μ (e i) b = μ (e i) b + μ (e i) (e i) * b := by
    intro i
    have h := hμ (e i) (e i) b
    rw [he] at h
    rw [← sub_eq_zero, ← h]
    abel
  have h11 : μ 1 b = μ 1 1 * b := by
    have h := hμ 1 1 b
    rw [one_mul, one_mul, one_mul] at h
    rw [← sub_eq_zero, ← h]
    abel
  rw [Finset.sum_congr rfl fun i _ ↦ hi i, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← LinearMap.sum_apply, ← map_sum, h1, h11, add_mul]

/-- **A trivializing derivation makes `μ` a coboundary.** -/
theorem eq_hcobdry_of_derivation {ι : Type*} [Fintype ι] (e : ι → Λ) (he : ∀ i, e i * e i = e i)
    (h1 : ∑ i, e i = 1) (hμ : IsHCocycle μ) (Δ : Λ →ₗ[R] Λ)
    (hΔ : ∀ x c, Δ (x * c) - x * Δ c - (Δ x - x * Δ 1) * c =
      ∑ i, e i * μ (e i * x) c - x * ∑ i, e i * μ (e i) c) :
    μ = hcobdry (LinearMap.mulLeft R (μ 1 1 + ∑ i, μ (e i) (e i) + Δ 1) -
      ∑ i, (μ (e i)).comp (LinearMap.mulLeft R (e i)) - Δ) := by
  ext a b
  rw [hcobdry_apply]
  simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  have hX := hΔ a b
  have S1 := hcocycle_sum_one e he h1 hμ a b
  have S2 := hcocycle_sum_two e he h1 hμ b
  set w := μ 1 1 + ∑ i, μ (e i) (e i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at S1
  rw [Finset.sum_add_distrib] at S2
  rw [Finset.mul_sum] at hX
  rw [← S1]
  have hS2 : a * (w * b) = a * ∑ i, μ (e i) (e i * b) + a * ∑ i, e i * μ (e i) b := by
    rw [← S2, mul_add]
  rw [Finset.mul_sum] at hS2
  simp only [mul_sub, sub_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
    at hX hS2 ⊢
  rw [eq_comm, ← sub_eq_zero]
  rw [← sub_eq_zero] at hX hS2
  have := congrArg₂ (· + ·) hX hS2
  simp only [add_zero] at this
  rw [← this]
  simp only [mul_assoc]
  abel

end GExt

end MultiplicativeBasisDeformations
