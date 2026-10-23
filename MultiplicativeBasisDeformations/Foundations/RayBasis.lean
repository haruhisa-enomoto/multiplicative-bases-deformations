module

public import MultiplicativeBasisDeformations.Foundations.LocalCorner

/-!
# Rays and ray transversals

Definition 3.2 and Corollary 3.3 (`projective-rays.tex`). For
`0 ≠ f ∈ A(x, y)`, `U(f) = R_x f R_y` is uniserial with radical `R(f)`, its unique
maximal subbimodule (`le_endpointRadical`), and "`[f] = U(f) ∖ R(f)`"
(`eq:ray-layer`; here `mem_ray_iff`). Corollary 3.3: "In each corner, the chosen
vectors represent the consecutive one-dimensional quotients of a finite chain.
They therefore form a basis adapted to every member of that chain."
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (F : PrimitiveIdempotents A)

/-! ### Units of the local corners -/

theorem isCornerUnit_e (x : Fin F.m) : F.IsCornerUnit (k := k) x (F.e x) :=
  ⟨F.e_mem_corner x, F.e x, F.e_mem_corner x, (F.complete.idem x).eq, (F.complete.idem x).eq⟩

theorem cornerUnit_mul {x : Fin F.m} {u w : A} (hu : F.IsCornerUnit (k := k) x u)
    (hw : F.IsCornerUnit (k := k) x w) : F.IsCornerUnit (k := k) x (u * w) := by
  obtain ⟨hu, u', hu', h1, h2⟩ := hu
  obtain ⟨hw, w', hw', h3, h4⟩ := hw
  refine ⟨F.corner_mul_corner hu hw, w' * u', F.corner_mul_corner hw' hu', ?_, ?_⟩
  · calc u * w * (w' * u') = u * (w * w') * u' := by simp only [mul_assoc]
      _ = F.e x := by rw [h3, F.mul_e_of_mem hu, h1]
  · calc w' * u' * (u * w) = w' * (u' * u) * w := by simp only [mul_assoc]
      _ = F.e x := by rw [h2, F.mul_e_of_mem hw', h4]

theorem cornerUnit_inv {x : Fin F.m} {u : A} (hu : F.IsCornerUnit (k := k) x u) :
    ∃ u', F.IsCornerUnit (k := k) x u' ∧ u * u' = F.e x ∧ u' * u = F.e x := by
  obtain ⟨hu, u', hu', h1, h2⟩ := hu
  exact ⟨u', ⟨hu', u, hu, h2, h1⟩, h1, h2⟩

theorem cornerVal_pow_succ {e : A} (he : IsIdempotentElem e) (z : he.Corner) (n : ℕ) :
    cornerVal he (z ^ (n + 1)) = cornerVal he z ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, corner_mul_val, ih, ← pow_succ]

/-- **An element of `R_x` outside `rad R_x` is a unit.** -/
theorem isCornerUnit_of_not_mem {x : Fin F.m} {a : A} (ha : a ∈ F.corner (k := k) x x)
    (ha' : a ∉ F.cornerRadical (k := k) x) : F.IsCornerUnit (k := k) x a := by
  set he := F.complete.idem x
  obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_cornerRadical x ha
  have hc0 : c ≠ 0 := fun h ↦ ha' (by rwa [h, zero_smul, sub_zero] at hc)
  let a' : he.Corner := cornerMk he a (F.corner_mem_sub x ha)
  let j : he.Corner := cornerMk he _ (F.corner_mem_sub x hc.1)
  obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := A)
  have hjK : (a - c • F.e x) ^ K = 0 := by
    have := Submodule.pow_mem_pow _ (F.cornerRadical_le_radical x hc) K
    rwa [hK, Submodule.mem_bot] at this
  have hjnil : IsNilpotent j := ⟨K + 1, corner_ext he (by
    rw [cornerVal_pow_succ, pow_succ, cornerVal_mk, hjK, zero_mul, corner_zero_val])⟩
  have hsplit : a' = j + algebraMap k he.Corner c := corner_ext he (by
    rw [corner_add_val, F.cornerVal_algebraMap, cornerVal_mk, cornerVal_mk, sub_add_cancel])
  have hunit : IsUnit a' := by
    rw [hsplit]
    exact hjnil.isUnit_add_right_of_commute ((isUnit_iff_ne_zero.2 hc0).map _)
      (Algebra.commutes _ _).symm
  obtain ⟨w, hw⟩ := hunit
  refine ⟨ha, cornerVal he (w⁻¹ : he.Cornerˣ).1, F.cornerVal_mem_corner (k := k) x _, ?_, ?_⟩
  · have := congrArg (cornerVal he) w.mul_inv
    rwa [corner_mul_val, hw, corner_one_val] at this
  · have := congrArg (cornerVal he) w.inv_mul
    rwa [corner_mul_val, hw, corner_one_val] at this

/-! ### Rays -/

theorem mem_ray_self {x y : Fin F.m} {f : A} (hf : f ∈ F.corner (k := k) x y) :
    f ∈ F.ray (k := k) x y f :=
  ⟨F.e x, F.e y, F.isCornerUnit_e x, F.isCornerUnit_e y, by
    rw [F.e_mul_of_mem hf, F.mul_e_of_mem hf]⟩

theorem ray_subset_corner {x y : Fin F.m} {f g : A} (hf : f ∈ F.corner (k := k) x y)
    (hg : g ∈ F.ray (k := k) x y f) : g ∈ F.corner (k := k) x y := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hg
  exact F.corner_mul_corner (F.corner_mul_corner hu.1 hf) hw.1

theorem ray_eq_of_mem {x y : Fin F.m} {f g : A} (hf : f ∈ F.corner (k := k) x y)
    (hg : g ∈ F.ray (k := k) x y f) : F.ray (k := k) x y g = F.ray (k := k) x y f := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hg
  obtain ⟨u', hu', h1, h2⟩ := F.cornerUnit_inv hu
  obtain ⟨w', hw', h3, h4⟩ := F.cornerUnit_inv hw
  ext g
  constructor
  · rintro ⟨u₁, w₁, hu₁, hw₁, rfl⟩
    exact ⟨u₁ * u, w * w₁, F.cornerUnit_mul hu₁ hu, F.cornerUnit_mul hw hw₁, by simp only [mul_assoc]⟩
  · rintro ⟨u₁, w₁, hu₁, hw₁, rfl⟩
    refine ⟨u₁ * u', w' * w₁, F.cornerUnit_mul hu₁ hu', F.cornerUnit_mul hw' hw₁, ?_⟩
    calc u₁ * f * w₁ = u₁ * (F.e x * f * F.e y) * w₁ := by
          rw [F.e_mul_of_mem hf, F.mul_e_of_mem hf]
      _ = u₁ * (u' * u * f * (w * w')) * w₁ := by rw [h2, h3]
      _ = u₁ * u' * (u * f * w) * (w' * w₁) := by simp only [mul_assoc]

theorem ne_zero_of_mem_ray {x y : Fin F.m} {f g : A} (hf : f ∈ F.corner (k := k) x y)
    (hf0 : f ≠ 0) (hg : g ∈ F.ray (k := k) x y f) : g ≠ 0 := by
  rintro rfl
  have := F.mem_ray_self hf
  rw [← F.ray_eq_of_mem hf hg] at this
  obtain ⟨u, w, -, -, h⟩ := this
  exact hf0 (by rw [h, mul_zero, zero_mul])

/-! ### Cyclic subbimodules -/

theorem endpointSpan_le {x y : Fin F.m} {N : Submodule k A} (hN : F.IsEndpointSubbimodule x y N)
    {g : A} (hg : g ∈ N) : F.endpointSpan (k := k) x y g ≤ N :=
  Submodule.span_le.2 (by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hN.2.2 b hb _ (hN.2.1 a ha g hg))

theorem endpointRadical_le {x y : Fin F.m} {g : A} (hg : g ∈ F.corner (k := k) x y) :
    F.endpointRadical (k := k) x y g ≤
      F.cornerRadical (k := k) x * F.endpointSpan (k := k) x y g ⊔
        F.endpointSpan (k := k) x y g * F.cornerRadical (k := k) y := by
  refine Submodule.span_le.2 ?_
  rintro _ (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
  · rw [mul_assoc]
    refine Submodule.mem_sup_left (Submodule.mul_mem_mul ha (Submodule.subset_span ?_))
    exact ⟨F.e x, F.e_mem_corner x, b, hb, by rw [F.e_mul_of_mem hg]⟩
  · refine Submodule.mem_sup_right (Submodule.mul_mem_mul (Submodule.subset_span ?_) hb)
    exact ⟨a, ha, F.e y, F.e_mem_corner y, by rw [mul_assoc a g, F.mul_e_of_mem hg]⟩

/-- **`f ∉ R(f)`** for `f ≠ 0`, by Nakayama's lemma. -/
theorem not_mem_endpointRadical {x y : Fin F.m} {g : A} (hg : g ∈ F.corner (k := k) x y)
    (hg0 : g ≠ 0) : g ∉ F.endpointRadical (k := k) x y g := by
  intro hgR
  have hUR : F.endpointSpan (k := k) x y g ≤ F.endpointRadical (k := k) x y g := by
    rw [F.endpointSpan_eq hg]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hgR) le_rfl
  have := F.le_of_le_rad (x := x) (y := y) (L := ⊥) (by rw [Submodule.mul_bot])
    (by rw [Submodule.bot_mul]) (hUR.trans ((F.endpointRadical_le hg).trans le_sup_left))
  exact hg0 ((Submodule.mem_bot k).1 (this (F.mem_endpointSpan_self hg)))

/-- **`R(f)` is the unique maximal subbimodule of `U(f)`.** -/
theorem le_endpointRadical (hA : IsRepresentationFinite k A) {x y : Fin F.m} {g : A}
    (hg : g ∈ F.corner (k := k) x y) {N : Submodule k A} (hN : F.IsEndpointSubbimodule x y N)
    (hNU : N ≤ F.endpointSpan (k := k) x y g) (hgN : g ∉ N) :
    N ≤ F.endpointRadical (k := k) x y g := by
  rcases (F.isChain_subbimodules hA x y).total hN (F.isEndpoint_endpointRadical hg) with h | h
  · exact h
  · by_contra hle
    obtain ⟨n, hn, hnR⟩ := SetLike.not_le_iff_exists.1 hle
    have hnU := hNU hn
    rw [F.endpointSpan_eq hg] at hnU
    obtain ⟨v, hv, r, hr, hvr⟩ := Submodule.mem_sup.1 hnU
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hvr
      exact hnR (hvr ▸ hr)
    apply hgN
    have : g = c⁻¹ • n - c⁻¹ • r := by
      rw [← hvr, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel_right]
    rw [this]
    exact N.sub_mem (N.smul_mem _ hn) (N.smul_mem _ (h hr))

/-- **`[f] = U(f) ∖ R(f)`** (`eq:ray-layer`). -/
theorem mem_ray_iff (hA : IsRepresentationFinite k A) {x y : Fin F.m} {f : A}
    (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0) (g : A) :
    g ∈ F.ray (k := k) x y f ↔
      g ∈ F.endpointSpan (k := k) x y f ∧ g ∉ F.endpointRadical (k := k) x y f := by
  have hR := F.isEndpoint_endpointRadical hf
  constructor
  · rintro ⟨u, w, hu, hw, rfl⟩
    refine ⟨Submodule.subset_span ⟨u, hu.1, w, hw.1, rfl⟩, fun hgR ↦ ?_⟩
    obtain ⟨u', hu', h1, h2⟩ := F.cornerUnit_inv hu
    obtain ⟨w', hw', h3, h4⟩ := F.cornerUnit_inv hw
    apply F.not_mem_endpointRadical hf hf0
    have := hR.2.2 w' hw'.1 _ (hR.2.1 u' hu'.1 _ hgR)
    have hfeq : f = u' * (u * f * w) * w' := by
      calc f = (u' * u) * f * (w * w') := by rw [h2, h3, F.e_mul_of_mem hf, F.mul_e_of_mem hf]
        _ = u' * (u * f * w) * w' := by simp only [mul_assoc]
    rwa [← hfeq] at this
  · rintro ⟨hgU, hgR⟩
    rcases F.endpointSpan_one_sided hA hf with h | h
    · obtain ⟨a, ha, rfl⟩ := F.exists_of_mem_span_left (h ▸ hgU)
      have ha' : a ∉ F.cornerRadical (k := k) x := fun haR ↦ hgR (Submodule.subset_span
        (Or.inl ⟨a, haR, F.e y, F.e_mem_corner y, by rw [mul_assoc, F.mul_e_of_mem hf]⟩))
      exact ⟨a, F.e y, F.isCornerUnit_of_not_mem ha ha', F.isCornerUnit_e y, by
        rw [mul_assoc, F.mul_e_of_mem hf]⟩
    · obtain ⟨b, hb, rfl⟩ := F.exists_of_mem_span_right (h ▸ hgU)
      have hb' : b ∉ F.cornerRadical (k := k) y := fun hbR ↦ hgR (Submodule.subset_span
        (Or.inr ⟨F.e x, F.e_mem_corner x, b, hbR, by rw [F.e_mul_of_mem hf]⟩))
      exact ⟨F.e x, b, F.isCornerUnit_e x, F.isCornerUnit_of_not_mem hb hb', by
        rw [F.e_mul_of_mem hf]⟩

/-- **A ray is determined by its subbimodule.** -/
theorem ray_eq_of_endpointSpan_eq (hA : IsRepresentationFinite k A) {x y : Fin F.m} {f g : A}
    (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0) (hg : g ∈ F.corner (k := k) x y)
    (h : F.endpointSpan (k := k) x y g = F.endpointSpan (k := k) x y f) :
    F.ray (k := k) x y g = F.ray (k := k) x y f := by
  refine F.ray_eq_of_mem hf ((F.mem_ray_iff hA hf hf0 g).2 ⟨h ▸ F.mem_endpointSpan_self hg, ?_⟩)
  intro hgR
  have := F.endpointSpan_le (F.isEndpoint_endpointRadical hf) hgR
  rw [h] at this
  exact F.not_mem_endpointRadical hf hf0 (this (F.mem_endpointSpan_self hf))

theorem endpointSpan_eq_of_mem_ray {x y : Fin F.m} {f g : A} (hf : f ∈ F.corner (k := k) x y)
    (hg : g ∈ F.ray (k := k) x y f) :
    F.endpointSpan (k := k) x y g = F.endpointSpan (k := k) x y f := by
  have hU := F.isEndpoint_endpointSpan hf
  obtain ⟨u, w, hu, hw, rfl⟩ := hg
  refine le_antisymm (F.endpointSpan_le hU (Submodule.subset_span ⟨u, hu.1, w, hw.1, rfl⟩)) ?_
  obtain ⟨u', hu', h1, h2⟩ := F.cornerUnit_inv hu
  obtain ⟨w', hw', h3, h4⟩ := F.cornerUnit_inv hw
  refine F.endpointSpan_le (F.isEndpoint_endpointSpan (F.ray_subset_corner hf
    ⟨u, w, hu, hw, rfl⟩)) (Submodule.subset_span ⟨u', hu'.1, w', hw'.1, ?_⟩)
  calc f = (u' * u) * f * (w * w') := by rw [h2, h3, F.e_mul_of_mem hf, F.mul_e_of_mem hf]
    _ = u' * (u * f * w) * w' := by simp only [mul_assoc]

/-- **Every nonzero subbimodule is cyclic**: `N = U(g)`, `g` taken outside the
largest subbimodule below `N`. -/
theorem exists_cyclic (hA : IsRepresentationFinite k A) {x y : Fin F.m} {N : Submodule k A}
    (hN : F.IsEndpointSubbimodule x y N) (hN0 : N ≠ ⊥) :
    ∃ g ∈ N, g ≠ 0 ∧ N = F.endpointSpan (k := k) x y g := by
  set S := {M : Submodule k A | F.IsEndpointSubbimodule x y M ∧ M < N}
  have hfin : S.Finite := (F.finite_subbimodules hA x y).subset fun M hM ↦ hM.1
  have hbot : F.IsEndpointSubbimodule x y ⊥ :=
    ⟨bot_le, fun _ _ n hn ↦ by rw [(Submodule.mem_bot k).1 hn, mul_zero]; exact Submodule.zero_mem _,
      fun _ _ n hn ↦ by rw [(Submodule.mem_bot k).1 hn, zero_mul]; exact Submodule.zero_mem _⟩
  obtain ⟨M, hM⟩ := hfin.exists_maximal ⟨⊥, hbot, bot_lt_iff_ne_bot.2 hN0⟩
  obtain ⟨g, hgN, hgM⟩ := SetLike.exists_of_lt hM.1.2
  have hg0 : g ≠ 0 := fun h ↦ hgM (h ▸ Submodule.zero_mem _)
  have hgC := hN.1 hgN
  have hU := F.isEndpoint_endpointSpan hgC
  have hUN := F.endpointSpan_le hN hgN
  refine ⟨g, hgN, hg0, (le_antisymm hUN ?_).symm⟩
  by_contra hNU
  have hlt : F.endpointSpan (k := k) x y g < N := lt_of_le_of_ne hUN fun h ↦ hNU (h ▸ le_rfl)
  rcases (F.isChain_subbimodules hA x y).total hU hM.1.1 with h | h
  · exact hgM (h (F.mem_endpointSpan_self hgC))
  · have := hM.2 ⟨hU, hlt⟩ h
    exact hgM (this (F.mem_endpointSpan_self hgC))

/-! ### Ray transversals -/

theorem corner_unique {x y x' y' : Fin F.m} {f : A} (hf : f ∈ F.corner (k := k) x y)
    (hf' : f ∈ F.corner (k := k) x' y') (hf0 : f ≠ 0) : x = x' ∧ y = y' := by
  constructor
  · by_contra h
    apply hf0
    rw [← F.e_mul_of_mem hf, ← F.e_mul_of_mem hf', ← mul_assoc, F.complete.ortho h, zero_mul]
  · by_contra h
    apply hf0
    rw [← F.mul_e_of_mem hf, ← F.mul_e_of_mem hf', mul_assoc, F.complete.ortho (Ne.symm h), mul_zero]

open Classical in
theorem proj_corner_of_mem {x y x' y' : Fin F.m} {f : A} (hf : f ∈ F.corner (k := k) x' y') :
    F.e x * f * F.e y = if f ∈ F.corner (k := k) x y then f else 0 := by
  split_ifs with h
  · exact (F.mem_corner_iff').1 h
  · by_cases hx : x = x'
    · subst hx
      have hy : y ≠ y' := fun hy ↦ h (hy ▸ hf)
      rw [← F.mul_e_of_mem hf, mul_assoc, mul_assoc, F.complete.ortho hy.symm, mul_zero, mul_zero]
    · rw [← F.e_mul_of_mem hf, ← mul_assoc, F.complete.ortho hx, zero_mul, zero_mul]

variable {b : F.NonzeroRay k → A} (hb : F.IsRayTransversal b)

include hb in
theorem transversal_spec (s : F.NonzeroRay k) :
    ∃ x y, b s ∈ F.corner (k := k) x y ∧ b s ≠ 0 ∧ s.1 = F.ray (k := k) x y (b s) := by
  obtain ⟨x, y, f, hf, hf0, hs⟩ := s.2
  have hbs := hb.1 s
  rw [hs] at hbs
  exact ⟨x, y, F.ray_subset_corner hf hbs, F.ne_zero_of_mem_ray hf hf0 hbs,
    hs.trans (F.ray_eq_of_mem hf hbs).symm⟩

include hb in
theorem transversal_ray {x y : Fin F.m} (s : F.NonzeroRay k) (hs : b s ∈ F.corner (k := k) x y) :
    s.1 = F.ray (k := k) x y (b s) := by
  obtain ⟨x', y', hs', hs0, hray⟩ := F.transversal_spec hb s
  obtain ⟨rfl, rfl⟩ := F.corner_unique hs' hs hs0
  exact hray

include hb in
/-- **Distinct rays of a corner have distinct subbimodules.** -/
theorem transversal_ext (hA : IsRepresentationFinite k A) {x y : Fin F.m} {s s' : F.NonzeroRay k}
    (hs : b s ∈ F.corner (k := k) x y) (hs' : b s' ∈ F.corner (k := k) x y)
    (h : F.endpointSpan (k := k) x y (b s) = F.endpointSpan (k := k) x y (b s')) : s = s' := by
  obtain ⟨-, -, -, hs0, -⟩ := F.transversal_spec hb s'
  apply Subtype.ext
  rw [F.transversal_ray hb s hs, F.transversal_ray hb s' hs']
  exact F.ray_eq_of_endpointSpan_eq hA hs' hs0 hs h

include hb in
/-- **The transversal spans every subbimodule of a corner.** -/
theorem le_span_transversal (hA : IsRepresentationFinite k A) {x y : Fin F.m} :
    ∀ (n : ℕ) (N : Submodule k A), Module.finrank k N = n → F.IsEndpointSubbimodule x y N →
      N ≤ Submodule.span k (b '' {s | b s ∈ N}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hN
  by_cases hN0 : N = ⊥
  · rw [hN0]; exact bot_le
  obtain ⟨g, hgN, hg0, hNU⟩ := F.exists_cyclic hA hN hN0
  have hgC := hN.1 hgN
  set R := F.endpointRadical (k := k) x y g
  have hRU : R ≤ F.endpointSpan (k := k) x y g := by
    rw [F.endpointSpan_eq hgC]; exact le_sup_right
  have hRN : R < N := by
    rw [hNU]
    exact lt_of_le_of_ne hRU fun h ↦ F.not_mem_endpointRadical hgC hg0
      (by change g ∈ R; rw [h]; exact F.mem_endpointSpan_self hgC)
  have hspanR : R ≤ Submodule.span k (b '' {s | b s ∈ N}) :=
    (ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hRN) R rfl
      (F.isEndpoint_endpointRadical hgC)).trans
      (Submodule.span_mono (Set.image_mono fun s hs ↦ hRN.le hs))
  let s : F.NonzeroRay k := ⟨F.ray (k := k) x y g, x, y, g, hgC, hg0, rfl⟩
  obtain ⟨hbU, hbR⟩ := (F.mem_ray_iff hA hgC hg0 (b s)).1 (hb.1 s)
  have hbN : b s ∈ N := hNU ▸ hbU
  have hbU' := hbU
  rw [F.endpointSpan_eq hgC] at hbU'
  obtain ⟨v, hv, r, hr, hvr⟩ := Submodule.mem_sup.1 hbU'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hvr
    exact hbR (hvr ▸ hr)
  have hg : g ∈ Submodule.span k (b '' {s | b s ∈ N}) := by
    have : g = c⁻¹ • b s - c⁻¹ • r := by
      rw [← hvr, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hbN, rfl⟩))
      (Submodule.smul_mem _ _ (hspanR hr))
  calc N = F.endpointSpan (k := k) x y g := hNU
    _ = (k ∙ g) ⊔ R := F.endpointSpan_eq hgC
    _ ≤ _ := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hg) hspanR

theorem eq_sum_corners (a : A) : a = ∑ x, ∑ y, F.e x * a * F.e y := by
  calc a = (∑ x, F.e x) * a * (∑ y, F.e y) := by rw [F.complete.complete, one_mul, mul_one]
    _ = ∑ x, ∑ y, F.e x * a * F.e y := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.mul_sum]

theorem corner_isEndpoint (x y : Fin F.m) : F.IsEndpointSubbimodule x y (F.corner (k := k) x y) :=
  ⟨le_rfl, fun _ ha _ hn ↦ F.corner_mul_corner ha hn, fun _ hb _ hn ↦ F.corner_mul_corner hn hb⟩

theorem eAe_mem_corner (x y : Fin F.m) (a : A) : F.e x * a * F.e y ∈ F.corner (k := k) x y :=
  ⟨a, by change F.e x * (a * F.e y) = _; rw [mul_assoc]⟩

include hb in
theorem span_transversal (hA : IsRepresentationFinite k A) :
    Submodule.span k (Set.range b) = ⊤ := by
  refine eq_top_iff.2 fun a _ ↦ ?_
  rw [F.eq_sum_corners a]
  refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
  exact Submodule.span_mono (Set.image_subset_range _ _)
    (F.le_span_transversal hb hA _ _ rfl (F.corner_isEndpoint x y) (F.eAe_mem_corner x y a))

include hb in
theorem linearIndependent_transversal (hA : IsRepresentationFinite k A) :
    LinearIndependent k b := by
  classical
  refine linearIndependent_iff'.2 fun S g hsum s₀ hs₀ ↦ ?_
  by_contra hg₀
  obtain ⟨x, y, hx, -, -⟩ := F.transversal_spec hb s₀
  set T := S.filter fun s ↦ g s ≠ 0 ∧ b s ∈ F.corner (k := k) x y
  have hT : (T.image fun s ↦ F.endpointSpan (k := k) x y (b s) : Set (Submodule k A)).Nonempty :=
    ⟨_, Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hs₀, hg₀, hx⟩))⟩
  obtain ⟨M, hM⟩ := (T.image fun s ↦ F.endpointSpan (k := k) x y (b s)).finite_toSet.exists_maximal hT
  obtain ⟨s₁, hs₁T, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hM.1)
  obtain ⟨hs₁S, hg₁, hs₁⟩ := Finset.mem_filter.1 hs₁T
  obtain ⟨-, -, -, hs₁0, -⟩ := F.transversal_spec hb s₁
  -- the corner part of the relation
  have hproj : ∑ s ∈ S.filter fun s ↦ b s ∈ F.corner (k := k) x y, g s • b s = 0 := by
    have h2 : ∀ s ∈ S, F.e x * (g s • b s) * F.e y =
        if b s ∈ F.corner (k := k) x y then g s • b s else 0 := by
      intro s _
      obtain ⟨x', y', hs', -, -⟩ := F.transversal_spec hb s
      rw [mul_smul_comm, smul_mul_assoc, F.proj_corner_of_mem hs', smul_ite, smul_zero]
    have := congrArg (fun z ↦ F.e x * z * F.e y) hsum
    rw [Finset.mul_sum, Finset.sum_mul, mul_zero, zero_mul, Finset.sum_congr rfl h2,
      ← Finset.sum_filter] at this
    exact this
  have hmem : s₁ ∈ S.filter fun s ↦ b s ∈ F.corner (k := k) x y := Finset.mem_filter.2 ⟨hs₁S, hs₁⟩
  rw [← Finset.add_sum_erase _ _ hmem] at hproj
  have hrest : ∑ s ∈ (S.filter fun s ↦ b s ∈ F.corner (k := k) x y).erase s₁, g s • b s ∈
      F.endpointRadical (k := k) x y (b s₁) := by
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨hss₁, hs⟩ := Finset.mem_erase.1 hs
    obtain ⟨hsS, hsC⟩ := Finset.mem_filter.1 hs
    by_cases hgs : g s = 0
    · rw [hgs, zero_smul]; exact Submodule.zero_mem _
    refine Submodule.smul_mem _ _ ?_
    have hsT : s ∈ T := Finset.mem_filter.2 ⟨hsS, hgs, hsC⟩
    have hU := F.isEndpoint_endpointSpan hsC
    have hU₁ := F.isEndpoint_endpointSpan hs₁
    have hle : F.endpointSpan (k := k) x y (b s) ≤ F.endpointSpan (k := k) x y (b s₁) := by
      rcases (F.isChain_subbimodules hA x y).total hU hU₁ with h | h
      · exact h
      · exact hM.2 (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hsT)) h
    have hnot : b s₁ ∉ F.endpointSpan (k := k) x y (b s) := fun h ↦
      hss₁ (F.transversal_ext hb hA hsC hs₁ (le_antisymm hle (F.endpointSpan_le hU h)))
    exact F.le_endpointRadical hA hs₁ hU hle hnot (F.mem_endpointSpan_self hsC)
  have h1 : g s₁ • b s₁ ∈ F.endpointRadical (k := k) x y (b s₁) := by
    have : g s₁ • b s₁ = -∑ s ∈ (S.filter fun s ↦ b s ∈ F.corner (k := k) x y).erase s₁,
        g s • b s := eq_neg_of_add_eq_zero_left hproj
    rw [this]
    exact Submodule.neg_mem _ hrest
  apply F.not_mem_endpointRadical hs₁ hs₁0
  have := Submodule.smul_mem _ (g s₁)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hg₁, one_smul] at this

/-- A two-sided ideal as a `k`-subspace. -/
def idealSubmodule (I : TwoSidedIdeal A) : Submodule k A where
  carrier := I
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' c z hz := by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ hz

include hb in
/-- **Corollary 3.3.** -/
theorem rayTransversal_isBasis (hA : IsRepresentationFinite k A) :
    LinearIndependent k b ∧ Submodule.span k (Set.range b) = ⊤ ∧
      ∀ I : TwoSidedIdeal A, ∀ a : A, a ∈ I ↔ a ∈ Submodule.span k (b '' {r | b r ∈ I}) := by
  refine ⟨F.linearIndependent_transversal hb hA, F.span_transversal hb hA, fun I a ↦ ⟨fun ha ↦ ?_,
    fun ha ↦ ?_⟩⟩
  · set Iₛ := idealSubmodule (k := k) I
    rw [F.eq_sum_corners a]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
    have hN : F.IsEndpointSubbimodule x y (F.corner (k := k) x y ⊓ Iₛ) :=
      ⟨inf_le_left, fun c hc n hn ↦ ⟨F.corner_mul_corner hc hn.1, I.mul_mem_left _ _ hn.2⟩,
        fun c hc n hn ↦ ⟨F.corner_mul_corner hn.1 hc, I.mul_mem_right _ _ hn.2⟩⟩
    have hmem : F.e x * a * F.e y ∈ F.corner (k := k) x y ⊓ Iₛ :=
      ⟨F.eAe_mem_corner x y a, I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)⟩
    exact Submodule.span_mono (Set.image_mono fun s hs ↦ hs.2)
      (F.le_span_transversal hb hA _ _ rfl hN hmem)
  · have : Submodule.span k (b '' {r | b r ∈ I}) ≤ idealSubmodule (k := k) I :=
      Submodule.span_le.2 (by rintro _ ⟨r, hr, rfl⟩; exact hr)
    exact this ha

end PrimitiveIdempotents

end MultiplicativeBasisDeformations
