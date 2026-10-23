module

public import MultiplicativeBasisDeformations.Foundations.BinaryNormalization

/-!
# Character decomposition of Hochschild cochains

`weights-and-parameters.tex`: "Integer ray weights also grade `A₀` and its
Hochschild complex, and we write `HH²(A₀)_χ` for the component of weight `χ ∈ L`. Since
`deg_J ∈ H_ℤ`, this decomposition refines the decomposition by internal degree."

For an algebra `Λ` with a length grading `G`, vertex idempotents of weight zero and a
compatible lattice grading `W`: the character-`χ` part `cpr2 χ φ` of a two-cochain is a
cochain of character `χ`; it is a cocycle, relative, of the same internal degree when
`φ` is, and `φ` is the finite sum of its character parts (`sum_cpr2`). The coboundary
commutes with the character parts (`cobdry_cpr1`).

Also (`exists_rel_cobdry`): "Inserting the primitive idempotents contracts the
complementary summands of the bar complex, so these relative cochains compute ordinary
Hochschild cohomology" (`weights-and-parameters.tex`), in the form used: a
normalized relative cocycle which is the coboundary of some one-cochain of degree `q` is
the coboundary of a normalized relative one-cochain of degree `q`. The correction is the
inner derivation of `u = ∑ f(e_j) e_j`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace LatGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {L : Type} [AddCommGroup L]
  [DecidableEq L] (W : LatGrading k Λ L)

theorem isHom_zero (l : L) : W.IsHom l (0 : Λ) := by unfold IsHom; rw [map_zero]

theorem isHom_add {l : L} {x y : Λ} (hx : W.IsHom l x) (hy : W.IsHom l y) : W.IsHom l (x + y) := by
  unfold IsHom; rw [map_add, hx, hy]

theorem isHom_smul {l : L} (c : k) {x : Λ} (hx : W.IsHom l x) : W.IsHom l (c • x) := by
  unfold IsHom; rw [map_smul, hx]

theorem isHom_sub {l : L} {x y : Λ} (hx : W.IsHom l x) (hy : W.IsHom l y) : W.IsHom l (x - y) := by
  unfold IsHom; rw [map_sub, hx, hy]

theorem isHom_sum {l : L} {ι : Type*} (s : Finset ι) (f : ι → Λ) (h : ∀ i ∈ s, W.IsHom l (f i)) :
    W.IsHom l (∑ i ∈ s, f i) := by
  unfold IsHom; rw [map_sum]; exact Finset.sum_congr rfl h

theorem eq_zero_of_isHom_out {l : L} {x : Λ} (hx : W.IsHom l x) (hl : l ∉ W.supp) : x = 0 := by
  rw [← hx, W.proj_out l hl, LinearMap.zero_apply]

/-- Additive maps commute with the weight decomposition. -/
theorem map_eq_sum {N : Type*} [AddCommGroup N] (f : Λ →+ N) (x : Λ) :
    f x = ∑ l ∈ W.supp, f (W.proj l x) := by
  conv_lhs => rw [W.sum x]
  rw [map_sum]

theorem proj_mul_left {l : L} {x : Λ} (hx : W.IsHom l x) (l' : L) (y : Λ) :
    W.proj (l + l') (x * y) = x * W.proj l' y := by
  conv_lhs => rw [W.sum y, Finset.mul_sum, map_sum]
  have : ∀ l'' ∈ W.supp, W.proj (l + l') (x * W.proj l'' y) =
      if l'' = l' then x * W.proj l'' y else 0 := fun l'' _ ↦ by
    rw [W.proj_of_isHom (W.isHom_mul hx (W.isHom_proj l'' y))]
    simp only [add_right_inj]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [W.proj_out l' h, LinearMap.zero_apply, mul_zero]

theorem proj_mul_right {l : L} {y : Λ} (hy : W.IsHom l y) (l' : L) (x : Λ) :
    W.proj (l' + l) (x * y) = W.proj l' x * y := by
  conv_lhs => rw [W.sum x, Finset.sum_mul, map_sum]
  have : ∀ l'' ∈ W.supp, W.proj (l' + l) (W.proj l'' x * y) =
      if l'' = l' then W.proj l'' x * y else 0 := fun l'' _ ↦ by
    rw [W.proj_of_isHom (W.isHom_mul (W.isHom_proj l'' x) hy)]
    simp only [add_left_inj]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [W.proj_out l' h, LinearMap.zero_apply, zero_mul]

/-- Linear maps agreeing on homogeneous elements agree. -/
theorem ext_of_hom {N : Type*} [AddCommGroup N] [Module k N] {f f' : Λ →ₗ[k] N}
    (h : ∀ l x, W.IsHom l x → f x = f' x) : f = f' := by
  ext x
  rw [W.sum x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ h l _ (W.isHom_proj l x)

/-- A function additive in each of three arguments vanishes if it vanishes on homogeneous
arguments. -/
theorem eq_zero_of_hom3 {N : Type*} [AddCommGroup N] (E : Λ → Λ → Λ → N)
    (h1 : ∀ a a' b c, E (a + a') b c = E a b c + E a' b c)
    (h2 : ∀ a b b' c, E a (b + b') c = E a b c + E a b' c)
    (h3 : ∀ a b c c', E a b (c + c') = E a b c + E a b c')
    (hh : ∀ α β γ a b c, W.IsHom α a → W.IsHom β b → W.IsHom γ c → E a b c = 0) (a b c : Λ) :
    E a b c = 0 := by
  have k1 := W.map_eq_sum (AddMonoidHom.mk' (fun a ↦ E a b c) fun a a' ↦ h1 a a' b c) a
  simp only [AddMonoidHom.mk'_apply] at k1
  rw [k1]
  refine Finset.sum_eq_zero fun α _ ↦ ?_
  have k2 := W.map_eq_sum (AddMonoidHom.mk' (fun b ↦ E (W.proj α a) b c) fun b b' ↦ h2 _ b b' c) b
  simp only [AddMonoidHom.mk'_apply] at k2
  rw [k2]
  refine Finset.sum_eq_zero fun β _ ↦ ?_
  have k3 := W.map_eq_sum
    (AddMonoidHom.mk' (fun c ↦ E (W.proj α a) (W.proj β b) c) fun c c' ↦ h3 _ _ c c') c
  simp only [AddMonoidHom.mk'_apply] at k3
  rw [k3]
  refine Finset.sum_eq_zero fun γ _ ↦ ?_
  exact hh α β γ _ _ _ (W.isHom_proj α a) (W.isHom_proj β b) (W.isHom_proj γ c)

/-- Bilinear maps agreeing on homogeneous pairs agree. -/
theorem ext2_of_hom {f f' : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (h : ∀ α β a b, W.IsHom α a → W.IsHom β b → f a b = f' a b) : f = f' :=
  W.ext_of_hom fun α a ha ↦ W.ext_of_hom fun β b hb ↦ h α β a b ha hb

/-! ### Characters of cochains -/

/-- A two-cochain of character `χ`. -/
def Char₂ (χ : L) (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop :=
  ∀ α β a b, W.IsHom α a → W.IsHom β b → W.IsHom (α + β + χ) (φ a b)

/-- A one-cochain of character `χ`. -/
def Char₁ (χ : L) (f : Λ →ₗ[k] Λ) : Prop := ∀ α a, W.IsHom α a → W.IsHom (α + χ) (f a)

/-- The character-`χ` part of a two-cochain. -/
def cpr2 (χ : L) (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  ∑ α ∈ W.supp, ∑ β ∈ W.supp, ((φ.comp (W.proj α)).compl₂ (W.proj β)).compr₂ (W.proj (α + β + χ))

/-- The character-`χ` part of a one-cochain. -/
def cpr1 (χ : L) (f : Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ :=
  ∑ α ∈ W.supp, W.proj (α + χ) ∘ₗ f ∘ₗ W.proj α

theorem cpr1_hom (χ : L) (f : Λ →ₗ[k] Λ) {α : L} {a : Λ} (ha : W.IsHom α a) :
    W.cpr1 χ f a = W.proj (α + χ) (f a) := by
  simp only [cpr1, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  by_cases hα : α ∈ W.supp
  · rw [Finset.sum_eq_single α (fun β _ hβ ↦ by
      rw [W.proj_of_isHom ha, if_neg (Ne.symm hβ), map_zero, map_zero]) (fun h ↦ absurd hα h), ha]
  · rw [W.eq_zero_of_isHom_out ha hα]; simp

theorem cpr2_hom (χ : L) (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) {α β : L} {a b : Λ} (ha : W.IsHom α a)
    (hb : W.IsHom β b) : W.cpr2 χ φ a b = W.proj (α + β + χ) (φ a b) := by
  by_cases hα : α ∈ W.supp
  swap
  · rw [W.eq_zero_of_isHom_out ha hα]; simp
  by_cases hβ : β ∈ W.supp
  swap
  · rw [W.eq_zero_of_isHom_out hb hβ]; simp
  simp only [cpr2, LinearMap.coe_sum, Finset.sum_apply, LinearMap.compr₂_apply,
    LinearMap.compl₂_apply, LinearMap.comp_apply]
  rw [Finset.sum_eq_single α]
  · rw [Finset.sum_eq_single β]
    · rw [ha, hb]
    · intro β' _ hβ'
      rw [W.proj_of_isHom hb, if_neg (Ne.symm hβ'), map_zero, map_zero]
    · intro h; exact absurd hβ h
  · intro α' _ hα'
    refine Finset.sum_eq_zero fun β' _ ↦ ?_
    rw [W.proj_of_isHom ha, if_neg (Ne.symm hα'), map_zero, LinearMap.zero_apply, map_zero]
  · intro h; exact absurd hα h

theorem char₂_cpr2 (χ : L) (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) : W.Char₂ χ (W.cpr2 χ φ) :=
  fun α β a b ha hb ↦ by rw [W.cpr2_hom χ φ ha hb]; exact W.isHom_proj _ _

theorem cpr2_of_char₂ {χ : L} {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (h : W.Char₂ χ φ) : W.cpr2 χ φ = φ :=
  W.ext2_of_hom fun α β a b ha hb ↦ by rw [W.cpr2_hom χ φ ha hb, h α β a b ha hb]

/-- The characters which can occur. -/
def chars : Finset L :=
  ((W.supp ×ˢ W.supp) ×ˢ W.supp).image fun t ↦ t.2 - t.1.1 - t.1.2

/-- **A two-cochain is the sum of its character parts.** -/
theorem sum_cpr2 (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) : φ = ∑ χ ∈ W.chars, W.cpr2 χ φ := by
  refine W.ext2_of_hom fun α β a b ha hb ↦ ?_
  rw [LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_sum, Finset.sum_apply]
  simp only [W.cpr2_hom _ φ ha hb]
  by_cases hα : α ∈ W.supp
  swap
  · rw [W.eq_zero_of_isHom_out ha hα]; simp
  by_cases hβ : β ∈ W.supp
  swap
  · rw [W.eq_zero_of_isHom_out hb hβ]; simp
  have hinj : Set.InjOn (fun χ ↦ α + β + χ) W.chars := fun χ _ χ' _ h ↦ by simpa using h
  rw [← Finset.sum_image (f := fun γ ↦ W.proj γ (φ a b)) hinj]
  conv_lhs => rw [W.sum (φ a b)]
  refine Finset.sum_subset (fun γ hγ ↦ Finset.mem_image.2 ⟨γ - α - β, Finset.mem_image.2
    ⟨((α, β), γ), Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hα, hβ⟩, hγ⟩, by abel⟩, by abel⟩)
    fun γ _ hγ ↦ by rw [W.proj_out γ hγ, LinearMap.zero_apply]

variable {G : LenGrading k Λ} (V : LenGrading.Vertices G)
  (compat : ∀ d l x, G.proj d (W.proj l x) = W.proj l (G.proj d x))
  (he0 : ∀ i, W.IsHom 0 (V.e i))

include compat in
theorem proj_isHomLen {d : ℕ} {l : L} {x : Λ} (hx : G.IsHom d x) : G.IsHom d (W.proj l x) := by
  unfold LenGrading.IsHom; rw [compat, hx]

include compat in
theorem hasDeg₂_cpr2 {q : ℕ} {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : LenGrading.HasDeg₂ G q φ) (χ : L) :
    LenGrading.HasDeg₂ G q (W.cpr2 χ φ) := fun d e a b ha hb ↦ by
  simp only [cpr2, LinearMap.coe_sum, Finset.sum_apply, LinearMap.compr₂_apply,
    LinearMap.compl₂_apply, LinearMap.comp_apply]
  refine G.isHom_sum _ _ fun α _ ↦ G.isHom_sum _ _ fun β _ ↦ ?_
  exact W.proj_isHomLen compat (hφ d e _ _ (W.proj_isHomLen compat ha) (W.proj_isHomLen compat hb))

include compat in
theorem hasDeg₁_cpr1 {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : LenGrading.HasDeg₁ G q f) (χ : L) :
    LenGrading.HasDeg₁ G q (W.cpr1 χ f) := fun d a ha ↦ by
  simp only [cpr1, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  exact G.isHom_sum _ _ fun α _ ↦ W.proj_isHomLen compat (hf d _ (W.proj_isHomLen compat ha))

theorem isCocycle₂_cpr2 {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : LenGrading.IsCocycle₂ φ) (χ : L) :
    LenGrading.IsCocycle₂ (W.cpr2 χ φ) := by
  intro a b c
  refine W.eq_zero_of_hom3 (fun a b c ↦ a * W.cpr2 χ φ b c - W.cpr2 χ φ (a * b) c +
    W.cpr2 χ φ a (b * c) - W.cpr2 χ φ a b * c) (fun a a' b c ↦ ?_) (fun a b b' c ↦ ?_)
    (fun a b c c' ↦ ?_) (fun α β γ a b c ha hb hc ↦ ?_) a b c
  · simp only [add_mul, map_add, LinearMap.add_apply]; abel
  · simp only [mul_add, add_mul, map_add, LinearMap.add_apply]; abel
  · simp only [mul_add, map_add]; abel
  · have hab := W.isHom_mul ha hb
    have hbc := W.isHom_mul hb hc
    rw [W.cpr2_hom χ φ hb hc, W.cpr2_hom χ φ hab hc, W.cpr2_hom χ φ ha hbc, W.cpr2_hom χ φ ha hb,
      ← W.proj_mul_left ha, ← W.proj_mul_right hc]
    rw [show α + (β + γ + χ) = α + β + γ + χ by abel, show α + (β + γ) + χ = α + β + γ + χ by abel,
      show α + β + χ + γ = α + β + γ + χ by abel, ← map_sub, ← map_add, ← map_sub, hφ a b c,
      map_zero]

theorem cobdry_cpr1 (f : Λ →ₗ[k] Λ) (χ : L) :
    LenGrading.cobdry k (W.cpr1 χ f) = W.cpr2 χ (LenGrading.cobdry k f) := by
  refine W.ext2_of_hom fun α β a b ha hb ↦ ?_
  rw [W.cpr2_hom χ _ ha hb, LenGrading.cobdry_apply, LenGrading.cobdry_apply,
    W.cpr1_hom χ f hb, W.cpr1_hom χ f (W.isHom_mul ha hb), W.cpr1_hom χ f ha,
    ← W.proj_mul_left ha, ← W.proj_mul_right hb, map_add, map_sub]
  rw [show α + (β + χ) = α + β + χ by abel, show α + χ + β = α + β + χ by abel]

include he0 in
theorem isRel₂_cpr2 {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : LenGrading.IsRel₂ V φ) (χ : L) :
    LenGrading.IsRel₂ V (W.cpr2 χ φ) := by
  refine ⟨fun i a b ↦ ?_, fun i a b ↦ ?_, fun i a b ↦ ?_, fun i b ↦ ?_, fun i a ↦ ?_⟩
  · have := W.ext2_of_hom (f := (W.cpr2 χ φ).comp (LinearMap.mulLeft k (V.e i)))
      (f' := (W.cpr2 χ φ).compr₂ (LinearMap.mulLeft k (V.e i))) fun α β a b ha hb ↦ by
        simp only [LinearMap.comp_apply, LinearMap.compr₂_apply, LinearMap.mulLeft_apply]
        have h0 := W.isHom_mul (he0 i) ha
        rw [zero_add] at h0
        rw [W.cpr2_hom χ φ h0 hb, W.cpr2_hom χ φ ha hb, hφ.left, ← W.proj_mul_left (he0 i),
          zero_add]
    exact LinearMap.congr_fun (LinearMap.congr_fun this a) b
  · have := W.ext2_of_hom (f := (W.cpr2 χ φ).comp (LinearMap.mulRight k (V.e i)))
      (f' := (W.cpr2 χ φ).compl₂ (LinearMap.mulLeft k (V.e i))) fun α β a b ha hb ↦ by
        simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply]
        have h0 := W.isHom_mul ha (he0 i)
        have h0' := W.isHom_mul (he0 i) hb
        rw [add_zero] at h0
        rw [zero_add] at h0'
        rw [W.cpr2_hom χ φ h0 hb, W.cpr2_hom χ φ ha h0', hφ.mid]
    exact LinearMap.congr_fun (LinearMap.congr_fun this a) b
  · have := W.ext2_of_hom (f := (W.cpr2 χ φ).compl₂ (LinearMap.mulRight k (V.e i)))
      (f' := (W.cpr2 χ φ).compr₂ (LinearMap.mulRight k (V.e i))) fun α β a b ha hb ↦ by
        simp only [LinearMap.compl₂_apply, LinearMap.compr₂_apply, LinearMap.mulRight_apply]
        have h0 := W.isHom_mul hb (he0 i)
        rw [add_zero] at h0
        rw [W.cpr2_hom χ φ ha h0, W.cpr2_hom χ φ ha hb, hφ.right,
          ← W.proj_mul_right (he0 i), add_zero]
    exact LinearMap.congr_fun (LinearMap.congr_fun this a) b
  · have := W.ext_of_hom (f := W.cpr2 χ φ (V.e i)) (f' := 0) fun β b hb ↦ by
      rw [W.cpr2_hom χ φ (he0 i) hb, hφ.unitL, map_zero, LinearMap.zero_apply]
    exact LinearMap.congr_fun this b
  · have := W.ext_of_hom (f := (W.cpr2 χ φ).flip (V.e i)) (f' := 0) fun α a ha ↦ by
      rw [LinearMap.flip_apply, W.cpr2_hom χ φ ha (he0 i), hφ.unitR, map_zero, LinearMap.zero_apply]
    exact LinearMap.congr_fun this a

end LatGrading

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  (V : Vertices G)

/-- The inner derivation `a ↦ u a − a u`. -/
def innerDer (u : Λ) : Λ →ₗ[k] Λ := LinearMap.mulLeft k u - LinearMap.mulRight k u

theorem cobdry_innerDer (u : Λ) : cobdry k (innerDer (k := k) u) = 0 := by
  ext a b
  simp only [cobdry_apply, innerDer, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, LinearMap.zero_apply]
  noncomm_ring

theorem cobdry_sub (f g : Λ →ₗ[k] Λ) : cobdry k (f - g) = cobdry k f - cobdry k g := by
  ext a b
  simp only [cobdry_apply, LinearMap.sub_apply, mul_sub, sub_mul]
  abel

theorem isHom_sub' {d : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom d b) : G.IsHom d (a - b) := by
  unfold IsHom; rw [map_sub, ha, hb]

/-- **Relative coboundaries.** A normalized relative cocycle which is the coboundary of a
one-cochain of degree `q` is the coboundary of a normalized relative one-cochain of degree
`q`. -/
theorem exists_rel_cobdry {q : ℕ} {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : IsRel₂ V φ) {f : Λ →ₗ[k] Λ}
    (hf : HasDeg₁ G q f) (hφf : φ = cobdry k f) :
    ∃ f' : Λ →ₗ[k] Λ, IsRel₁ V f' ∧ HasDeg₁ G q f' ∧ φ = cobdry k f' := by
  set u := ∑ j, f (V.e j) * V.e j
  have horth := V.complete.toOrthogonalIdempotents
  have hsum : ∑ j, V.e j = 1 := V.complete.complete
  have hR : ∀ i j, V.e i * f (V.e j) = (if i = j then f (V.e i) else 0) - f (V.e i) * V.e j := by
    intro i j
    have := congrArg (fun ψ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ ψ (V.e i) (V.e j)) hφf
    simp only [hφ.unitL, cobdry_apply, horth.mul_eq] at this
    rw [apply_ite f, map_zero] at this
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    convert this.symm using 1; abel
  have hfe : ∀ i, f (V.e i) = u * V.e i - V.e i * u := by
    intro i
    have hu1 : u * V.e i = f (V.e i) * V.e i := by
      simp only [u, Finset.sum_mul, mul_assoc, horth.mul_eq]
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [if_neg hj, mul_zero])
        (fun h ↦ absurd (Finset.mem_univ i) h), if_pos rfl]
    have hu2 : V.e i * u = f (V.e i) * V.e i - f (V.e i) := by
      have : ∀ j, V.e i * (f (V.e j) * V.e j) =
          (if i = j then f (V.e i) * V.e j else 0) - f (V.e i) * V.e j := by
        intro j
        rw [← mul_assoc, hR i j, sub_mul, mul_assoc, (horth.idem j).eq, ite_mul, zero_mul]
      simp only [u]
      rw [Finset.mul_sum]
      simp_rw [this]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← Finset.mul_sum,
        hsum, mul_one]
    rw [hu1, hu2]; abel
  have hφ' : φ = cobdry k (f - innerDer (k := k) u) := by
    rw [hφf]; ext a b
    simp only [cobdry_apply, LinearMap.sub_apply, innerDer, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
    noncomm_ring
  have hunit : ∀ i, (f - innerDer (k := k) u) (V.e i) = 0 := fun i ↦ by
    simp only [LinearMap.sub_apply, innerDer, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [hfe i, sub_self]
  refine ⟨f - innerDer (k := k) u, ⟨fun i a ↦ ?_, fun i a ↦ ?_, hunit⟩, fun d a ha ↦ ?_, hφ'⟩
  · have := congrArg (fun ψ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ ψ (V.e i) a) hφ'
    simp only [hφ.unitL, cobdry_apply, hunit i, zero_mul, add_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  · have := congrArg (fun ψ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ ψ a (V.e i)) hφ'
    simp only [hφ.unitR, cobdry_apply, hunit i, mul_zero, zero_sub] at this
    exact neg_add_eq_zero.1 this.symm
  · have hu : G.IsHom q u := G.isHom_sum _ _ fun j _ ↦ by
      have := G.isHom_mul (hf 0 _ (V.deg0 j)) (V.deg0 j)
      simpa using this
    simp only [LinearMap.sub_apply, innerDer, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    refine isHom_sub' (hf d a ha) (isHom_sub' ?_ ?_)
    · have := G.isHom_mul hu ha; rwa [add_comm] at this
    · exact G.isHom_mul ha hu

section RelClosure

variable {V}

theorem IsRel₂.zero : IsRel₂ V (0 : Λ →ₗ[k] Λ →ₗ[k] Λ) :=
  ⟨fun _ _ _ ↦ by simp, fun _ _ _ ↦ by simp, fun _ _ _ ↦ by simp, fun _ _ ↦ by simp,
    fun _ _ ↦ by simp⟩

theorem IsRel₂.add {φ ψ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : IsRel₂ V φ) (hψ : IsRel₂ V ψ) :
    IsRel₂ V (φ + ψ) :=
  ⟨fun i a b ↦ by simp [hφ.left, hψ.left, mul_add], fun i a b ↦ by simp [hφ.mid, hψ.mid],
    fun i a b ↦ by simp [hφ.right, hψ.right, add_mul], fun i b ↦ by simp [hφ.unitL, hψ.unitL],
    fun i a ↦ by simp [hφ.unitR, hψ.unitR]⟩

theorem IsRel₂.smul {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : IsRel₂ V φ) (t : k) : IsRel₂ V (t • φ) :=
  ⟨fun i a b ↦ by simp [hφ.left], fun i a b ↦ by simp [hφ.mid],
    fun i a b ↦ by simp [hφ.right], fun i b ↦ by simp [hφ.unitL], fun i a ↦ by simp [hφ.unitR]⟩

theorem IsRel₂.sub {φ ψ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : IsRel₂ V φ) (hψ : IsRel₂ V ψ) :
    IsRel₂ V (φ - ψ) :=
  ⟨fun i a b ↦ by simp [hφ.left, hψ.left, mul_sub], fun i a b ↦ by simp [hφ.mid, hψ.mid],
    fun i a b ↦ by simp [hφ.right, hψ.right, sub_mul], fun i b ↦ by simp [hφ.unitL, hψ.unitL],
    fun i a ↦ by simp [hφ.unitR, hψ.unitR]⟩

theorem IsRel₂.sum {ι : Type*} (s : Finset ι) {φ : ι → Λ →ₗ[k] Λ →ₗ[k] Λ}
    (h : ∀ i ∈ s, IsRel₂ V (φ i)) : IsRel₂ V (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRel₂.zero (V := V)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end RelClosure

theorem cobdry_add (f g : Λ →ₗ[k] Λ) : cobdry k (f + g) = cobdry k f + cobdry k g := by
  ext a b
  simp only [cobdry_apply, LinearMap.add_apply, mul_add, add_mul]
  abel

theorem cobdry_zero : cobdry k (0 : Λ →ₗ[k] Λ) = 0 := by
  ext a b; simp [cobdry_apply]

theorem cobdry_sum {ι : Type*} (s : Finset ι) (f : ι → Λ →ₗ[k] Λ) :
    cobdry k (∑ i ∈ s, f i) = ∑ i ∈ s, cobdry k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cobdry_zero (k := k) (Λ := Λ)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cobdry_add, ih]

theorem hasDeg₁_sum {q : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Λ →ₗ[k] Λ}
    (h : ∀ i ∈ s, HasDeg₁ G q (f i)) : HasDeg₁ G q (∑ i ∈ s, f i) := fun d a ha ↦ by
  rw [LinearMap.coe_sum, Finset.sum_apply]
  exact G.isHom_sum _ _ fun i hi ↦ h i hi d a ha

variable {L : Type} [AddCommGroup L] [DecidableEq L] (W : LatGrading k Λ L)
  (compat : ∀ d l x, G.proj d (W.proj l x) = W.proj l (G.proj d x))
  (he0 : ∀ i, W.IsHom 0 (V.e i))

include compat he0 in
/-- **The spanning hypothesis of Theorem 7.7 from its character parts.** -/
theorem span_of_char {n : ℕ} {μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ} {qd : Fin n → ℕ}
    (hμrel : ∀ i, IsRel₂ V (μ i))
    (h : ∀ q, 0 < q → ∀ (χ : L) (φ : Λ →ₗ[k] Λ →ₗ[k] Λ), IsRel₂ V φ → HasDeg₂ G q φ →
      IsCocycle₂ φ → W.Char₂ χ φ →
      ∃ (c : Fin n → k) (f : Λ →ₗ[k] Λ), HasDeg₁ G q f ∧
        φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i) + cobdry k f) :
    ∀ q, 0 < q → ∀ φ, IsRel₂ V φ → HasDeg₂ G q φ → IsCocycle₂ φ →
      ∃ (c : Fin n → k) (f : Λ →ₗ[k] Λ), IsRel₁ V f ∧ HasDeg₁ G q f ∧
        φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i) + cobdry k f := by
  intro q hq φ hφ hφd hφc
  choose c f hfd hcf using fun χ : L ↦ h q hq χ (W.cpr2 χ φ) (W.isRel₂_cpr2 V he0 hφ χ)
    (W.hasDeg₂_cpr2 compat hφd χ) (W.isCocycle₂_cpr2 hφc χ) (W.char₂_cpr2 χ φ)
  set C : Fin n → k := fun i ↦ ∑ χ ∈ W.chars, c χ i
  set F := ∑ χ ∈ W.chars, f χ
  have hsum : φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), C i • μ i) + cobdry k F := by
    conv_lhs => rw [W.sum_cpr2 φ]
    rw [Finset.sum_congr rfl fun χ _ ↦ hcf χ, Finset.sum_add_distrib, cobdry_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_smul]
  have hrel : IsRel₂ V (φ - ∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), C i • μ i) :=
    hφ.sub (IsRel₂.sum _ fun i _ ↦ (hμrel i).smul _)
  obtain ⟨f', hf'rel, hf'd, hf'⟩ := exists_rel_cobdry V hrel (hasDeg₁_sum _ fun χ _ ↦ hfd χ)
    (by rw [hsum]; abel)
  exact ⟨C, f', hf'rel, hf'd, by rw [← hf']; abel⟩

end LenGrading

end MultiplicativeBasisDeformations
