module

public import MultiplicativeBasisDeformations.Foundations.GradedLayers

/-!
# Positive filtered deformations

Definition 6.2 (`def:positive-deformation`, `positive-deformations.tex`):
"A positive filtered deformation of a finite-dimensional nonnegatively graded
algebra `Λ` is an algebra `B` with a finite decreasing multiplicative filtration
and an identification `gr B = Λ`." The identification is recorded by the
leading-term maps `σ_d : F^d → Λ_d` (`PosFiltration`), surjective with kernel
`F^{d+1}` and multiplicative.

Lemma 6.4 (`lem:split-positive-deformation`, lines 189–233): the vertex
idempotents lift (through the nilpotent ideal `F¹`), and the filtration splits
as `S`-bimodules, giving a linear isomorphism `φ : Λ ≅ B` that is an
`S`-bimodule map, sends `Λ_{≥d}` onto `F^d` and has leading term the identity
(`exists_split`). In the transported multiplication `a ⋆ b = φ⁻¹(φa φb)` the
`S`-actions are those of `Λ` and `a ⋆ b - ab` raises degree (`star_sub_mul_ge`).

Here the splitting is built from diagonal idempotents whose degree-`0` corners are lines
(`Diag`, `exists_splitD`); for `S = Λ₀ ≅ kⁿ` (`Vertices`) this is `exists_split`. A split
semisimple `S` with matrix blocks is handled in `Refinements/SplitSemisimple.lean` by lifting
matrix units and transporting the splitting of the root corners.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] (G : LenGrading k Λ)

/-- `Λ_{≥ m}`. -/
def geSub (m : ℕ) : Submodule k Λ where
  carrier := {a | G.Ge m a}
  add_mem' := G.ge_add
  zero_mem' := fun _ _ ↦ map_zero _
  smul_mem' c _ h := G.ge_smul c h

theorem mem_geSub {m : ℕ} {a : Λ} : a ∈ G.geSub m ↔ G.Ge m a := Iff.rfl

theorem isHom_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Λ) (h : ∀ i ∈ s, G.IsHom d (f i)) :
    G.IsHom d (∑ i ∈ s, f i) := by
  unfold IsHom
  rw [map_sum]
  exact Finset.sum_congr rfl h

theorem ge_sub_proj {m : ℕ} {a : Λ} (ha : G.Ge m a) : G.Ge (m + 1) (a - G.proj m a) := by
  intro d hd
  rw [map_sub, G.proj_proj]
  rcases Nat.lt_or_ge d m with h | h
  · rw [ha d h, if_neg (by omega), sub_zero]
  · obtain rfl : d = m := by omega
    rw [if_pos rfl, sub_self]

theorem eq_zero_of_ge {m : ℕ} {a : Λ} (ha : G.Ge m a) (hm : G.N ≤ m) : a = 0 := by
  rw [G.sum a]
  exact Finset.sum_eq_zero fun d hd ↦ ha d (by have := Finset.mem_range.1 hd; omega)

theorem ge_sum_proj (m : ℕ) (a : Λ) :
    G.Ge m (∑ e ∈ Finset.Ico m G.N, G.proj e a) := by
  intro d hd
  rw [map_sum]
  refine Finset.sum_eq_zero fun e he ↦ ?_
  rw [G.proj_proj, if_neg (by have := (Finset.mem_Ico.1 he).1; omega)]

theorem eq_sum_proj_of_ge {m : ℕ} {a : Λ} (ha : G.Ge m a) :
    a = ∑ e ∈ Finset.Ico m G.N, G.proj e a := by
  conv_lhs => rw [G.sum a]
  rcases le_or_gt m G.N with h | h
  · rw [← Finset.sum_range_add_sum_Ico _ h, Finset.sum_eq_zero fun d hd ↦ ha d
      (Finset.mem_range.1 hd), zero_add]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact Finset.sum_eq_zero fun d hd ↦ ha d (by have := Finset.mem_range.1 hd; omega)

theorem corner_corner {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {e : ι → R}
    (he : OrthogonalIdempotents e) (i j i' j' : ι) (y : R) :
    e i' * (e i * y * e j) * e j' = if i' = i ∧ j' = j then e i * y * e j else 0 := by
  calc e i' * (e i * y * e j) * e j' = (e i' * e i) * y * (e j * e j') := by simp only [mul_assoc]
    _ = _ := by
      rw [he.mul_eq, he.mul_eq]
      by_cases h1 : i' = i <;> by_cases h2 : j = j' <;> simp [h1, h2, eq_comm]

/-- **Vertex idempotents**: a complete set of orthogonal idempotents of degree
`0` spanning `Λ₀` (`S = Λ₀ ≅ kⁿ`). -/
structure Vertices where
  n : ℕ
  e : Fin n → Λ
  complete : CompleteOrthogonalIdempotents e
  deg0 : ∀ i, G.IsHom 0 (e i)
  span0 : ∀ a, G.IsHom 0 a → ∃ c : Fin n → k, a = ∑ i, c i • e i

variable {G}

theorem Vertices.isHom_one (V : Vertices G) : G.IsHom 0 (1 : Λ) := by
  rw [← V.complete.complete]
  exact G.isHom_sum _ _ fun i _ ↦ V.deg0 i

variable (G) in
/-- **Diagonal idempotents**: a complete set of orthogonal idempotents of degree `0` whose
degree-`0` diagonal corners are lines (`e_i Λ₀ e_i = k e_i`). The vertex idempotents of `Λ₀ ≅ kⁿ`
(`Vertices`) and the diagonal matrix units of a split semisimple `Λ₀` are examples. -/
structure Diag where
  n : ℕ
  e : Fin n → Λ
  complete : CompleteOrthogonalIdempotents e
  deg0 : ∀ i, G.IsHom 0 (e i)
  corner0 : ∀ i a, G.IsHom 0 a → ∃ c : k, e i * a * e i = c • e i

theorem Diag.isHom_one (V : Diag G) : G.IsHom 0 (1 : Λ) := by
  rw [← V.complete.complete]
  exact G.isHom_sum _ _ fun i _ ↦ V.deg0 i

/-- Vertex idempotents are diagonal idempotents. -/
def Vertices.toDiag (V : Vertices G) : Diag G where
  n := V.n
  e := V.e
  complete := V.complete
  deg0 := V.deg0
  corner0 i a ha := by
    classical
    obtain ⟨c, rfl⟩ := V.span0 a ha
    refine ⟨c i, ?_⟩
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single i]
    · rw [mul_smul_comm, smul_mul_assoc, (V.complete.idem i).eq, (V.complete.idem i).eq]
    · intro l _ hl
      rw [mul_smul_comm, smul_mul_assoc, V.complete.ortho (Ne.symm hl), zero_mul, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

end LenGrading

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] (G : LenGrading k Λ)

/-- **Definition 6.2**: a positive filtered deformation `B` of `Λ`: a finite
decreasing multiplicative filtration `F` with `F⁰ = B`, and leading-term maps
`σ_d` identifying `F^d/F^{d+1}` with `Λ_d` multiplicatively. -/
structure PosFiltration (B : Type w) [Ring B] [Algebra k B] where
  F : ℕ → Submodule k B
  F_zero : F 0 = ⊤
  F_succ_le : ∀ d, F (d + 1) ≤ F d
  F_mul : ∀ d e (a b : B), a ∈ F d → b ∈ F e → a * b ∈ F (d + e)
  M : ℕ
  F_M : F M = ⊥
  σ : ℕ → B →ₗ[k] Λ
  σ_hom : ∀ d a, G.IsHom d (σ d a)
  σ_ker : ∀ d a, a ∈ F d → (σ d a = 0 ↔ a ∈ F (d + 1))
  σ_surj : ∀ d x, G.IsHom d x → ∃ a ∈ F d, σ d a = x
  σ_mul : ∀ d e (a b : B), a ∈ F d → b ∈ F e → σ (d + e) (a * b) = σ d a * σ e b

namespace PosFiltration

variable {G} {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)

theorem mem_zero (a : B) : a ∈ P.F 0 := by rw [P.F_zero]; trivial

theorem F_anti {d d' : ℕ} (h : d ≤ d') : P.F d' ≤ P.F d := by
  induction d', h using Nat.le_induction with
  | base => exact le_rfl
  | succ d' _ ih => exact (P.F_succ_le d').trans ih

theorem mul_mem_left {d : ℕ} (a : B) {b : B} (hb : b ∈ P.F d) : a * b ∈ P.F d := by
  simpa using P.F_mul 0 d a b (P.mem_zero a) hb

theorem mul_mem_right {d : ℕ} {a : B} (b : B) (ha : a ∈ P.F d) : a * b ∈ P.F d := by
  simpa using P.F_mul d 0 a b ha (P.mem_zero b)

theorem eq_bot_of_le {d : ℕ} (h : P.M ≤ d) : P.F d = ⊥ :=
  eq_bot_iff.2 (P.F_M ▸ P.F_anti h)

theorem σ_mul_left (d : ℕ) (a b : B) (hb : b ∈ P.F d) : P.σ d (a * b) = P.σ 0 a * P.σ d b := by
  simpa using P.σ_mul 0 d a b (P.mem_zero a) hb

theorem σ_mul_right (d : ℕ) (a b : B) (ha : a ∈ P.F d) : P.σ d (a * b) = P.σ d a * P.σ 0 b := by
  simpa using P.σ_mul d 0 a b ha (P.mem_zero b)

theorem pow_mem {x : B} (hx : x ∈ P.F 1) (n : ℕ) : x ^ (n + 1) ∈ P.F (n + 1) := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ]; exact P.F_mul _ _ _ _ ih hx

variable (V : Diag G)

/-- The leading term in degree `0`, as a ring homomorphism `B → Λ`. -/
def σ0 : B →+* Λ where
  toFun := P.σ 0
  map_one' := by
    obtain ⟨u, -, hu⟩ := P.σ_surj 0 1 V.isHom_one
    calc P.σ 0 1 = P.σ 0 1 * P.σ 0 u := by rw [hu, mul_one]
      _ = P.σ 0 (1 * u) := (P.σ_mul_left 0 1 u (P.mem_zero u)).symm
      _ = 1 := by rw [one_mul, hu]
  map_mul' a b := P.σ_mul_left 0 a b (P.mem_zero b)
  map_zero' := map_zero _
  map_add' := map_add _

theorem σ0_apply (a : B) : P.σ0 V a = P.σ 0 a := rfl

theorem ker_σ0_nilpotent : ∀ x ∈ RingHom.ker (P.σ0 V), IsNilpotent x := by
  intro x hx
  have h1 : x ∈ P.F 1 := (P.σ_ker 0 x (P.mem_zero x)).1 hx
  refine ⟨P.M + 1, ?_⟩
  have := P.F_anti (Nat.le_succ P.M) (P.pow_mem h1 P.M)
  rw [P.F_M] at this
  exact (Submodule.mem_bot k).1 this

/-- **Lifted vertex idempotents.** -/
theorem exists_lift : ∃ eL : Fin V.n → B, CompleteOrthogonalIdempotents eL ∧
    ∀ i, P.σ 0 (eL i) = V.e i := by
  obtain ⟨eL, h1, h2⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker (P.σ0 V)
    (P.ker_σ0_nilpotent V) V.complete fun i ↦ by
      obtain ⟨a, -, ha⟩ := P.σ_surj 0 _ (V.deg0 i)
      exact ⟨a, ha⟩
  exact ⟨eL, h1, fun i ↦ congrFun h2 i⟩

/-! ### Splitting the filtration as `S`-bimodules -/

variable (eL : Fin V.n → B)

/-- `x ↦ ẽ_i x ẽ_j`. -/
def cornerMap (i j : Fin V.n) : B →ₗ[k] B :=
  LinearMap.mulLeft k (eL i) ∘ₗ LinearMap.mulRight k (eL j)

theorem cornerMap_apply (i j : Fin V.n) (x : B) : cornerMap V eL i j x = eL i * x * eL j := by
  simp [cornerMap, mul_assoc]

/-- The corner `ẽ_i F^d ẽ_j`. -/
def C (i j : Fin V.n) (d : ℕ) : Submodule k B := (P.F d).map (cornerMap V eL i j)

open Classical in
/-- A complement of `ẽ_i F^{d+1} ẽ_j` in `ẽ_i F^d ẽ_j` (the line of `ẽ_i` in the
degree-`0` diagonal corners). -/
def W (i j : Fin V.n) (d : ℕ) : Submodule k B :=
  if i = j ∧ d = 0 then k ∙ eL i
  else Classical.choose (Submodule.exists_isCompl (P.C V eL i j (d + 1))) ⊓ P.C V eL i j d

variable {P V eL} (heL : CompleteOrthogonalIdempotents eL) (hσe : ∀ i, P.σ 0 (eL i) = V.e i)

include heL in
theorem mem_C {i j : Fin V.n} {d : ℕ} {x : B} :
    x ∈ P.C V eL i j d ↔ x ∈ P.F d ∧ eL i * x * eL j = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [cornerMap_apply]
    refine ⟨P.mul_mem_right _ (P.mul_mem_left _ hy), ?_⟩
    calc eL i * (eL i * y * eL j) * eL j = (eL i * eL i) * y * (eL j * eL j) := by
          simp only [mul_assoc]
      _ = _ := by rw [(heL.idem i).eq, (heL.idem j).eq]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, by rw [cornerMap_apply, he]⟩

include heL in
theorem C_succ_le (i j : Fin V.n) (d : ℕ) : P.C V eL i j (d + 1) ≤ P.C V eL i j d :=
  Submodule.map_mono (P.F_succ_le d)

theorem idem_eq_zero {x : B} (hx : IsIdempotentElem x) (h1 : x ∈ P.F 1) : x = 0 := by
  have := P.F_anti (Nat.le_succ P.M) (P.pow_mem h1 P.M)
  rw [hx.pow_succ_eq, P.F_M] at this
  exact (Submodule.mem_bot k).1 this

include heL in
theorem eL_mem_C (i : Fin V.n) : eL i ∈ P.C V eL i i 0 :=
  (mem_C heL).2 ⟨P.mem_zero _, by rw [(heL.idem i).eq, (heL.idem i).eq]⟩

include heL in
theorem W_le (i j : Fin V.n) (d : ℕ) : P.W V eL i j d ≤ P.C V eL i j d := by
  unfold W
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (Submodule.span_singleton_le_iff_mem _ _).2 (eL_mem_C heL i)
  · exact inf_le_right

include hσe in
theorem σ0_corner_eq {i : Fin V.n} {x : B} (hx : eL i * x * eL i = x) (heL : CompleteOrthogonalIdempotents eL) :
    ∃ c : k, P.σ 0 x = c • V.e i := by
  have h1 : P.σ 0 x = V.e i * P.σ 0 x * V.e i := by
    conv_lhs => rw [← hx]
    rw [P.σ_mul_right 0 _ _ (P.mem_zero _), P.σ_mul_left 0 _ _ (P.mem_zero _), hσe]
  rw [h1]
  exact V.corner0 i _ (P.σ_hom 0 x)

include heL hσe in
theorem sup_W (i j : Fin V.n) (d : ℕ) :
    P.C V eL i j (d + 1) ⊔ P.W V eL i j d = P.C V eL i j d := by
  unfold W
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    refine le_antisymm (sup_le (C_succ_le heL i i 0)
      ((Submodule.span_singleton_le_iff_mem _ _).2 (eL_mem_C heL i))) fun x hx ↦ ?_
    have hxC := (mem_C heL).1 hx
    obtain ⟨c, hc⟩ := σ0_corner_eq hσe hxC.2 heL
    have hy : x - c • eL i ∈ P.C V eL i i 1 := by
      refine (mem_C heL).2 ⟨(P.σ_ker 0 _ (P.mem_zero _)).1 ?_, ?_⟩
      · rw [map_sub, map_smul, hσe, hc, sub_self]
      · rw [mul_sub, sub_mul, hxC.2, mul_smul_comm, smul_mul_assoc, (heL.idem i).eq,
          (heL.idem i).eq]
    rw [show x = (x - c • eL i) + c • eL i by abel]
    exact Submodule.add_mem_sup hy (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))
  · have h := Classical.choose_spec (Submodule.exists_isCompl (P.C V eL i j (d + 1)))
    rw [← sup_inf_assoc_of_le _ (C_succ_le heL i j d), h.sup_eq_top, top_inf_eq]

include hσe in
theorem W_inf {i j : Fin V.n} {d : ℕ} {x : B} (hx : x ∈ P.W V eL i j d)
    (hx' : x ∈ P.C V eL i j (d + 1)) (heL : CompleteOrthogonalIdempotents eL) : x = 0 := by
  unfold W at hx
  split_ifs at hx with hij
  · obtain ⟨rfl, rfl⟩ := hij
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have h1 := ((mem_C heL).1 hx').1
    have h0 : P.σ 0 (c • eL i) = 0 := (P.σ_ker 0 _ (P.mem_zero _)).2 h1
    rw [map_smul, hσe] at h0
    rcases smul_eq_zero.1 h0 with hc | he
    · rw [hc, zero_smul]
    · have : eL i ∈ P.F 1 := (P.σ_ker 0 _ (P.mem_zero _)).1 (by rw [hσe, he])
      rw [P.idem_eq_zero (heL.idem i) this, smul_zero]
  · have h := Classical.choose_spec (Submodule.exists_isCompl (P.C V eL i j (d + 1)))
    have : x ∈ P.C V eL i j (d + 1) ⊓ Classical.choose
        (Submodule.exists_isCompl (P.C V eL i j (d + 1))) := ⟨hx', hx.1⟩
    rw [h.inf_eq_bot] at this
    exact (Submodule.mem_bot k).1 this

variable (V) in
/-- The corner `e_i Λ_d e_j` of `Λ`. -/
def Lc (i j : Fin V.n) (d : ℕ) : Submodule k Λ where
  carrier := {x | G.IsHom d x ∧ V.e i * x * V.e j = x}
  add_mem' {x y} hx hy := ⟨by unfold LenGrading.IsHom; rw [map_add, hx.1, hy.1],
    by rw [mul_add, add_mul, hx.2, hy.2]⟩
  zero_mem' := ⟨by unfold LenGrading.IsHom; rw [map_zero], by rw [mul_zero, zero_mul]⟩
  smul_mem' c x hx := ⟨by unfold LenGrading.IsHom; rw [map_smul, hx.1],
    by rw [mul_smul_comm, smul_mul_assoc, hx.2]⟩

variable (V) in
/-- `a ↦ e_i (proj_d a) e_j`. -/
def πc (i j : Fin V.n) (d : ℕ) : Λ →ₗ[k] Λ :=
  LinearMap.mulLeft k (V.e i) ∘ₗ LinearMap.mulRight k (V.e j) ∘ₗ G.proj d

theorem πc_apply (i j : Fin V.n) (d : ℕ) (a : Λ) :
    πc V i j d a = V.e i * G.proj d a * V.e j := by
  simp [πc, mul_assoc]

theorem πc_mem (i j : Fin V.n) (d : ℕ) (a : Λ) : πc V i j d a ∈ Lc V i j d := by
  rw [πc_apply]
  refine ⟨?_, ?_⟩
  · have := G.isHom_mul (G.isHom_mul (V.deg0 i) (G.isHom_proj d a)) (V.deg0 j)
    simpa using this
  · classical
    have := corner_corner V.complete.toOrthogonalIdempotents i j i j (G.proj d a)
    rwa [if_pos ⟨rfl, rfl⟩] at this

theorem πc_of_mem {i j : Fin V.n} {d : ℕ} {x : Λ} (hx : x ∈ Lc V i j d) (i' j' : Fin V.n)
    (d' : ℕ) : πc V i' j' d' x = if i' = i ∧ j' = j ∧ d' = d then x else 0 := by
  classical
  rw [πc_apply, G.proj_of_isHom hx.1]
  by_cases hd : d = d'
  · subst hd
    rw [if_pos rfl]
    conv_lhs => rw [← hx.2]
    rw [corner_corner V.complete.toOrthogonalIdempotents, hx.2]
    by_cases h : i' = i ∧ j' = j
    · rw [if_pos h, if_pos ⟨h.1, h.2, rfl⟩]
    · rw [if_neg h, if_neg (fun h' ↦ h ⟨h'.1, h'.2.1⟩)]
  · rw [if_neg hd, if_neg (fun h ↦ hd h.2.2.symm), mul_zero, zero_mul]

include heL hσe in
theorem σ_corner {d : ℕ} {x : B} (hx : x ∈ P.F d) (i j : Fin V.n) :
    P.σ d (eL i * x * eL j) = V.e i * P.σ d x * V.e j := by
  rw [P.σ_mul_right d _ _ (P.mul_mem_left _ hx), P.σ_mul_left d _ _ hx, hσe, hσe]

variable (P V eL) in
/-- `σ_d` on the complement. -/
def τ (i j : Fin V.n) (d : ℕ) : P.W V eL i j d →ₗ[k] Λ := P.σ d ∘ₗ (P.W V eL i j d).subtype

include heL hσe in
theorem τ_injective (i j : Fin V.n) (d : ℕ) : Function.Injective (P.τ V eL i j d) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨w, hw⟩ h0
  simp only [LinearMap.mem_ker, τ, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype] at h0
  have hwC := (mem_C heL).1 (W_le heL i j d hw)
  have hw1 : w ∈ P.F (d + 1) := (P.σ_ker d w hwC.1).1 h0
  have := W_inf hσe hw ((mem_C heL).2 ⟨hw1, hwC.2⟩) heL
  simp [this]

include heL hσe in
theorem range_τ (i j : Fin V.n) (d : ℕ) : LinearMap.range (P.τ V eL i j d) = Lc V i j d := by
  ext y
  constructor
  · rintro ⟨⟨w, hw⟩, rfl⟩
    have hwC := (mem_C heL).1 (W_le heL i j d hw)
    refine ⟨P.σ_hom d w, ?_⟩
    change V.e i * P.σ d w * V.e j = P.σ d w
    rw [← σ_corner heL hσe hwC.1, hwC.2]
  · intro hy
    obtain ⟨a, ha, rfl⟩ := P.σ_surj d y hy.1
    have hc : eL i * a * eL j ∈ P.C V eL i j d := (mem_C heL).2
      ⟨P.mul_mem_right _ (P.mul_mem_left _ ha), by
        calc eL i * (eL i * a * eL j) * eL j = (eL i * eL i) * a * (eL j * eL j) := by
              simp only [mul_assoc]
          _ = _ := by rw [(heL.idem i).eq, (heL.idem j).eq]⟩
    rw [← sup_W heL hσe] at hc
    obtain ⟨c₁, hc₁, w, hw, hcw⟩ := Submodule.mem_sup.1 hc
    have hc₁F := ((mem_C heL).1 hc₁).1
    have h0 : P.σ d c₁ = 0 := (P.σ_ker d c₁ (P.F_succ_le d hc₁F)).2 hc₁F
    refine ⟨⟨w, hw⟩, ?_⟩
    change P.σ d w = P.σ d a
    have := congrArg (P.σ d) hcw
    rw [map_add, h0, zero_add, σ_corner heL hσe ha, hy.2] at this
    exact this

/-- The inverse of `σ_d` on the corner `e_i Λ_d e_j`, extended by the corner projection. -/
def ψ (i j : Fin V.n) (d : ℕ) : Λ →ₗ[k] B :=
  (P.W V eL i j d).subtype ∘ₗ (LinearEquiv.ofInjective _ (τ_injective (P := P) heL hσe i j d)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (P.τ V eL i j d)) (πc V i j d)
      (fun a ↦ (range_τ (P := P) heL hσe i j d).symm ▸ πc_mem (V := V) i j d a)

theorem ψ_mem (i j : Fin V.n) (d : ℕ) (a : Λ) : ψ heL hσe i j d a ∈ P.W V eL i j d := by
  simp only [ψ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  exact Subtype.property _

theorem σ_ψ (i j : Fin V.n) (d : ℕ) (a : Λ) : P.σ d (ψ heL hσe i j d a) = πc V i j d a := by
  simp only [ψ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  have := LinearEquiv.ofInjective_symm_apply (f := P.τ V eL i j d)
    (h := τ_injective (P := P) heL hσe i j d) (LinearMap.codRestrict _ (πc V i j d)
      (fun a ↦ (range_τ (P := P) heL hσe i j d).symm ▸ πc_mem (V := V) i j d a) a)
  exact this

theorem ψ_eq_zero {i j : Fin V.n} {d : ℕ} {a : Λ} (h : πc V i j d a = 0) :
    ψ heL hσe i j d a = 0 := by
  have h0 : LinearMap.codRestrict (LinearMap.range (P.τ V eL i j d)) (πc V i j d)
      (fun a ↦ (range_τ (P := P) heL hσe i j d).symm ▸ πc_mem (V := V) i j d a) a = 0 :=
    Subtype.ext h
  simp only [ψ, LinearMap.coe_comp, Function.comp_apply, h0, map_zero]

theorem ψ_mem_F (i j : Fin V.n) (d : ℕ) (a : Λ) : ψ heL hσe i j d a ∈ P.F d :=
  ((mem_C heL).1 (W_le heL i j d (ψ_mem heL hσe i j d a))).1

theorem ψ_corner (i j : Fin V.n) (d : ℕ) (a : Λ) :
    eL i * ψ heL hσe i j d a * eL j = ψ heL hσe i j d a :=
  ((mem_C heL).1 (W_le heL i j d (ψ_mem heL hσe i j d a))).2

/-- **The splitting map** `φ = Σ ψ_{ijd}`. -/
def φ0 : Λ →ₗ[k] B := ∑ i, ∑ j, ∑ d ∈ Finset.range G.N, ψ heL hσe i j d

theorem φ0_apply (a : Λ) :
    φ0 heL hσe a = ∑ i, ∑ j, ∑ d ∈ Finset.range G.N, ψ heL hσe i j d a := by
  simp [φ0, LinearMap.sum_apply]

theorem φ0_of_mem {i j : Fin V.n} {d : ℕ} {x : Λ} (hx : x ∈ Lc V i j d) :
    φ0 heL hσe x = ψ heL hσe i j d x := by
  classical
  by_cases hd : d < G.N
  · rw [φ0_apply, Finset.sum_eq_single i, Finset.sum_eq_single j, Finset.sum_eq_single d]
    · intro d' _ hd'
      exact ψ_eq_zero heL hσe (by rw [πc_of_mem hx, if_neg (fun h ↦ hd' h.2.2)])
    · intro h; exact absurd (Finset.mem_range.2 hd) h
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun d' _ ↦ ψ_eq_zero heL hσe
        (by rw [πc_of_mem hx, if_neg (fun h ↦ hj' h.2.1)])
    · intro h; exact absurd (Finset.mem_univ j) h
    · intro i' _ hi'
      exact Finset.sum_eq_zero fun j' _ ↦ Finset.sum_eq_zero fun d' _ ↦ ψ_eq_zero heL hσe
        (by rw [πc_of_mem hx, if_neg (fun h ↦ hi' h.1)])
    · intro h; exact absurd (Finset.mem_univ i) h
  · have : x = 0 := G.isHom_zero_of_ge hx.1 (by omega)
    subst this
    rw [map_zero, map_zero]

theorem eq_sum_corners (a : Λ) : a = ∑ i, ∑ j, V.e i * a * V.e j := by
  calc a = (∑ i, V.e i) * a * (∑ j, V.e j) := by rw [V.complete.complete, one_mul, mul_one]
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; simp_rw [Finset.mul_sum]

theorem mem_Lc_of_hom {d : ℕ} {a : Λ} (ha : G.IsHom d a) (i j : Fin V.n) :
    V.e i * a * V.e j ∈ Lc V i j d := by
  have := πc_mem (V := V) i j d a
  rwa [πc_apply, ha] at this

/-- **Leading terms**: `φ` maps `Λ_d` into `F^d` with leading term the identity. -/
theorem φ0_hom {d : ℕ} {a : Λ} (ha : G.IsHom d a) :
    φ0 heL hσe a ∈ P.F d ∧ P.σ d (φ0 heL hσe a) = a := by
  classical
  have hsum : φ0 heL hσe a = ∑ i, ∑ j, ψ heL hσe i j d (V.e i * a * V.e j) := by
    conv_lhs => rw [eq_sum_corners (V := V) a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ φ0_of_mem heL hσe (mem_Lc_of_hom ha i j)
  rw [hsum]
  refine ⟨Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ψ_mem_F heL hσe i j d _, ?_⟩
  rw [map_sum]
  conv_rhs => rw [eq_sum_corners (V := V) a]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [σ_ψ, πc_of_mem (mem_Lc_of_hom ha i j), if_pos ⟨rfl, rfl, rfl⟩]

theorem eq_sum_πc (a : Λ) : a = ∑ i, ∑ j, ∑ d ∈ Finset.range G.N, πc V i j d a := by
  calc a = ∑ d ∈ Finset.range G.N, G.proj d a := G.sum a
    _ = ∑ d ∈ Finset.range G.N, ∑ i, ∑ j, πc V i j d a :=
        Finset.sum_congr rfl fun d _ ↦ by simp_rw [πc_apply]; exact eq_sum_corners (V := V) _
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm

/-- **`φ` is an `S`-bimodule map.** -/
theorem φ0_left (l : Fin V.n) (a : Λ) : φ0 heL hσe (V.e l * a) = eL l * φ0 heL hσe a := by
  classical
  have key : ∀ i j d (x : Λ), x ∈ Lc V i j d →
      φ0 heL hσe (V.e l * x) = eL l * φ0 heL hσe x := by
    intro i j d x hx
    rw [φ0_of_mem heL hσe hx]
    by_cases hl : l = i
    · subst hl
      have hx' : V.e l * x = x := by
        rw [← hx.2, ← mul_assoc, ← mul_assoc, (V.complete.idem l).eq]
      rw [hx', φ0_of_mem heL hσe hx, ← ψ_corner heL hσe, ← mul_assoc, ← mul_assoc,
        (heL.idem l).eq]
    · have h0 : V.e l * x = 0 := by
        rw [← hx.2, ← mul_assoc, ← mul_assoc, V.complete.ortho hl, zero_mul, zero_mul]
      rw [h0, map_zero, ← ψ_corner heL hσe, ← mul_assoc, ← mul_assoc, heL.ortho hl, zero_mul,
        zero_mul]
  conv_lhs => rw [eq_sum_πc (V := V) a]
  conv_rhs => rw [eq_sum_πc (V := V) a]
  simp only [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl
    fun d _ ↦ key i j d _ (πc_mem i j d a)

theorem φ0_right (l : Fin V.n) (a : Λ) : φ0 heL hσe (a * V.e l) = φ0 heL hσe a * eL l := by
  classical
  have key : ∀ i j d (x : Λ), x ∈ Lc V i j d →
      φ0 heL hσe (x * V.e l) = φ0 heL hσe x * eL l := by
    intro i j d x hx
    rw [φ0_of_mem heL hσe hx]
    by_cases hl : l = j
    · subst hl
      have hx' : x * V.e l = x := by
        rw [← hx.2, mul_assoc, (V.complete.idem l).eq]
      rw [hx', φ0_of_mem heL hσe hx]
      conv_rhs => rw [← ψ_corner heL hσe i l d x]
      rw [mul_assoc, (heL.idem l).eq, ψ_corner]
    · have h0 : x * V.e l = 0 := by
        rw [← hx.2, mul_assoc, V.complete.ortho (Ne.symm hl), mul_zero]
      rw [h0, map_zero]
      conv_rhs => rw [← ψ_corner heL hσe i j d x]
      rw [mul_assoc, heL.ortho (Ne.symm hl), mul_zero]
  conv_lhs => rw [eq_sum_πc (V := V) a]
  conv_rhs => rw [eq_sum_πc (V := V) a]
  simp only [Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl
    fun d _ ↦ key i j d _ (πc_mem i j d a)

theorem φ0_ge {d : ℕ} {a : Λ} (ha : G.Ge d a) : φ0 heL hσe a ∈ P.F d := by
  rw [G.eq_sum_proj_of_ge ha, map_sum]
  exact Submodule.sum_mem _ fun e he ↦
    P.F_anti (Finset.mem_Ico.1 he).1 (φ0_hom heL hσe (G.isHom_proj e a)).1

theorem φ0_surj_aux : ∀ n d, P.M ≤ d + n → ∀ x ∈ P.F d, ∃ a, G.Ge d a ∧ φ0 heL hσe a = x := by
  intro n
  induction n with
  | zero =>
      intro d hd x hx
      rw [P.eq_bot_of_le (by omega)] at hx
      rw [(Submodule.mem_bot k).1 hx]
      exact ⟨0, fun _ _ ↦ map_zero _, map_zero _⟩
  | succ n ih =>
      intro d hd x hx
      set y := x - φ0 heL hσe (P.σ d x)
      have hlead := φ0_hom heL hσe (P.σ_hom d x)
      have hy : y ∈ P.F (d + 1) := by
        refine (P.σ_ker d y (Submodule.sub_mem _ hx hlead.1)).1 ?_
        rw [map_sub, hlead.2, sub_self]
      obtain ⟨a', ha', hay⟩ := ih (d + 1) (by omega) y hy
      refine ⟨P.σ d x + a', G.ge_add (G.ge_of_isHom (P.σ_hom d x)) (G.ge_mono (by omega) ha'), ?_⟩
      rw [map_add, hay]
      show _ + (x - _) = x
      abel

theorem φ0_injective : Function.Injective (φ0 heL hσe) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [LinearMap.mem_ker] at ha
  rw [Submodule.mem_bot]
  by_contra ha0
  have hex : ∃ d, G.proj d a ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (by rw [G.sum a]; exact Finset.sum_eq_zero fun d _ ↦ h d)
  set d := Nat.find hex
  have hge : G.Ge d a := fun e he ↦ by
    by_contra h
    exact Nat.find_min hex he h
  have h1 := φ0_ge heL hσe (G.ge_sub_proj hge)
  rw [map_sub, ha, zero_sub] at h1
  have h2 : φ0 heL hσe (G.proj d a) ∈ P.F (d + 1) := by
    have := Submodule.neg_mem _ h1
    rwa [neg_neg] at this
  have h3 := (φ0_hom heL hσe (G.isHom_proj d a))
  have h4 := (P.σ_ker d _ h3.1).2 h2
  rw [h3.2] at h4
  exact Nat.find_spec hex h4

theorem φ0_e (i : Fin V.n) : φ0 heL hσe (V.e i) = eL i := by
  classical
  have hx : V.e i ∈ Lc V i i 0 := by
    have := mem_Lc_of_hom (V := V) (V.deg0 i) i i
    rwa [(V.complete.idem i).eq, (V.complete.idem i).eq] at this
  have hw := ψ_mem heL hσe i i 0 (V.e i)
  have hσ := σ_ψ heL hσe i i 0 (V.e i)
  rw [πc_of_mem hx, if_pos ⟨rfl, rfl, rfl⟩] at hσ
  unfold W at hw
  rw [if_pos ⟨rfl, rfl⟩] at hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hw
  rw [φ0_of_mem heL hσe hx, ← hc]
  rw [← hc, map_smul, hσe] at hσ
  by_cases he : V.e i = 0
  · have : eL i ∈ P.F 1 := (P.σ_ker 0 _ (P.mem_zero _)).1 (by rw [hσe, he])
    rw [P.idem_eq_zero (heL.idem i) this, smul_zero]
  · have hc1 : c = 1 := by
      by_contra hc1
      have : (c - 1) • V.e i = 0 := by rw [sub_smul, hσ, one_smul, sub_self]
      exact he ((smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc1))
    rw [hc1, one_smul]

variable (P V) in
/-- The diagonal idempotents lift, and the filtration splits compatibly: a linear isomorphism
`φ : Λ ≅ B` sending `e_i` to the lifted idempotents, linear for them on both sides, mapping
`Λ_{≥d}` onto `F^d`, with leading term the identity. -/
theorem exists_splitD :
    ∃ φ : Λ ≃ₗ[k] B, CompleteOrthogonalIdempotents (fun i ↦ φ (V.e i)) ∧
      (∀ i a, φ (V.e i * a) = φ (V.e i) * φ a) ∧ (∀ i a, φ (a * V.e i) = φ a * φ (V.e i)) ∧
      (∀ d a, G.IsHom d a → P.σ d (φ a) = a) ∧
      ∀ d, Submodule.map φ.toLinearMap (G.geSub d) = P.F d := by
  obtain ⟨eL, heL, hσe⟩ := P.exists_lift V
  have hsurj : Function.Surjective (φ0 heL hσe) := fun x ↦ by
    obtain ⟨a, -, ha⟩ := φ0_surj_aux heL hσe P.M 0 (by omega) x (P.mem_zero x)
    exact ⟨a, ha⟩
  let φ := LinearEquiv.ofBijective (φ0 heL hσe) ⟨φ0_injective heL hσe, hsurj⟩
  have hφ : ∀ a, φ a = φ0 heL hσe a := fun a ↦ rfl
  refine ⟨φ, ?_, fun i a ↦ ?_, fun i a ↦ ?_, fun d a ha ↦ ?_, fun d ↦ ?_⟩
  · simp only [hφ, φ0_e]; exact heL
  · rw [hφ, hφ, hφ, φ0_e, φ0_left]
  · rw [hφ, hφ, hφ, φ0_e, φ0_right]
  · exact (φ0_hom heL hσe ha).2
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact φ0_ge heL hσe ha
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := φ0_surj_aux heL hσe P.M d (by omega) x hx
      exact ⟨a, ha, rfl⟩

/-- **Lemma 6.4** for `S = Λ₀ ≅ kⁿ`: the vertex idempotents lift, and the filtration splits as
`S`-bimodules: a linear isomorphism `φ : Λ ≅ B` sending `e_i` to the lifted idempotents,
`S`-bilinear, mapping `Λ_{≥d}` onto `F^d`, with leading term the identity. For a split semisimple
`S` see `PosFiltration.splitPositiveDeformation_ss`. -/
theorem exists_split (V : Vertices G) :
    ∃ φ : Λ ≃ₗ[k] B, CompleteOrthogonalIdempotents (fun i ↦ φ (V.e i)) ∧
      (∀ i a, φ (V.e i * a) = φ (V.e i) * φ a) ∧ (∀ i a, φ (a * V.e i) = φ a * φ (V.e i)) ∧
      (∀ d a, G.IsHom d a → P.σ d (φ a) = a) ∧
      ∀ d, Submodule.map φ.toLinearMap (G.geSub d) = P.F d :=
  P.exists_splitD V.toDiag

end PosFiltration

end MultiplicativeBasisDeformations
