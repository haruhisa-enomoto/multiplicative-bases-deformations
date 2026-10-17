import MultiplicativeBasisDeformations.Refinements.ModuleLifting
import MultiplicativeBasisDeformations.Foundations.PositiveDeformation
import MultiplicativeBasisDeformations.Foundations.A0Graded

/-!
# The split form of a positive filtered deformation (Lemma 6.4, as used in Proposition 6.5)

`positive-deformations.tex`: "The resulting identification of `B` with `Λ` as
filtered vector spaces induces the prescribed identification `gr B = Λ`, and the multiplication
of `B` becomes `μ₀ + Σ_{q>0} μ_q`, where `μ₀` is the multiplication of `Λ` and each `μ_q` raises
internal degree by `q`, […] and vanishes when an input belongs to `S`."

From a splitting `φ : Λ ≅ B` (`Split`, given by `PosFiltration.exists_split`) the transported
product `a ⋆ b = φ⁻¹(φa φb)` decomposes into homogeneous parts `μ_q` (`Split.μ`), which form a
positive deformation in split form (`Split.posDef`) with total product `⋆` (`Split.tot_eq_star`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

universe u v w

namespace PosFiltration

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)

/-- **A splitting of a positive filtered deformation** (Lemma 6.4): a linear isomorphism
`φ : Λ ≅ B` preserving `1`, mapping `Λ_{≥d}` onto `F^d`, with leading term the identity. -/
structure Split where
  φ : Λ ≃ₗ[k] B
  one : φ 1 = 1
  σφ : ∀ d a, G.IsHom d a → P.σ d (φ a) = a
  F_eq : ∀ d, Submodule.map φ.toLinearMap (G.geSub d) = P.F d

/-- **Lemma 6.4** gives a splitting. -/
theorem nonempty_split (V : Vertices G) : Nonempty (Split P) := by
  obtain ⟨φ, hc, -, -, hσ, hF⟩ := P.exists_split V
  refine ⟨⟨φ, ?_, hσ, hF⟩⟩
  rw [← V.complete.complete, map_sum, hc.complete]

namespace Split

variable {P} (S : Split P)

theorem mem_F_iff {d : ℕ} {a : Λ} : S.φ a ∈ P.F d ↔ G.Ge d a := by
  rw [← S.F_eq d]
  constructor
  · rintro ⟨a', ha', h⟩
    rw [S.φ.injective h] at ha'
    exact ha'
  · intro h; exact ⟨a, h, rfl⟩

theorem σ_ge {d : ℕ} {a : Λ} (ha : G.Ge d a) : P.σ d (S.φ a) = G.proj d a := by
  have hrest := G.ge_sub_proj ha
  have h1 : S.φ (a - G.proj d a) ∈ P.F (d + 1) := (S.mem_F_iff).2 hrest
  have h2 : P.σ d (S.φ (a - G.proj d a)) = 0 :=
    (P.σ_ker d _ (P.F_succ_le d h1)).2 h1
  rw [map_sub, map_sub, S.σφ d _ (G.isHom_proj d a), sub_eq_zero] at h2
  exact h2

/-- The transported product `a ⋆ b = φ⁻¹(φa φb)`. -/
def star : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  LinearMap.mk₂ k (fun a b ↦ S.φ.symm (S.φ a * S.φ b))
    (fun a a' b ↦ by simp [add_mul]) (fun c a b ↦ by simp [smul_mul_assoc])
    (fun a b b' ↦ by simp [mul_add]) (fun c a b ↦ by simp [mul_smul_comm])

theorem star_apply (a b : Λ) : S.star a b = S.φ.symm (S.φ a * S.φ b) := rfl

theorem φ_star (a b : Λ) : S.φ (S.star a b) = S.φ a * S.φ b := by
  rw [star_apply, LinearEquiv.apply_symm_apply]

theorem star_ge {d e : ℕ} {a b : Λ} (ha : G.Ge d a) (hb : G.Ge e b) : G.Ge (d + e) (S.star a b) :=
  (S.mem_F_iff).1 (by rw [φ_star]; exact P.F_mul d e _ _ ((S.mem_F_iff).2 ha) ((S.mem_F_iff).2 hb))

theorem proj_star {d e : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom e b) :
    G.proj (d + e) (S.star a b) = a * b := by
  rw [← S.σ_ge (S.star_ge (G.ge_of_isHom ha) (G.ge_of_isHom hb)), φ_star,
    P.σ_mul d e _ _ ((S.mem_F_iff).2 (G.ge_of_isHom ha)) ((S.mem_F_iff).2 (G.ge_of_isHom hb)),
    S.σφ d a ha, S.σφ e b hb]

theorem star_assoc (a b c : Λ) : S.star (S.star a b) c = S.star a (S.star b c) := by
  apply S.φ.injective
  rw [φ_star, φ_star, φ_star, φ_star, mul_assoc]

theorem star_one_left (a : Λ) : S.star 1 a = a := by
  rw [star_apply, S.one, one_mul, LinearEquiv.symm_apply_apply]

theorem star_one_right (a : Λ) : S.star a 1 = a := by
  rw [star_apply, S.one, mul_one, LinearEquiv.symm_apply_apply]

/-- **The degree-`q` part of the transported product.** -/
def μ (q : ℕ) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  LinearMap.mk₂ k
    (fun a b ↦ ∑ p ∈ range G.N, ∑ p' ∈ range G.N,
      G.proj (p + p' + q) (S.star (G.proj p a) (G.proj p' b)))
    (fun a a' b ↦ by simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c a b ↦ by simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum])
    (fun a b b' ↦ by simp only [map_add, Finset.sum_add_distrib])
    (fun c a b ↦ by simp only [map_smul, Finset.smul_sum])

theorem μ_hom {q d e : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom e b) :
    S.μ q a b = G.proj (d + e + q) (S.star a b) := by
  simp only [μ, LinearMap.mk₂_apply]
  by_cases hd : d < G.N
  · by_cases he : e < G.N
    · rw [Finset.sum_eq_single d, Finset.sum_eq_single e]
      · rw [G.proj_of_isHom ha, if_pos rfl, G.proj_of_isHom hb, if_pos rfl]
      · intro p' _ hp'
        rw [G.proj_of_isHom hb, if_neg (Ne.symm hp'), map_zero, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 he) h
      · intro p _ hp
        refine Finset.sum_eq_zero fun p' _ ↦ ?_
        rw [G.proj_of_isHom ha, if_neg (Ne.symm hp), map_zero, LinearMap.zero_apply, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 hd) h
    · rw [G.isHom_zero_of_ge hb (by omega)]
      simp
  · rw [G.isHom_zero_of_ge ha (by omega)]
    simp

theorem μ_isHom {q d e : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom e b) :
    G.IsHom (d + e + q) (S.μ q a b) := by
  rw [S.μ_hom ha hb]; exact G.isHom_proj _ _

theorem μ_eq_zero {q : ℕ} (hq : G.N ≤ q) : S.μ q = 0 := by
  ext a b
  simp only [μ, LinearMap.mk₂_apply, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun p' _ ↦ by
    rw [G.proj_ge _ (by omega), LinearMap.zero_apply]

/-- `a ⋆ b = Σ_q μ_q(a, b)` for homogeneous `a`, `b`. -/
theorem star_eq_sum_hom {d e : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom e b) :
    S.star a b = ∑ q ∈ range G.N, S.μ q a b := by
  have hge := S.star_ge (G.ge_of_isHom ha) (G.ge_of_isHom hb)
  conv_lhs => rw [G.sum (S.star a b)]
  have h1 : ∑ x ∈ range G.N, G.proj x (S.star a b) =
      ∑ x ∈ range (d + e + G.N), G.proj x (S.star a b) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show G.N ≤ d + e + G.N by omega),
      Finset.sum_eq_zero (s := Finset.Ico _ _) (fun x hx ↦ by
        rw [G.proj_ge x (Finset.mem_Ico.1 hx).1, LinearMap.zero_apply]), add_zero]
  rw [h1, Finset.sum_range_add,
    Finset.sum_eq_zero (fun x hx ↦ hge x (Finset.mem_range.1 hx)), zero_add]
  exact Finset.sum_congr rfl fun q _ ↦ (S.μ_hom ha hb).symm

theorem star_eq_sum (a b : Λ) : S.star a b = ∑ q ∈ range G.N, S.μ q a b := by
  have key : ∀ p p', S.star (G.proj p a) (G.proj p' b) =
      ∑ q ∈ range G.N, S.μ q (G.proj p a) (G.proj p' b) := fun p p' ↦
    S.star_eq_sum_hom (G.isHom_proj p a) (G.isHom_proj p' b)
  have hl : S.star a b = ∑ p ∈ range G.N, ∑ p' ∈ range G.N,
      ∑ q ∈ range G.N, S.μ q (G.proj p a) (G.proj p' b) := by
    conv_lhs => rw [G.sum a, G.sum b]
    simp only [map_sum, LinearMap.sum_apply, key]
    rw [Finset.sum_comm]
  have hr : ∑ q ∈ range G.N, S.μ q a b = ∑ q ∈ range G.N, ∑ p ∈ range G.N,
      ∑ p' ∈ range G.N, S.μ q (G.proj p a) (G.proj p' b) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    conv_lhs => rw [G.sum a, G.sum b]
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
  rw [hl, hr]
  set X : ℕ → ℕ → ℕ → Λ := fun p p' q ↦ S.μ q (G.proj p a) (G.proj p' b)
  change ∑ p ∈ range G.N, ∑ p' ∈ range G.N, ∑ q ∈ range G.N, X p p' q =
    ∑ q ∈ range G.N, ∑ p ∈ range G.N, ∑ p' ∈ range G.N, X p p' q
  calc ∑ p ∈ range G.N, ∑ p' ∈ range G.N, ∑ q ∈ range G.N, X p p' q
      = ∑ p ∈ range G.N, ∑ q ∈ range G.N, ∑ p' ∈ range G.N, X p p' q :=
        Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
    _ = ∑ q ∈ range G.N, ∑ p ∈ range G.N, ∑ p' ∈ range G.N, X p p' q := Finset.sum_comm

theorem μ_zero_apply (a b : Λ) : S.μ 0 a b = a * b := by
  have key : ∀ p p', S.μ 0 (G.proj p a) (G.proj p' b) = G.proj p a * G.proj p' b := fun p p' ↦ by
    rw [S.μ_hom (G.isHom_proj p a) (G.isHom_proj p' b), add_zero,
      S.proj_star (G.isHom_proj p a) (G.isHom_proj p' b)]
  conv_lhs => rw [G.sum a, G.sum b]
  conv_rhs => rw [G.sum a, G.sum b]
  simp only [map_sum, LinearMap.sum_apply, key, Finset.sum_mul_sum]
  rw [Finset.sum_comm]

theorem μ_unit_left {q : ℕ} (hq : 0 < q) (h1 : G.IsHom 0 (1 : Λ)) (a : Λ) : S.μ q 1 a = 0 := by
  conv_lhs => rw [G.sum a]
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [S.μ_hom h1 (G.isHom_proj e a), S.star_one_left, G.proj_proj, if_neg (by omega)]

theorem μ_unit_right {q : ℕ} (hq : 0 < q) (h1 : G.IsHom 0 (1 : Λ)) (a : Λ) : S.μ q a 1 = 0 := by
  conv_lhs => rw [G.sum a]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [S.μ_hom (G.isHom_proj e a) h1, S.star_one_right, G.proj_proj, if_neg (by omega)]

/-- Extracting the degree-`d₀ + n` part of a double sum of homogeneous terms. -/
theorem proj_box (d₀ : ℕ) (X : ℕ → ℕ → Λ) (hX : ∀ q q', G.IsHom (d₀ + q + q') (X q q'))
    (hz : ∀ q q', G.N ≤ q ∨ G.N ≤ q' → X q q' = 0) (n : ℕ) :
    G.proj (d₀ + n) (∑ q ∈ range G.N, ∑ q' ∈ range G.N, X q q') =
      ∑ x ∈ antidiagonal n, X x.1 x.2 := by
  rcases Nat.eq_zero_or_pos G.N with hN | hN
  · rw [hN]
    simp only [Finset.range_zero, Finset.sum_empty, map_zero]
    exact (Finset.sum_eq_zero fun x _ ↦ hz _ _ (Or.inl (by omega))).symm
  have hbox := GExt.sum_range_ad_box' (G.N - 1) (G.N - 1) (G.N - 1 + (G.N - 1) + 1 + n)
    (by omega) X (fun i j hi ↦ hz i j (Or.inl (by omega))) (fun i j hj ↦ hz i j (Or.inr (by omega)))
  rw [show G.N - 1 + 1 = G.N by omega] at hbox
  rw [← hbox, map_sum]
  rw [Finset.sum_eq_single n]
  · rw [map_sum]
    exact Finset.sum_congr rfl fun x hx ↦ by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [G.proj_of_isHom (hX x.1 x.2), if_pos (by omega)]
  · intro m _ hm
    rw [map_sum]
    exact Finset.sum_eq_zero fun x hx ↦ by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [G.proj_of_isHom (hX x.1 x.2), if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem μAssoc_hom {d e f : ℕ} {a b c : Λ} (ha : G.IsHom d a) (hb : G.IsHom e b)
    (hc : G.IsHom f c) (n : ℕ) : GExt.μAssoc S.μ n a b c = 0 := by
  have hX : ∀ q q', G.IsHom (d + e + f + q + q') (S.μ q' (S.μ q a b) c) := fun q q' ↦ by
    have := S.μ_isHom (q := q') (S.μ_isHom (q := q) ha hb) hc
    rwa [show d + e + q + f + q' = d + e + f + q + q' by ring] at this
  have hY : ∀ q q', G.IsHom (d + e + f + q + q') (S.μ q' a (S.μ q b c)) := fun q q' ↦ by
    have := S.μ_isHom (q := q') ha (S.μ_isHom (q := q) hb hc)
    rwa [show d + (e + f + q) + q' = d + e + f + q + q' by ring] at this
  have hzX : ∀ q q', G.N ≤ q ∨ G.N ≤ q' → S.μ q' (S.μ q a b) c = 0 := by
    rintro q q' (h | h)
    · rw [S.μ_eq_zero h]; simp
    · rw [S.μ_eq_zero h]; simp
  have hzY : ∀ q q', G.N ≤ q ∨ G.N ≤ q' → S.μ q' a (S.μ q b c) = 0 := by
    rintro q q' (h | h)
    · rw [S.μ_eq_zero h]; simp
    · rw [S.μ_eq_zero h]; simp
  have hl : S.star (S.star a b) c = ∑ q ∈ range G.N, ∑ q' ∈ range G.N, S.μ q' (S.μ q a b) c := by
    rw [S.star_eq_sum a b, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun q _ ↦ S.star_eq_sum_hom (S.μ_isHom ha hb) hc
  have hr : S.star a (S.star b c) = ∑ q ∈ range G.N, ∑ q' ∈ range G.N, S.μ q' a (S.μ q b c) := by
    rw [S.star_eq_sum b c, map_sum]
    exact Finset.sum_congr rfl fun q _ ↦ S.star_eq_sum_hom ha (S.μ_isHom hb hc)
  have h := congrArg (G.proj (d + e + f + n)) (S.star_assoc a b c)
  rw [hl, hr, proj_box (d + e + f) _ hX hzX, proj_box (d + e + f) _ hY hzY] at h
  unfold GExt.μAssoc
  rw [h, sub_self]

/-- `μAssoc` as a linear map in each argument. -/
def μAssocL₁ (n : ℕ) (b c : Λ) : Λ →ₗ[k] Λ where
  toFun a := GExt.μAssoc S.μ n a b c
  map_add' a a' := by
    simp only [GExt.μAssoc, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel
  map_smul' t a := by
    simp only [GExt.μAssoc, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub,
      RingHom.id_apply]

def μAssocL₂ (n : ℕ) (a c : Λ) : Λ →ₗ[k] Λ where
  toFun b := GExt.μAssoc S.μ n a b c
  map_add' b b' := by
    simp only [GExt.μAssoc, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel
  map_smul' t b := by
    simp only [GExt.μAssoc, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub,
      RingHom.id_apply]

def μAssocL₃ (n : ℕ) (a b : Λ) : Λ →ₗ[k] Λ where
  toFun c := GExt.μAssoc S.μ n a b c
  map_add' c c' := by
    simp only [GExt.μAssoc, map_add, Finset.sum_add_distrib]; abel
  map_smul' t c := by
    simp only [GExt.μAssoc, map_smul, Finset.smul_sum, smul_sub, RingHom.id_apply]

theorem μAssoc_eq_zero (n : ℕ) (a b c : Λ) : GExt.μAssoc S.μ n a b c = 0 := by
  have h3 : ∀ d a, G.IsHom d a → ∀ e b, G.IsHom e b → ∀ c, GExt.μAssoc S.μ n a b c = 0 := by
    intro d a ha e b hb c
    change S.μAssocL₃ n a b c = 0
    rw [G.sum c, map_sum]
    exact Finset.sum_eq_zero fun f _ ↦ S.μAssoc_hom ha hb (G.isHom_proj f c) n
  have h2 : ∀ d a, G.IsHom d a → ∀ b c, GExt.μAssoc S.μ n a b c = 0 := by
    intro d a ha b c
    change S.μAssocL₂ n a c b = 0
    rw [G.sum b, map_sum]
    exact Finset.sum_eq_zero fun e _ ↦ h3 d a ha e _ (G.isHom_proj e b) c
  change S.μAssocL₁ n b c a = 0
  rw [G.sum a, map_sum]
  exact Finset.sum_eq_zero fun d _ ↦ h2 d _ (G.isHom_proj d a) b c

theorem μ_hdeg (h1 : G.IsHom 0 (1 : Λ)) (q : ℕ) :
    GExt.HDeg (GExt.GAlg.ofLen G h1) (S.μ q) q := by
  intro p p' a b ha hb
  rcases lt_or_ge p 0 with hp | hp
  · rw [(GExt.ZGr.ofLen_isHom_neg G hp a).1 ha, map_zero, LinearMap.zero_apply]
    exact (GExt.ZGr.ofLen G).isHom_zero _
  rcases lt_or_ge p' 0 with hp' | hp'
  · rw [(GExt.ZGr.ofLen_isHom_neg G hp' b).1 hb, map_zero]
    exact (GExt.ZGr.ofLen G).isHom_zero _
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hp'
  change (GExt.ZGr.ofLen G).IsHom d a at ha
  change (GExt.ZGr.ofLen G).IsHom e b at hb
  rw [GExt.ZGr.ofLen_isHom] at ha hb
  change (GExt.ZGr.ofLen G).IsHom _ _
  rw [show (d : ℤ) + e + q = ((d + e + q : ℕ) : ℤ) by push_cast; ring, GExt.ZGr.ofLen_isHom]
  exact S.μ_isHom ha hb

/-- **The positive deformation in split form** of a split positive filtered deformation. -/
def posDef (h1 : G.IsHom 0 (1 : Λ)) : GExt.PosDef (GExt.GAlg.ofLen G h1) where
  μ := S.μ
  μ_zero := S.μ_zero_apply
  deg := S.μ_hdeg h1
  assoc := S.μAssoc_eq_zero
  unit_left _ hq a := S.μ_unit_left hq h1 a
  unit_right _ hq a := S.μ_unit_right hq h1 a

omit S in
theorem ofLen_nonneg (h1 : G.IsHom 0 (1 : Λ)) : ∀ q ∈ (GExt.GAlg.ofLen G h1).gr.supp, 0 ≤ q := by
  intro q hq
  change q ∈ (Finset.range G.N).map Nat.castEmbedding at hq
  obtain ⟨d, -, rfl⟩ := Finset.mem_map.1 hq
  exact Nat.cast_nonneg d

/-- **The total product of the split form is the transported product.** -/
theorem tot_eq_star (h1 : G.IsHom 0 (1 : Λ)) (a b : Λ) : (S.posDef h1).tot a b = S.star a b := by
  set C := GExt.degBound (GExt.GAlg.ofLen G h1).gr
  have hz1 : ∀ q, C < q → S.μ q = 0 := fun q hq ↦
    (S.posDef h1).μ_eq_zero (ofLen_nonneg h1) hq
  have hz2 : ∀ q, G.N ≤ q → S.μ q = 0 := fun q hq ↦ S.μ_eq_zero hq
  have ext : ∀ K, (∀ q, K ≤ q → S.μ q a b = 0) →
      ∑ q ∈ range K, S.μ q a b = ∑ q ∈ range (C + 1 + G.N), S.μ q a b := by
    intro K hK
    rcases le_or_gt K (C + 1 + G.N) with h | h
    · rw [← Finset.sum_range_add_sum_Ico _ h, Finset.sum_eq_zero (s := Finset.Ico _ _)
        (fun q hq ↦ hK q (Finset.mem_Ico.1 hq).1), add_zero]
    · rw [← Finset.sum_range_add_sum_Ico _ h.le, Finset.sum_eq_zero (s := Finset.Ico _ _)
        (fun q hq ↦ by rw [hz2 q (by have := (Finset.mem_Ico.1 hq).1; omega)]; rfl), add_zero]
  rw [S.star_eq_sum, ext G.N (fun q hq ↦ by rw [hz2 q hq]; rfl)]
  have : (S.posDef h1).tot a b = ∑ q ∈ range (C + 1), S.μ q a b := by
    simp only [GExt.PosDef.tot, LinearMap.sum_apply]; rfl
  rw [this, ext (C + 1) (fun q hq ↦ by rw [hz1 q (by omega)]; rfl)]

end Split

/-! ### Filtered lifts of graded modules -/

section Lifts

variable {M : Type*} [AddCommGroup M] [Module k M] (h1 : G.IsHom 0 (1 : Λ))
  (MM : GExt.GMod (GExt.GAlg.ofLen G h1) M)

/-- **A filtered lift of `M` to `B` with associated graded module `M`**
(`positive-deformations.tex`): a right `B`-action on the graded space `M` such that `F^d B`
raises internal degree by at least `d`, with leading term the action of `Λ` through `σ_d`. -/
structure FLift where
  act : M →ₗ[k] B →ₗ[k] M
  mul : ∀ m x y, act (act m x) y = act m (x * y)
  one : ∀ m, act m 1 = m
  filt : ∀ (d : ℕ) (p : ℤ) (m : M) (x : B), x ∈ P.F d → MM.gr.IsHom p m →
    ∀ e, e < p + d → MM.gr.proj e (act m x) = 0
  lead : ∀ (d : ℕ) (p : ℤ) (m : M) (x : B), x ∈ P.F d → MM.gr.IsHom p m →
    MM.gr.proj (p + d) (act m x) = MM.act m (P.σ d x)

variable {P h1 MM}

/-- The filtered lift of a lifted action family. -/
def Split.fLift (S : Split P) (L : GExt.ActFam (S.posDef h1) MM) : FLift P h1 MM where
  act := L.tot.compl₂ S.φ.symm.toLinearMap
  mul m x y := by
    simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
    rw [L.tot_assoc (Split.ofLen_nonneg h1), S.tot_eq_star, Split.star_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  one m := by
    simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
    rw [show S.φ.symm 1 = 1 by rw [LinearEquiv.symm_apply_eq, S.one], L.tot_one]
  filt d p m x hx hm e he := by
    simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
    have ha : G.Ge d (S.φ.symm x) := (S.mem_F_iff).1 (by rwa [LinearEquiv.apply_symm_apply])
    rw [G.eq_sum_proj_of_ge ha, map_sum, map_sum]
    refine Finset.sum_eq_zero fun f hf ↦ ?_
    have hf' := (Finset.mem_Ico.1 hf).1
    simp only [GExt.ActFam.tot, LinearMap.sum_apply, map_sum]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    have hdeg := L.deg n p f m (S.φ.symm x |> G.proj f) hm
      ((GExt.ZGr.ofLen_isHom G f _).2 (G.isHom_proj f _))
    rw [MM.gr.proj_of_isHom hdeg, if_neg (by omega)]
  lead d p m x hx hm := by
    simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
    have ha : G.Ge d (S.φ.symm x) := (S.mem_F_iff).1 (by rwa [LinearEquiv.apply_symm_apply])
    have hσ : P.σ d x = G.proj d (S.φ.symm x) := by
      rw [← S.σ_ge ha, LinearEquiv.apply_symm_apply]
    rw [hσ]
    conv_lhs => rw [G.eq_sum_proj_of_ge ha, map_sum, map_sum]
    by_cases hdN : ¬ d < G.N
    · have h0 : G.proj d = 0 := G.proj_ge d (by omega)
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, h0, LinearMap.zero_apply, map_zero]
    push_neg at hdN
    rw [Finset.sum_eq_single d]
    · simp only [GExt.ActFam.tot, LinearMap.sum_apply, map_sum]
      rw [Finset.sum_eq_single 0]
      · rw [L.ν_zero, MM.gr.proj_of_isHom (MM.act_hom _ _ _ _ hm
          ((GExt.ZGr.ofLen_isHom G d _).2 (G.isHom_proj d _))), if_pos rfl]
      · intro n _ hn
        have hdeg := L.deg n p d m (S.φ.symm x |> G.proj d) hm
          ((GExt.ZGr.ofLen_isHom G d _).2 (G.isHom_proj d _))
        rw [MM.gr.proj_of_isHom hdeg, if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    · intro f hf hfd
      have hf' := (Finset.mem_Ico.1 hf).1
      simp only [GExt.ActFam.tot, LinearMap.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun n _ ↦ ?_
      have hdeg := L.deg n p f m (S.φ.symm x |> G.proj f) hm
        ((GExt.ZGr.ofLen_isHom G f _).2 (G.isHom_proj f _))
      rw [MM.gr.proj_of_isHom hdeg, if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_Ico.2 ⟨le_rfl, hdN⟩) h

/-- **Proposition 6.5(1), existence**: under `Ext²_Λ(M, M)_t = 0` for `t > 0`, `M` has a
filtered lift to `B` with associated graded module `M`. -/
theorem exists_fLift_of_split (hS : Nonempty (Split P)) (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM MM 1 t) :
    Nonempty (FLift P h1 MM) := by
  obtain ⟨S⟩ := hS
  obtain ⟨L⟩ := GExt.exists_actFam MM (S.posDef h1) (Split.ofLen_nonneg h1) hExt
  exact ⟨S.fLift L⟩


theorem exists_fLift (V : Vertices G) : ∀ (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM MM 1 t),
    Nonempty (FLift P h1 MM) :=
  exists_fLift_of_split (P.nonempty_split V)

end Lifts

end PosFiltration

namespace GExt

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Extracting the degree-`d₀ + n` part of a double sum of homogeneous terms. -/
theorem ZGr.proj_box (g : ZGr (R := R) M) (d₀ : ℤ) (K₁ K₂ : ℕ) (X : ℕ → ℕ → M)
    (hX : ∀ i j : ℕ, g.IsHom (d₀ + i + j) (X i j))
    (hz1 : ∀ i j, K₁ ≤ i → X i j = 0) (hz2 : ∀ i j, K₂ ≤ j → X i j = 0) (n : ℕ) :
    g.proj (d₀ + n) (∑ i ∈ Finset.range K₁, ∑ j ∈ Finset.range K₂, X i j) =
      ∑ x ∈ antidiagonal n, X x.1 x.2 := by
  classical
  have hbox := sum_range_ad_box' K₁ K₂ (K₁ + K₂ + 1 + n) (by omega) X
    (fun i j hi ↦ hz1 i j (by omega)) (fun i j hj ↦ hz2 i j (by omega))
  have e1 : ∑ i ∈ Finset.range (K₁ + 1), ∑ j ∈ Finset.range (K₂ + 1), X i j =
      ∑ i ∈ Finset.range K₁, ∑ j ∈ Finset.range K₂, X i j := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j _ ↦ hz1 K₁ j le_rfl), add_zero]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [Finset.sum_range_succ, hz2 i K₂ le_rfl, add_zero]
  rw [← e1, ← hbox, map_sum, Finset.sum_eq_single n]
  · rw [map_sum]
    exact Finset.sum_congr rfl fun x hx ↦ by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [g.proj_of_isHom (hX x.1 x.2), if_pos (by push_cast [← this]; ring)]
  · intro m _ hm
    rw [map_sum]
    exact Finset.sum_eq_zero fun x hx ↦ by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [g.proj_of_isHom (hX x.1 x.2), if_neg (by intro h; apply hm; push_cast [← this] at h; omega)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

end GExt

namespace PosFiltration

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] {P : PosFiltration G B}
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {h1 : G.IsHom 0 (1 : Λ)} {MM : GExt.GMod (GExt.GAlg.ofLen G h1) M}
  {NN : GExt.GMod (GExt.GAlg.ofLen G h1) N}

/-- Bilinear maps agreeing on homogeneous inputs agree. -/
theorem bilin_ext {f g : M →ₗ[k] Λ →ₗ[k] N}
    (h : ∀ (p : ℤ) (q : ℕ) m a, MM.gr.IsHom p m → G.IsHom q a → f m a = g m a) : f = g := by
  refine MM.gr.ext_of_hom (f := f) (f' := g) fun p m hm ↦ LinearMap.ext fun a ↦ ?_
  rw [G.sum a, map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ ↦ h p q m _ hm (G.isHom_proj q a)

/-- The degree-`n` part of a filtered lift. -/
def FLift.ν (S : Split P) (A : FLift P h1 MM) (n : ℕ) : M →ₗ[k] Λ →ₗ[k] M :=
  LinearMap.mk₂ k
    (fun m a ↦ ∑ p ∈ MM.gr.supp, ∑ q ∈ Finset.range G.N,
      MM.gr.proj (p + q + n) (A.act (MM.gr.proj p m) (S.φ (G.proj q a))))
    (fun m m' a ↦ by simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c m a ↦ by simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum])
    (fun m a a' ↦ by simp only [map_add, Finset.sum_add_distrib])
    (fun c m a ↦ by simp only [map_smul, Finset.smul_sum])

theorem FLift.ν_hom (S : Split P) (A : FLift P h1 MM) (n : ℕ) {p : ℤ} {q : ℕ} {m : M} {a : Λ}
    (hm : MM.gr.IsHom p m) (ha : G.IsHom q a) :
    A.ν S n m a = MM.gr.proj (p + q + n) (A.act m (S.φ a)) := by
  classical
  simp only [FLift.ν, LinearMap.mk₂_apply]
  by_cases hp : p ∈ MM.gr.supp
  · by_cases hq : q < G.N
    · rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
      · rw [MM.gr.proj_of_isHom hm, if_pos rfl, G.proj_of_isHom ha, if_pos rfl]
      · intro q' _ hq'
        rw [G.proj_of_isHom ha, if_neg (Ne.symm hq'), map_zero, map_zero, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 hq) h
      · intro p' _ hp'
        refine Finset.sum_eq_zero fun q' _ ↦ ?_
        rw [MM.gr.proj_of_isHom hm, if_neg (Ne.symm hp'), map_zero, LinearMap.zero_apply,
          map_zero]
      · intro h; exact absurd hp h
    · rw [G.isHom_zero_of_ge ha (by omega)]
      simp
  · rw [MM.gr.eq_zero_of_isHom_out hm hp]
    simp

/-- **A filtered lift is the sum of its parts.** -/
theorem FLift.act_eq_sum (S : Split P) (A : FLift P h1 MM) {p : ℤ} {q : ℕ} {m : M} {a : Λ}
    (hm : MM.gr.IsHom p m) (ha : G.IsHom q a) :
    A.act m (S.φ a) = ∑ i ∈ Finset.range (2 * GExt.degBound MM.gr + 1), A.ν S i m a := by
  classical
  by_cases hp : p ∈ MM.gr.supp
  · set X := A.act m (S.φ a)
    set K := 2 * GExt.degBound MM.gr + 1
    have hx : S.φ a ∈ P.F q := (S.mem_F_iff).2 (G.ge_of_isHom ha)
    rw [Finset.sum_congr rfl fun i _ ↦ A.ν_hom S i hm ha]
    set T := (Finset.range K).image (fun i : ℕ ↦ p + q + i)
    have hinj : Set.InjOn (fun i : ℕ ↦ p + q + (i : ℤ)) (Finset.range K) := by
      intro i _ j _ h; simp only at h; omega
    rw [← Finset.sum_image (f := fun e ↦ MM.gr.proj e X) hinj]
    conv_lhs => rw [MM.gr.sum X]
    have e1 : ∑ e ∈ MM.gr.supp, MM.gr.proj e X = ∑ e ∈ MM.gr.supp ∪ T, MM.gr.proj e X :=
      Finset.sum_subset Finset.subset_union_left (fun e _ he ↦ by
        rw [MM.gr.proj_out e he, LinearMap.zero_apply])
    have e2 : ∑ e ∈ T, MM.gr.proj e X = ∑ e ∈ MM.gr.supp ∪ T, MM.gr.proj e X :=
      Finset.sum_subset Finset.subset_union_right (fun e he heT ↦ by
        rcases Finset.mem_union.1 he with he | he
        · by_cases hlt : e < p + q
          · exact A.filt q p m _ hx hm e hlt
          · exfalso
            apply heT
            have h1 := GExt.le_degBound hp
            have h2 := GExt.le_degBound he
            rw [abs_le] at h1 h2
            refine Finset.mem_image.2 ⟨(e - p - q).toNat, Finset.mem_range.2 (by omega), by omega⟩
        · exact absurd he heT)
    rw [e1, e2]
  · rw [MM.gr.eq_zero_of_isHom_out hm hp, map_zero, LinearMap.zero_apply]
    exact (Finset.sum_eq_zero fun i _ ↦ by rw [map_zero, LinearMap.zero_apply]).symm

theorem FLift.ν_shift (S : Split P) (A : FLift P h1 MM) (n : ℕ) : GExt.IsShift MM n (A.ν S n) := by
  intro p q m a hm ha
  rcases lt_or_ge q 0 with hq | hq
  · rw [(GExt.ZGr.ofLen_isHom_neg G hq a).1 ha, map_zero]
    exact MM.gr.isHom_zero _
  obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  change (GExt.ZGr.ofLen G).IsHom e a at ha
  rw [GExt.ZGr.ofLen_isHom] at ha
  rw [A.ν_hom S n hm ha]
  exact MM.gr.isHom_proj _ _

theorem FLift.ν_zero (S : Split P) (A : FLift P h1 MM) (m : M) (a : Λ) :
    A.ν S 0 m a = MM.act m a := by
  have := bilin_ext (MM := MM) (f := A.ν S 0) (g := MM.act) fun p q m a hm ha ↦ by
    rw [A.ν_hom S 0 hm ha, Nat.cast_zero, add_zero,
      A.lead q p m _ ((S.mem_F_iff).2 (G.ge_of_isHom ha)) hm, S.σφ q a ha]
  rw [this]

/-- **The action family of a filtered lift.** -/
def FLift.toActFam (S : Split P) (A : FLift P h1 MM) : GExt.ActFam (S.posDef h1) MM where
  ν := A.ν S
  ν_zero := A.ν_zero S
  deg := A.ν_shift S
  assoc n m a b := by
    refine GExt.assocErr_eq_zero_of_hom (MM := MM) (A.ν S) (S.posDef h1).μ n
      (fun p q r m a b hm ha hb ↦ ?_) m a b
    rcases lt_or_ge q 0 with hq | hq
    · rw [(GExt.ZGr.ofLen_isHom_neg G hq a).1 ha]
      simpa using GExt.assocErr_smul_mid (A.ν S) (S.posDef h1).μ n (0 : k) m (0 : Λ) b
    rcases lt_or_ge r 0 with hr | hr
    · rw [(GExt.ZGr.ofLen_isHom_neg G hr b).1 hb]
      simpa using GExt.assocErr_smul_right (A.ν S) (S.posDef h1).μ n (0 : k) m a (0 : Λ)
    obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    obtain ⟨f, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    change (GExt.ZGr.ofLen G).IsHom e a at ha
    change (GExt.ZGr.ofLen G).IsHom f b at hb
    rw [GExt.ZGr.ofLen_isHom] at ha hb
    set K := 2 * GExt.degBound MM.gr + 1
    have hnn := Split.ofLen_nonneg (G := G) h1
    have hνz : ∀ i, K ≤ i → A.ν S i = 0 := fun i hi ↦
      GExt.shift_eq_zero hnn (A.ν_shift S i) (by omega)
    have hl : A.act (A.act m (S.φ a)) (S.φ b) =
        ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, A.ν S j (A.ν S i m a) b := by
      rw [A.act_eq_sum S hm ha, map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ ↦
        A.act_eq_sum S (A.ν_shift S i p e m a hm ((GExt.ZGr.ofLen_isHom G e a).2 ha)) hb
    have hr' : A.act m (S.φ (S.star a b)) =
        ∑ q ∈ Finset.range G.N, ∑ i ∈ Finset.range K, A.ν S i m (S.μ q a b) := by
      rw [S.star_eq_sum a b, map_sum, map_sum]
      exact Finset.sum_congr rfl fun q _ ↦ A.act_eq_sum S hm (S.μ_isHom ha hb)
    have hmul : A.act (A.act m (S.φ a)) (S.φ b) = A.act m (S.φ (S.star a b)) := by
      rw [A.mul, Split.φ_star]
    rw [hl, hr'] at hmul
    have h2 := congrArg (MM.gr.proj (p + e + f + n)) hmul
    rw [GExt.ZGr.proj_box MM.gr (p + e + f) K K (fun i j ↦ A.ν S j (A.ν S i m a) b)
      (fun i j ↦ by
        have := A.ν_shift S j _ f _ b (A.ν_shift S i p e m a hm
          ((GExt.ZGr.ofLen_isHom G e a).2 ha)) ((GExt.ZGr.ofLen_isHom G f b).2 hb)
        convert this using 1; ring)
      (fun i j hi ↦ by rw [hνz i hi]; simp) (fun i j hj ↦ by rw [hνz j hj]; simp) n] at h2
    rw [GExt.ZGr.proj_box MM.gr (p + e + f) G.N K (fun q i ↦ A.ν S i m (S.μ q a b))
      (fun q i ↦ by
        have := A.ν_shift S i p (e + f + q : ℕ) m _ hm
          ((GExt.ZGr.ofLen_isHom G _ _).2 (S.μ_isHom ha hb))
        convert this using 1; push_cast; ring)
      (fun q i hq ↦ by rw [S.μ_eq_zero hq]; simp) (fun q i hi ↦ by rw [hνz i hi]; simp) n] at h2
    unfold GExt.assocErr
    rw [h2, sub_eq_zero]
    exact (Finset.Nat.sum_antidiagonal_swap
      (f := fun x : ℕ × ℕ ↦ A.ν S x.2 m (S.μ x.1 a b))).symm

theorem FLift.toActFam_tot (S : Split P) (A : FLift P h1 MM) (m : M) (a : Λ) :
    (A.toActFam S).tot m a = A.act m (S.φ a) := by
  have := bilin_ext (MM := MM) (f := (A.toActFam S).tot) (g := A.act.compl₂ S.φ.toLinearMap)
    fun p q m a hm ha ↦ by
      simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
      rw [A.act_eq_sum S hm ha]
      simp only [GExt.ActFam.tot, LinearMap.sum_apply]
      rfl
  have h2 := LinearMap.congr_fun (LinearMap.congr_fun this m) a
  simpa using h2

section Statements

variable (hS : Nonempty (Split P))

include hS in
/-- **Proposition 6.5(1), uniqueness**: under `Ext¹_Λ(M, M)_t = 0` for `t > 0`, two filtered
lifts of `M` are isomorphic by a `B`-linear isomorphism with leading term the identity. -/
theorem fLift_unique_of_split (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM MM 0 t) (A A' : FLift P h1 MM) :
    ∃ Φ : M ≃ₗ[k] M, (∀ m x, Φ (A.act m x) = A'.act (Φ m) x) ∧
      ∀ p m, MM.gr.IsHom p m → ∀ e, e ≤ p → MM.gr.proj e (Φ m) = if e = p then m else 0 := by
  obtain ⟨S⟩ := hS
  have hnn := Split.ofLen_nonneg (G := G) h1
  obtain ⟨F, hF0, hF, hFa⟩ := GExt.exists_liftMap (S.posDef h1) (A.toActFam S) (A'.toActFam S)
    (r := 0) LinearMap.id (fun m a ↦ rfl) (fun p m hm ↦ by simpa using hm) hnn
    (fun t ht ↦ by simpa using hExt t ht)
  let Φ := LinearEquiv.ofBijective (GExt.mapTot MM MM 0 F) (GExt.mapTot_bijective hF0 hF)
  refine ⟨Φ, fun m x ↦ ?_, fun p m hm e he ↦ ?_⟩
  · have h := GExt.mapTot_comm hnn (A.toActFam S) (A'.toActFam S) hF hFa m (S.φ.symm x)
    rw [A.toActFam_tot, A'.toActFam_tot, LinearEquiv.apply_symm_apply] at h
    exact h
  · change MM.gr.proj e (GExt.mapTot MM MM 0 F m) = _
    simp only [GExt.mapTot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_eq_single 0]
    · rw [hF0, LinearMap.id_apply, MM.gr.proj_of_isHom hm]
      by_cases h : e = p
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    · intro i _ hi
      rw [MM.gr.proj_of_isHom (hF i p m hm), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

include hS in
/-- **Proposition 6.5(2), lifts of maps**: under `Ext¹_Λ(M, N)_{r+t} = 0` for `t > 0`, a
homogeneous `Λ`-linear map of degree `r ≥ 0` lifts to a `B`-linear map of the filtered lifts,
of filtration order `r`, with leading term the given map. -/
theorem fLift_map_of_split (A : FLift P h1 MM) (A' : FLift P h1 NN) (r : ℕ) (f : M →ₗ[k] N)
    (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))
    (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM NN 0 (r + t)) :
    ∃ Φ : M →ₗ[k] N, (∀ m x, Φ (A.act m x) = A'.act (Φ m) x) ∧ GExt.OrderGe MM NN r Φ ∧
      GExt.ZGr.comp MM.gr NN.gr r Φ = f := by
  obtain ⟨S⟩ := hS
  have hnn := Split.ofLen_nonneg (G := G) h1
  obtain ⟨F, hF0, hF, hFa⟩ := GExt.exists_liftMap (S.posDef h1) (A.toActFam S) (A'.toActFam S)
    f hf hfd hnn hExt
  refine ⟨GExt.mapTot MM NN r F, fun m x ↦ ?_, fun p m hm d hd ↦ ?_, ?_⟩
  · have h := GExt.mapTot_comm hnn (A.toActFam S) (A'.toActFam S) hF hFa m (S.φ.symm x)
    rw [A.toActFam_tot, A'.toActFam_tot, LinearEquiv.apply_symm_apply] at h
    exact h
  · simp only [GExt.mapTot, LinearMap.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [NN.gr.proj_of_isHom (hF i p m hm), if_neg (by omega)]
  · refine MM.gr.ext_of_hom fun p m hm ↦ ?_
    rw [GExt.ZGr.comp_hom MM.gr NN.gr _ hm]
    simp only [GExt.mapTot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_eq_single 0]
    · rw [hF0, NN.gr.proj_of_isHom (hfd p m hm), if_pos rfl]
    · intro i _ hi
      rw [NN.gr.proj_of_isHom (hF i p m hm), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

include hS in
/-- **Proposition 6.5(2), leading terms**: the leading term of a `B`-linear map of filtration
order `r` between filtered lifts is a homogeneous `Λ`-linear map of degree `r`. -/
theorem fLift_leading_of_split (A : FLift P h1 MM) (A' : FLift P h1 NN) {r : ℤ} (g : M →ₗ[k] N)
    (hg : ∀ m x, g (A.act m x) = A'.act (g m) x) (hord : GExt.OrderGe MM NN r g) (m : M) (a : Λ) :
    GExt.ZGr.comp MM.gr NN.gr r g (MM.act m a) = NN.act (GExt.ZGr.comp MM.gr NN.gr r g m) a := by
  obtain ⟨S⟩ := hS
  have hnn := Split.ofLen_nonneg (G := G) h1
  refine GExt.leading_linear hnn (A.toActFam S) (A'.toActFam S) (fun m a ↦ ?_) hord m a
  rw [A.toActFam_tot, A'.toActFam_tot, hg]

/-- Every map of the lifts has some (negative) filtration order. -/
theorem orderGe_bot (g : M →ₗ[k] N) :
    GExt.OrderGe MM NN (-(GExt.degBound MM.gr + GExt.degBound NN.gr + 1 : ℕ)) g := by
  intro p m hm d hd
  by_cases hp : p ∈ MM.gr.supp
  · rw [NN.gr.proj_out d fun hmem ↦ by
      have h1 := GExt.le_degBound hp
      have h2 := GExt.le_degBound hmem
      rw [abs_le] at h1 h2
      push_cast at hd
      omega]
    rfl
  · rw [MM.gr.eq_zero_of_isHom_out hm hp, map_zero, map_zero]

theorem orderGe_succ {r : ℤ} {g : M →ₗ[k] N} (hord : GExt.OrderGe MM NN r g)
    (h0 : GExt.ZGr.comp MM.gr NN.gr r g = 0) : GExt.OrderGe MM NN (r + 1) g := by
  intro p m hm d hd
  rcases lt_or_eq_of_le (show d ≤ p + r by omega) with h | h
  · exact hord p m hm d h
  · rw [h, ← GExt.ZGr.comp_hom MM.gr NN.gr g hm, h0, LinearMap.zero_apply]

include hS in
/-- **Proposition 6.5(3), first part**: if the graded `Hom_Λ(M, N)` vanishes in negative
degrees, every `B`-linear map of the lifts has filtration order `≥ 0`. -/
theorem fLift_orderGe_zero_of_split (A : FLift P h1 MM) (A' : FLift P h1 NN)
    (hneg : ∀ r : ℤ, r < 0 → ∀ f : M →ₗ[k] N, (∀ m a, f (MM.act m a) = NN.act (f m) a) →
      (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m)) → f = 0)
    (g : M →ₗ[k] N) (hg : ∀ m x, g (A.act m x) = A'.act (g m) x) : GExt.OrderGe MM NN 0 g := by
  set r₀ : ℕ := GExt.degBound MM.gr + GExt.degBound NN.gr + 1
  have key : ∀ t : ℕ, t ≤ r₀ → GExt.OrderGe MM NN (-(r₀ : ℤ) + t) g := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Nat.cast_zero, add_zero]
      exact orderGe_bot (MM := MM) (NN := NN) g
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have h0 := hneg (-(r₀ : ℤ) + t) (by omega) _
        (fun m a ↦ fLift_leading_of_split hS A A' g hg hprev m a)
        (fun p m hm ↦ GExt.ZGr.comp_isHom MM.gr NN.gr g hm)
      have := orderGe_succ hprev h0
      rwa [show -(r₀ : ℤ) + t + 1 = -(r₀ : ℤ) + ((t + 1 : ℕ) : ℤ) by push_cast; ring] at this
  simpa using key r₀ le_rfl

include hS in
/-- **Proposition 6.5(2), the associated graded Hom spaces**: for `r ≥ 0`, a `B`-linear map of
order `r` has leading term zero exactly when it has order `r + 1`, and every homogeneous
`Λ`-linear map of degree `r` is a leading term. -/
theorem fLift_gr_hom_of_split (A : FLift P h1 MM) (A' : FLift P h1 NN) (r : ℕ)
    (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM NN 0 (r + t)) :
    (∀ g : M →ₗ[k] N, GExt.OrderGe MM NN r g →
      (GExt.ZGr.comp MM.gr NN.gr r g = 0 ↔ GExt.OrderGe MM NN (r + 1) g)) ∧
    ∀ f : M →ₗ[k] N, (∀ m a, f (MM.act m a) = NN.act (f m) a) →
      (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m)) →
      ∃ g : M →ₗ[k] N, (∀ m x, g (A.act m x) = A'.act (g m) x) ∧ GExt.OrderGe MM NN r g ∧
        GExt.ZGr.comp MM.gr NN.gr r g = f := by
  refine ⟨fun g hord ↦ ⟨fun h0 ↦ orderGe_succ hord h0, fun h1' ↦ ?_⟩,
    fun f hf hfd ↦ fLift_map_of_split hS A A' r f hf hfd hExt⟩
  refine MM.gr.ext_of_hom fun p m hm ↦ ?_
  rw [GExt.ZGr.comp_hom MM.gr NN.gr g hm, LinearMap.zero_apply]
  exact h1' p m hm _ (by omega)

/-! The forms with vertex idempotents (`S = Λ₀ ≅ kⁿ`); for a split semisimple `S` the splitting is
`PosFiltration.nonempty_split_ss`. -/

theorem fLift_unique (V : Vertices G) : ∀ (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM MM 0 t) (A A' : FLift P h1 MM),
    ∃ Φ : M ≃ₗ[k] M, (∀ m x, Φ (A.act m x) = A'.act (Φ m) x) ∧
      ∀ p m, MM.gr.IsHom p m → ∀ e, e ≤ p → MM.gr.proj e (Φ m) = if e = p then m else 0 :=
  fLift_unique_of_split (P.nonempty_split V)

theorem fLift_map (V : Vertices G) : ∀ (A : FLift P h1 MM) (A' : FLift P h1 NN) (r : ℕ) (f : M →ₗ[k] N)
    (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))
    (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM NN 0 (r + t)),
    ∃ Φ : M →ₗ[k] N, (∀ m x, Φ (A.act m x) = A'.act (Φ m) x) ∧ GExt.OrderGe MM NN r Φ ∧
      GExt.ZGr.comp MM.gr NN.gr r Φ = f :=
  fLift_map_of_split (P.nonempty_split V)

theorem fLift_leading (V : Vertices G) : ∀ (A : FLift P h1 MM) (A' : FLift P h1 NN) {r : ℤ} (g : M →ₗ[k] N)
    (hg : ∀ m x, g (A.act m x) = A'.act (g m) x) (hord : GExt.OrderGe MM NN r g) (m : M) (a : Λ),
    GExt.ZGr.comp MM.gr NN.gr r g (MM.act m a) = NN.act (GExt.ZGr.comp MM.gr NN.gr r g m) a :=
  fLift_leading_of_split (P.nonempty_split V)

theorem fLift_orderGe_zero (V : Vertices G) : ∀ (A : FLift P h1 MM) (A' : FLift P h1 NN)
    (hneg : ∀ r : ℤ, r < 0 → ∀ f : M →ₗ[k] N, (∀ m a, f (MM.act m a) = NN.act (f m) a) →
      (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m)) → f = 0)
    (g : M →ₗ[k] N) (hg : ∀ m x, g (A.act m x) = A'.act (g m) x),
    GExt.OrderGe MM NN 0 g :=
  fLift_orderGe_zero_of_split (P.nonempty_split V)

theorem fLift_gr_hom (V : Vertices G) : ∀ (A : FLift P h1 MM) (A' : FLift P h1 NN) (r : ℕ)
    (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM NN 0 (r + t)),
    (∀ g : M →ₗ[k] N, GExt.OrderGe MM NN r g →
      (GExt.ZGr.comp MM.gr NN.gr r g = 0 ↔ GExt.OrderGe MM NN (r + 1) g)) ∧
    ∀ f : M →ₗ[k] N, (∀ m a, f (MM.act m a) = NN.act (f m) a) →
      (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m)) →
      ∃ g : M →ₗ[k] N, (∀ m x, g (A.act m x) = A'.act (g m) x) ∧ GExt.OrderGe MM NN r g ∧
        GExt.ZGr.comp MM.gr NN.gr r g = f :=
  fLift_gr_hom_of_split (P.nonempty_split V)

end Statements

end PosFiltration

end MultiplicativeBasisDeformations
