module

public import MultiplicativeBasisDeformations.Foundations.FiltrationRays
public import MultiplicativeBasisDeformations.Foundations.FinalStandardness

/-!
# Initial forms identify ray products (Proposition 8.3(2), Theorem 11.8(1))

`local-ray-geometry.tex` (`prop:dimension-induction`(2)): "The initial-form bijection of
Lemma 3.7 identifies the products in `ray A` and `ray A₀`." Theorem 11.8(1) uses the same
identification.

For the categorical filtration `J` of `A` (`posFiltA`), Lemma 3.7 (`rayDegree_J`) gives the
initial-form bijection between the rays of a corner and the nonzero pieces `A₀(x,y)_d`. Here:
for nonzero `f ∈ A(x,y)`, `g ∈ A(y,z)` of degrees `d`, `e`, the ray product `[f][g]` is nonzero
(`fg ∉ M(f,g)`) iff the product of the initial forms `σ_d f · σ_e g` is nonzero, and then
`σ_{d+e}(fg) = σ_d f · σ_e g` (`IndSkeleton.initialForm_products`).

One direction holds for every positive filtered deformation whose radical lies in degree one
(`mul_not_mem_of_σ`: `M(f,g) ⊆ F^{d+e+1}`). For the converse we count: the initial forms of
the rays of a presentation of `A` by the table `P` of `A₀` (`rayA_eq_rayA0`) give a
bijection `θ` of the rays of `P` (`thetaR`) under which every nonzero product of `P` comes
from a nonzero product of `A`; both tables have the same number of nonzero products, so the
two sets of pairs coincide.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace PosFiltration

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)
  [IsAlgClosed k] [FiniteDimensional k B] (F : PrimitiveIdempotents B)

theorem σ_mul3 {d : ℕ} (a f c : B) (hf : f ∈ P.F d) :
    P.σ d (a * f * c) = P.σ 0 a * P.σ d f * P.σ 0 c := by
  have h1 := P.σ_mul 0 d a f (P.mem_zero _) hf
  have h2 := P.σ_mul (0 + d) 0 (a * f) c (P.F_mul 0 d _ _ (P.mem_zero _) hf) (P.mem_zero _)
  simp only [Nat.zero_add, Nat.add_zero] at h1 h2
  rw [h2, h1]

/-- **The initial form of a corner unit is a nonzero multiple of the idempotent.** -/
theorem σ_cornerUnit (hP : P.RadOne) {x : Fin F.m} {u : B} (hu : F.IsCornerUnit (k := k) x u) :
    ∃ c : k, c ≠ 0 ∧ P.σ 0 u = c • P.σ 0 (F.e x) := by
  obtain ⟨c, hc, hn⟩ := F.exists_unit_decomp hu
  refine ⟨c, hc, ?_⟩
  have h1 : u - c • F.e x ∈ P.F (0 + 1) := hP hn.2
  have := (P.σ_ker 0 _ (P.mem_zero _)).2 h1
  rwa [map_sub, map_smul, sub_eq_zero] at this

/-- **`M(f, h) ⊆ F^{d+e+1}`.** -/
theorem insertionSpan_le_F (hP : P.RadOne) {x y z : Fin F.m} {f h : B} {d e : ℕ}
    (hf : f ∈ P.F d) (hh : h ∈ P.F e) :
    F.insertionSpan (k := k) x y z f h ≤ P.F (d + e + 1) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, -, r, hr, c, -, rfl⟩
  show a * f * r * h * c ∈ P.F (d + e + 1)
  have h1 : f * r ∈ P.F (d + 1) := P.F_mul_rad hP d hr.2 hf
  have h2 : f * r * h ∈ P.F (d + 1 + e) := P.F_mul _ _ _ _ h1 hh
  rw [show d + 1 + e = d + e + 1 by omega] at h2
  have h3 := P.mul_mem_left a h2
  rw [← mul_assoc, ← mul_assoc] at h3
  exact P.mul_mem_right c (show a * f * r * h ∈ P.F (d + e + 1) by
    simpa only [mul_assoc] using h3)

/-- **If the initial forms multiply to a nonzero element, the ray product is nonzero with that
initial form.** -/
theorem mul_not_mem_of_σ (hP : P.RadOne) {x y z : Fin F.m} {f h : B} {d e : ℕ}
    (hf : f ∈ P.F d) (hh : h ∈ P.F e) (hσ : P.σ d f * P.σ e h ≠ 0) :
    f * h ∉ F.insertionSpan (k := k) x y z f h ∧ f * h ∈ P.F (d + e) ∧
      f * h ∉ P.F (d + e + 1) ∧ P.σ (d + e) (f * h) = P.σ d f * P.σ e h := by
  have hσfh := P.σ_mul d e f h hf hh
  have hnot : f * h ∉ P.F (d + e + 1) := fun h1 ↦
    hσ (by rw [← hσfh]; exact (P.σ_ker _ _ (P.F_mul d e f h hf hh)).2 h1)
  exact ⟨fun hM ↦ hnot (P.insertionSpan_le_F F hP hf hh hM), P.F_mul d e f h hf hh, hnot, hσfh⟩

/-- **Elements of a ray have proportional initial forms.** -/
theorem σ_of_mem_ray (hP : P.RadOne) {x y : Fin F.m} {f f' : B} (hfc : f ∈ F.corner (k := k) x y)
    (hf' : f' ∈ F.ray (k := k) x y f) {d : ℕ} (hf : f ∈ P.F d) :
    f' ∈ P.F d ∧ ∃ c : k, c ≠ 0 ∧ P.σ d f' = c • P.σ d f := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hf'
  refine ⟨P.mul_mem_right _ (P.mul_mem_left _ hf), ?_⟩
  obtain ⟨c, hc, hcu⟩ := P.σ_cornerUnit F hP hu
  obtain ⟨c', hc', hcw⟩ := P.σ_cornerUnit F hP hw
  refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
  have he : P.σ 0 (F.e x) * P.σ d f * P.σ 0 (F.e y) = P.σ d f := by
    rw [← P.σ_mul3 _ _ _ hf, (PrimitiveIdempotents.mem_corner_iff' F).1 hfc]
  rw [P.σ_mul3 _ _ _ hf, hcu, hcw, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, he, smul_smul,
    mul_comm]

end PosFiltration

/-! ### The initial forms of the idempotents of `A` are vertex idempotents of `A₀` -/

namespace MeshWalk

open ScalarMeshCategory CatAlg

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

include hfin in
theorem isHom_of_isDiag {z : (Alg D.F0)ᵐᵒᵖ} {t : D.PV → k} (hz : IsDiag D z t) :
    (lenA0 D hfin).IsHom 0 z := by
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  change degProj c 0 p.1 q.1 (z.unop p q) = z.unop p q
  rw [degProj_of_mem c (by rw [hz p q]; exact Submodule.smul_mem _ _ (idTo_mem_degreePart D p q)),
    if_pos rfl]

theorem isDiag_one : IsDiag D 1 (fun _ ↦ 1) := fun p q ↦ by
  rw [MulOpposite.unop_one, one_apply, one_smul]

theorem isDiag_eP (p : D.PV) : IsDiag D (eP D p) (Pi.single p 1) := fun p' q' ↦ by
  change idem (F := D.F0) p p' q' = _
  simp only [idem, colAlg, unit]
  by_cases h : p' = p
  · subst h; simp
  · simp [h, idTo_ne h, Pi.single_apply]

theorem isDiag_add {z w : (Alg D.F0)ᵐᵒᵖ} {t s : D.PV → k} (hz : IsDiag D z t)
    (hw : IsDiag D w s) : IsDiag D (z + w) (t + s) := fun p q ↦ by
  rw [MulOpposite.unop_add, CatAlg.add_apply, hz p q, hw p q, Pi.add_apply, add_smul]

theorem isDiag_sum {ι : Type*} (S : Finset ι) {z : ι → (Alg D.F0)ᵐᵒᵖ} {t : ι → D.PV → k}
    (hz : ∀ i, IsDiag D (z i) (t i)) : IsDiag D (∑ i ∈ S, z i) (∑ i ∈ S, t i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro p q; simp
  | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact isDiag_add D (hz i) ih

include hfin in
theorem isDiag_coeff {z : (Alg D.F0)ᵐᵒᵖ} {t s : D.PV → k} (hz : IsDiag D z t) (hs : IsDiag D z s) :
    t = s := by
  funext p
  have := (hz p p).symm.trans (hs p p)
  rw [idTo_self, ← sub_eq_zero, ← sub_smul] at this
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right (CatAlg.MeshData.id_ne_zero (L := L) p.1))

theorem eq_of_isDiag {z w : (Alg D.F0)ᵐᵒᵖ} {t : D.PV → k} (hz : IsDiag D z t) (hw : IsDiag D w t) :
    z = w := by
  apply MulOpposite.unop_injective; apply CatAlg.ext; intro p q; rw [hz p q, hw p q]

variable {B : Type u} [Ring B] [Algebra k B] (P : PosFiltration (lenA0 D hfin) B)

theorem σ_zero_one : P.σ 0 1 = 1 := by
  obtain ⟨a, -, ha⟩ := P.σ_surj 0 1 (isHom_of_isDiag D hfin (isDiag_one D))
  have := P.σ_zero_mul 1 a
  rw [one_mul, ha, mul_one] at this
  exact this.symm

variable [IsAlgClosed k] [FiniteDimensional k B] (F : PrimitiveIdempotents B)

theorem σ_e_ne_zero (x : Fin F.m) : P.σ 0 (F.e x) ≠ 0 := by
  intro h
  have h1 : F.e x ∈ P.F 1 := by simpa using (P.σ_ker 0 _ (P.mem_zero _)).1 h
  have hpow : ∀ n, F.e x ∈ P.F (n + 1) := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
        have := P.F_mul (n + 1) 1 _ _ ih h1
        rwa [(F.complete.idem x).eq] at this
  apply (F.primitive x).2.1
  have := P.F_succ_le P.M (hpow P.M)
  rwa [P.F_M, Submodule.mem_bot] at this

theorem isDiag_zero : IsDiag D 0 0 := fun p q ↦ by
  rw [MulOpposite.unop_zero, CatAlg.zero_apply, Pi.zero_apply, zero_smul]

/-- **Vertex matching**: the initial forms of the idempotents `e_x` are the vertex idempotents
of `A₀`, for a bijection of the vertices. -/
theorem exists_vertexMatch (hcard : Fintype.card D.PV = F.m) :
    ∃ π : Fin F.m ≃ D.PV, ∀ x, P.σ 0 (F.e x) = eP D (π x) := by
  classical
  choose t ht using fun x ↦ isDiag_of_isHom D hfin (P.σ_hom 0 (F.e x))
  have hidem : ∀ x, t x * t x = t x := fun x ↦ by
    have h1 := isDiag_mul D (ht x) (ht x)
    rw [← P.σ_zero_mul, (F.complete.idem x).eq] at h1
    exact isDiag_coeff D hfin h1 (ht x)
  have horth : ∀ x y, x ≠ y → t y * t x = 0 := fun x y hxy ↦ by
    have h1 := isDiag_mul D (ht x) (ht y)
    rw [← P.σ_zero_mul, F.complete.ortho hxy, map_zero] at h1
    exact isDiag_coeff D hfin h1 (isDiag_zero D)
  have hsum : ∑ x, t x = 1 := by
    have h1 := isDiag_sum D Finset.univ ht
    rw [← map_sum, F.complete.complete, σ_zero_one D hfin P] at h1
    exact isDiag_coeff D hfin h1 (isDiag_one D)
  have h01 : ∀ x p, t x p = 0 ∨ t x p = 1 := fun x p ↦ by
    have := congrFun (hidem x) p
    simp only [Pi.mul_apply] at this
    rcases mul_eq_zero.1 (show t x p * (t x p - 1) = 0 by rw [mul_sub, this, mul_one, sub_self])
      with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hex : ∀ p, ∃ x, t x p = 1 := fun p ↦ by
    by_contra hno
    push Not at hno
    have := congrFun hsum p
    rw [Finset.sum_apply, Finset.sum_eq_zero fun x _ ↦ (h01 x p).resolve_right (hno x)] at this
    exact zero_ne_one this
  choose g hg using hex
  have huniq : ∀ x p, t x p = 1 → g p = x := fun x p hx ↦ by
    by_contra hne
    have := congrFun (horth _ _ hne) p
    simp only [Pi.mul_apply, hx, hg p, mul_one, Pi.zero_apply] at this
    exact one_ne_zero this
  have hsurj : Function.Surjective g := fun x ↦ by
    have hE := σ_e_ne_zero D hfin P F x
    by_contra hno
    push Not at hno
    apply hE
    refine eq_of_isDiag D (ht x) (show IsDiag D 0 (t x) by
      have : t x = 0 := funext fun p ↦ (h01 x p).resolve_right fun h ↦ hno p (huniq x p h)
      rw [this]; exact isDiag_zero D)
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_surjective_and_card g).2 ⟨hsurj, by rw [hcard, Fintype.card_fin]⟩
  refine ⟨(Equiv.ofBijective g hbij).symm, fun x ↦ eq_of_isDiag D (ht x) ?_⟩
  have htx : t x = Pi.single ((Equiv.ofBijective g hbij).symm x) 1 := by
    funext p
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h]; have := hg ((Equiv.ofBijective g hbij).symm x)
      rwa [show g ((Equiv.ofBijective g hbij).symm x) = x from
        (Equiv.ofBijective g hbij).apply_symm_apply x] at this
    · refine (h01 x p).resolve_right fun h1 ↦ h ?_
      rw [Equiv.eq_symm_apply]; exact huniq x p h1
  rw [htx]; exact isDiag_eP D _

/-! ### Homogeneous elements of a corner of `A₀` -/

section Lines

attribute [local instance] Classical.decEq

variable [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

/-- The length degree of a ray of `A₀`. -/
abbrev dA (r : RayA0 D v₀) : ℕ := (degR D v₀ (wtR D v₀ r)).toNat

theorem basisR_isHom' (r : RayA0 D v₀) :
    (lenA0 D (hfinObj (c := c))).IsHom (dA D v₀ r) (basisR D v₀ hF r) := by
  obtain ⟨⟨x, y, g⟩, hr⟩ := r
  obtain ⟨p, hp⟩ := exists_path_of_nz hr
  rw [dA, degR_wtR_path D v₀ (t := ⟨(x, y, g), hr⟩) hp, Int.toNat_natCast]
  exact basisR_isHom D v₀ hF hr hp

/-- **A nonzero homogeneous element of a corner of `A₀` is a multiple of one ray vector.** -/
theorem eq_smul_basisR {a b : Fin (FpA0 D v₀ hF).m} {d : ℕ} {z : (Alg D.F0)ᵐᵒᵖ}
    (hz : z ∈ (FpA0 D v₀ hF).corner (k := k) a b) (hd : (lenA0 D (hfinObj (c := c))).IsHom d z)
    (hz0 : z ≠ 0) :
    ∃ r, idxA0 D v₀ hF (srcR D v₀ r) = a ∧ idxA0 D v₀ hF (tgtR D v₀ r) = b ∧ dA D v₀ r = d ∧
      ∃ t : k, t ≠ 0 ∧ z = t • basisR D v₀ hF r := by
  classical
  -- coefficients vanish off the degree
  have hdeg : ∀ r, (basisR D v₀ hF).repr z r ≠ 0 → dA D v₀ r = d := fun r hr ↦ by
    by_contra h
    exact hr (LenGrading.repr_eq_zero_of_isHom (lenA0 D (hfinObj (c := c))) (basisR D v₀ hF) (dA D v₀)
      (basisR_isHom' D v₀ hF) hd h)
  -- coefficients vanish off the corner
  have hcor : ∀ r, (basisR D v₀ hF).repr z r ≠ 0 → (basisR D v₀ hF) r ∈ (FpA0 D v₀ hF).corner (k := k) a b := fun r hr ↦ by
    by_contra h
    apply hr
    have e : z = (FpA0 D v₀ hF).e a * z * (FpA0 D v₀ hF).e b := ((PrimitiveIdempotents.mem_corner_iff' (FpA0 D v₀ hF)).1 hz).symm
    have hz' : z = ∑ s, (basisR D v₀ hF).repr z s • ((FpA0 D v₀ hF).e a * (basisR D v₀ hF) s * (FpA0 D v₀ hF).e b) := by
      conv_lhs => rw [e, ← (basisR D v₀ hF).sum_repr z]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [mul_smul_comm, smul_mul_assoc]
    have hs : ∀ s, (FpA0 D v₀ hF).e a * (basisR D v₀ hF) s * (FpA0 D v₀ hF).e b = if (basisR D v₀ hF) s ∈ (FpA0 D v₀ hF).corner (k := k) a b then (basisR D v₀ hF) s else 0 :=
      fun s ↦ (FpA0 D v₀ hF).proj_corner_of_mem (basisR_mem_corner D v₀ hF s)
    simp only [hs, smul_ite, smul_zero] at hz'
    have := congrArg (fun w ↦ (basisR D v₀ hF).repr w r) hz'
    simp only [map_sum, map_smul] at this
    rw [this, Finset.sum_apply']
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    split_ifs with hs'
    · rw [map_smul, (basisR D v₀ hF).repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
      rintro rfl; exact h hs'
    · simp
  have hend : ∀ r, (basisR D v₀ hF).repr z r ≠ 0 → idxA0 D v₀ hF (srcR D v₀ r) = a ∧
      idxA0 D v₀ hF (tgtR D v₀ r) = b := fun r hr ↦
    (FpA0 D v₀ hF).corner_unique (basisR_mem_corner D v₀ hF r) (hcor r hr) ((basisR D v₀ hF).ne_zero r)
  -- a nonzero coefficient
  obtain ⟨r, hr⟩ : ∃ r, (basisR D v₀ hF).repr z r ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 ((basisR D v₀ hF).repr.injective (by ext s; simp [h s]))
  obtain ⟨h1, h2⟩ := hend r hr
  refine ⟨r, h1, h2, hdeg r hr, (basisR D v₀ hF).repr z r, hr, ?_⟩
  conv_lhs => rw [← (basisR D v₀ hF).sum_repr z]
  refine Finset.sum_eq_single r (fun s _ hs ↦ ?_) (by simp)
  by_contra hs0
  have hs0' : (basisR D v₀ hF).repr z s ≠ 0 := fun h ↦ hs0 (by rw [h, zero_smul])
  obtain ⟨h1', h2'⟩ := hend s hs0'
  apply hs
  refine sepR_deg D v₀ hF s r ((idxA0 D v₀ hF).injective (h1'.trans h1.symm))
    ((idxA0 D v₀ hF).injective (h2'.trans h2.symm)) ?_
  have e1 := hdeg s hs0'
  have e2 := hdeg r hr
  have n1 := degR_nonneg D v₀ hF s
  have n2 := degR_nonneg D v₀ hF r
  simp only [dA] at e1 e2
  omega

end Lines

/-! ### Counting nonzero products -/

section Counting

attribute [local instance] Classical.decEq

variable [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  (Pf : PosFiltration (lenA0 D (hfinObj (c := c))) B) (hP : Pf.RadOne)
  (hA : IsRepresentationFinite k B) {ι : D.PV ≃ Fin F.m} {β : RayA0 D v₀ → B}
  (hβ : F.IsRayPres (k := k) (A0Mult D v₀ hF) ι β)

theorem eP_eq_unitM (p : D.PV) : eP D p = MulOpposite.op (unitM p p (𝟙 (D.F0 p))) := by
  show MulOpposite.op (idem (F := D.F0) p) = _
  congr 1
  apply CatAlg.ext; intro p' q'
  simp [unitM_apply, idem, colAlg, unit]

/-- The degree of a ray vector of the presentation. -/
def degβ (r : RayA0 D v₀) : ℕ := (Pf.exists_degree (hβ.ne r)).choose

theorem degβ_spec (r : RayA0 D v₀) :
    β r ∈ Pf.F (degβ D F v₀ hF Pf hβ r) ∧ β r ∉ Pf.F (degβ D F v₀ hF Pf hβ r + 1) :=
  (Pf.exists_degree (hβ.ne r)).choose_spec

include hβ in
theorem card_PV : Fintype.card D.PV = F.m := by rw [Fintype.card_congr ι, Fintype.card_fin]

/-- The vertex matching of the initial forms. -/
def πV : Fin F.m ≃ D.PV :=
  (exists_vertexMatch D (hfinObj (c := c)) Pf F (card_PV D F v₀ hF hβ)).choose

theorem σ_e_eq (x : Fin F.m) :
    Pf.σ 0 (F.e x) = (FpA0 D v₀ hF).e (idxA0 D v₀ hF (πV D F v₀ hF Pf hβ x)) := by
  rw [(exists_vertexMatch D (hfinObj (c := c)) Pf F (card_PV D F v₀ hF hβ)).choose_spec x,
    FpA0_e, eP_eq_unitM]
  rfl

theorem exists_thetaR (r : RayA0 D v₀) : ∃ r' : RayA0 D v₀,
    idxA0 D v₀ hF (srcR D v₀ r') = idxA0 D v₀ hF (πV D F v₀ hF Pf hβ (ι (srcR D v₀ r))) ∧
    idxA0 D v₀ hF (tgtR D v₀ r') = idxA0 D v₀ hF (πV D F v₀ hF Pf hβ (ι (tgtR D v₀ r))) ∧
    dA D v₀ r' = degβ D F v₀ hF Pf hβ r ∧
    ∃ t : k, t ≠ 0 ∧ Pf.σ (degβ D F v₀ hF Pf hβ r) (β r) = t • basisR D v₀ hF r' := by
  obtain ⟨h1, h2⟩ := degβ_spec D F v₀ hF Pf hβ r
  have hz := Pf.σ_corner_mem F (hβ.corner r) h1
  refine eq_smul_basisR D v₀ hF ?_ (Pf.σ_hom _ _) (fun h ↦ h2 ((Pf.σ_ker _ _ h1).1 h))
  rw [PrimitiveIdempotents.mem_corner_iff', ← σ_e_eq, ← σ_e_eq]
  exact hz.1

/-- **The initial-form map on the rays of `P`.** -/
def thetaR (r : RayA0 D v₀) : RayA0 D v₀ := (exists_thetaR D F v₀ hF Pf hβ r).choose

theorem thetaR_spec (r : RayA0 D v₀) :
    srcR D v₀ (thetaR D F v₀ hF Pf hβ r) = πV D F v₀ hF Pf hβ (ι (srcR D v₀ r)) ∧
    tgtR D v₀ (thetaR D F v₀ hF Pf hβ r) = πV D F v₀ hF Pf hβ (ι (tgtR D v₀ r)) ∧
    ∃ t : k, t ≠ 0 ∧ Pf.σ (degβ D F v₀ hF Pf hβ r) (β r) =
      t • basisR D v₀ hF (thetaR D F v₀ hF Pf hβ r) := by
  obtain ⟨h1, h2, -, h4⟩ := (exists_thetaR D F v₀ hF Pf hβ r).choose_spec
  exact ⟨(idxA0 D v₀ hF).injective h1, (idxA0 D v₀ hF).injective h2, h4⟩

theorem thetaR_dA (r : RayA0 D v₀) :
    dA D v₀ (thetaR D F v₀ hF Pf hβ r) = degβ D F v₀ hF Pf hβ r :=
  (exists_thetaR D F v₀ hF Pf hβ r).choose_spec.2.2.1

include hP hA in
theorem thetaR_injective : Function.Injective (thetaR D F v₀ hF Pf hβ) := by
  intro r s h
  obtain ⟨hr1, hr2, -⟩ := thetaR_spec D F v₀ hF Pf hβ r
  obtain ⟨hs1, hs2, -⟩ := thetaR_spec D F v₀ hF Pf hβ s
  rw [h] at hr1 hr2
  have e1 : srcR D v₀ r = srcR D v₀ s := ι.injective ((πV D F v₀ hF Pf hβ).injective (hr1.symm.trans hs1))
  have e2 : tgtR D v₀ r = tgtR D v₀ s := ι.injective ((πV D F v₀ hF Pf hβ).injective (hr2.symm.trans hs2))
  have ed : degβ D F v₀ hF Pf hβ r = degβ D F v₀ hF Pf hβ s := by
    rw [← thetaR_dA, ← thetaR_dA, h]
  obtain ⟨a1, a2⟩ := degβ_spec D F v₀ hF Pf hβ r
  obtain ⟨b1, b2⟩ := degβ_spec D F v₀ hF Pf hβ s
  rw [ed] at a1 a2
  have hcs := hβ.corner s
  have hcr := hβ.corner r
  change β r ∈ F.corner (k := k) (ι (srcR D v₀ r)) (ι (tgtR D v₀ r)) at hcr
  change β s ∈ F.corner (k := k) (ι (srcR D v₀ s)) (ι (tgtR D v₀ s)) at hcs
  rw [e1, e2] at hcr
  have hray := Pf.ray_eq_of_degree F hP hA hcr hcs a1 a2 b1 b2
  refine hβ.inj r s ?_
  change β r ∈ F.ray (k := k) (ι (srcR D v₀ s)) (ι (tgtR D v₀ s)) (β s)
  rw [← hray]; exact F.mem_ray_self hcr

include hP in
/-- **A nonzero product of `P` at the initial forms is a nonzero product of the presentation.** -/
theorem mul_some_of_thetaR {r s t : RayA0 D v₀}
    (h : (A0Mult D v₀ hF).mul (thetaR D F v₀ hF Pf hβ r) (thetaR D F v₀ hF Pf hβ s) = some t) :
    ((A0Mult D v₀ hF).mul r s).isSome := by
  obtain ⟨hr1, hr2, cr, hcr, hσr⟩ := thetaR_spec D F v₀ hF Pf hβ r
  obtain ⟨hs1, hs2, cs, hcs, hσs⟩ := thetaR_spec D F v₀ hF Pf hβ s
  have hmid := (A0Mult D v₀ hF).mul_mid _ _ _ h
  change tgtR D v₀ _ = srcR D v₀ _ at hmid
  rw [hr2, hs1] at hmid
  have hts : tgtR D v₀ r = srcR D v₀ s := ι.injective ((πV D F v₀ hF Pf hβ).injective hmid)
  have hb : basisR D v₀ hF (thetaR D F v₀ hF Pf hβ r) * basisR D v₀ hF (thetaR D F v₀ hF Pf hβ s) =
      basisR D v₀ hF t := (RaySys.OfBasis.mulB_eq_some _).1 h
  have hσ : Pf.σ (degβ D F v₀ hF Pf hβ r) (β r) * Pf.σ (degβ D F v₀ hF Pf hβ s) (β s) ≠ 0 := by
    rw [hσr, hσs, smul_mul_smul_comm, hb]
    exact smul_ne_zero (mul_ne_zero hcr hcs) ((basisR D v₀ hF).ne_zero t)
  obtain ⟨hM, -⟩ := Pf.mul_not_mem_of_σ F hP (x := ι (srcR D v₀ r)) (y := ι (tgtR D v₀ r))
    (z := ι (tgtR D v₀ s)) (degβ_spec D F v₀ hF Pf hβ r).1 (degβ_spec D F v₀ hF Pf hβ s).1 hσ
  cases hm : (A0Mult D v₀ hF).mul r s with
  | some _ => rfl
  | none => exact absurd (hβ.mul_none r s hm hts) hM

include hP hA in
/-- **Every nonzero product of the presentation has nonzero initial forms** (counting). -/
theorem σ_mul_ne_zero_of_mul {r s : RayA0 D v₀} (h : ((A0Mult D v₀ hF).mul r s).isSome) :
    Pf.σ (degβ D F v₀ hF Pf hβ r) (β r) * Pf.σ (degβ D F v₀ hF Pf hβ s) (β s) ≠ 0 := by
  classical
  set θ := thetaR D F v₀ hF Pf hβ
  have hθ : Function.Bijective θ :=
    Finite.injective_iff_bijective.1 (thetaR_injective D F v₀ hF Pf hP hA hβ)
  set N := (Finset.univ : Finset (RayA0 D v₀ × RayA0 D v₀)).filter
    fun q ↦ ((A0Mult D v₀ hF).mul q.1 q.2).isSome
  set Nθ := (Finset.univ : Finset (RayA0 D v₀ × RayA0 D v₀)).filter
    fun q ↦ ((A0Mult D v₀ hF).mul (θ q.1) (θ q.2)).isSome
  have hsub : Nθ ⊆ N := fun q hq ↦ by
    simp only [Nθ, N, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hq
    exact mul_some_of_thetaR D F v₀ hF Pf hP hβ ht
  have hcard : N.card ≤ Nθ.card := by
    refine Finset.card_le_card_of_injOn (fun q ↦ ((Equiv.ofBijective θ hθ).symm q.1,
      (Equiv.ofBijective θ hθ).symm q.2)) (fun q hq ↦ ?_) (fun q _ q' _ hqq ↦ ?_)
    · simp only [Nθ, N, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hq ⊢
      have e1 : θ ((Equiv.ofBijective θ hθ).symm q.1) = q.1 :=
        (Equiv.ofBijective θ hθ).apply_symm_apply q.1
      have e2 : θ ((Equiv.ofBijective θ hθ).symm q.2) = q.2 :=
        (Equiv.ofBijective θ hθ).apply_symm_apply q.2
      rw [e1, e2]; exact hq
    · simp only [Prod.mk.injEq] at hqq
      exact Prod.ext ((Equiv.ofBijective θ hθ).symm.injective hqq.1)
        ((Equiv.ofBijective θ hθ).symm.injective hqq.2)
  have heq : Nθ = N := Finset.eq_of_subset_of_card_le hsub hcard
  have hrs : (r, s) ∈ Nθ := by
    rw [heq]; simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  simp only [Nθ, Finset.mem_filter, Finset.mem_univ, true_and] at hrs
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hrs
  obtain ⟨-, -, cr, hcr, hσr⟩ := thetaR_spec D F v₀ hF Pf hβ r
  obtain ⟨-, -, cs, hcs, hσs⟩ := thetaR_spec D F v₀ hF Pf hβ s
  rw [hσr, hσs, smul_mul_smul_comm, (RaySys.OfBasis.mulB_eq_some _).1 ht]
  exact smul_ne_zero (mul_ne_zero hcr hcs) ((basisR D v₀ hF).ne_zero t)

include hP hA hβ in
/-- **Initial forms identify ray products** (Proposition 8.3(2)): for nonzero `f ∈ A(x,y)`,
`g ∈ A(y,z)` of degrees `d`, `e`, the ray product `[f][g]` is nonzero iff
`σ_d f · σ_e g ≠ 0`, and then `fg` has degree `d + e` with initial form `σ_d f · σ_e g`. -/
theorem initialForm_products {x y z : Fin F.m} {f g : B} {d e : ℕ}
    (hf : f ∈ F.corner (k := k) x y) (hg : g ∈ F.corner (k := k) y z)
    (hfd : f ∈ Pf.F d) (hfd' : f ∉ Pf.F (d + 1)) (hge : g ∈ Pf.F e) (hge' : g ∉ Pf.F (e + 1)) :
    (f * g ∉ F.insertionSpan (k := k) x y z f g ↔ Pf.σ d f * Pf.σ e g ≠ 0) ∧
      (Pf.σ d f * Pf.σ e g ≠ 0 → f * g ∈ Pf.F (d + e) ∧ f * g ∉ Pf.F (d + e + 1) ∧
        Pf.σ (d + e) (f * g) = Pf.σ d f * Pf.σ e g) := by
  refine ⟨⟨fun hM ↦ ?_, fun hσ ↦ (Pf.mul_not_mem_of_σ F hP hfd hge hσ).1⟩,
    fun hσ ↦ (Pf.mul_not_mem_of_σ F hP (x := x) (y := y) (z := z) hfd hge hσ).2⟩
  have hf0 : f ≠ 0 := fun h ↦ hfd' (h ▸ Submodule.zero_mem _)
  have hg0 : g ≠ 0 := fun h ↦ hge' (h ▸ Submodule.zero_mem _)
  obtain ⟨r, hrx, hry, hfr⟩ := hβ.surj x y f hf hf0
  obtain ⟨s, hsy, hsz, hgs⟩ := hβ.surj y z g hg hg0
  have hts : tgtR D v₀ r = srcR D v₀ s := ι.injective (hry.trans hsy.symm)
  -- `β r` lies in the ray of `f`, `β s` in the ray of `g`
  have hcr : β r ∈ F.corner (k := k) x y := by
    have := hβ.corner r; rwa [hrx, hry] at this
  have hcs : β s ∈ F.corner (k := k) y z := by
    have := hβ.corner s; rwa [hsy, hsz] at this
  have hrf : β r ∈ F.ray (k := k) x y f := by
    rw [F.ray_eq_of_mem hcr hfr]; exact F.mem_ray_self hcr
  have hsg : β s ∈ F.ray (k := k) y z g := by
    rw [F.ray_eq_of_mem hcs hgs]; exact F.mem_ray_self hcs
  obtain ⟨hr1, cr, hcr0, hσr⟩ := Pf.σ_of_mem_ray F hP hf hrf hfd
  obtain ⟨hs1, cs, hcs0, hσs⟩ := Pf.σ_of_mem_ray F hP hg hsg hge
  -- the degrees of `β r`, `β s` are `d`, `e`
  have hdeg : ∀ {a : B} {n n' : ℕ}, a ∈ Pf.F n → a ∉ Pf.F (n + 1) → a ∈ Pf.F n' →
      a ∉ Pf.F (n' + 1) → n = n' := fun h1 h2 h3 h4 ↦ by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact h2 (Pf.F_anti (by omega) h3)
    · exact h4 (Pf.F_anti (by omega) h1)
  have hr2 : β r ∉ Pf.F (d + 1) := fun h ↦ by
    have := (Pf.σ_ker d _ hr1).2 h
    rw [hσr, smul_eq_zero] at this
    exact this.elim hcr0 fun h' ↦ hfd' ((Pf.σ_ker d f hfd).1 h')
  have hs2 : β s ∉ Pf.F (e + 1) := fun h ↦ by
    have := (Pf.σ_ker e _ hs1).2 h
    rw [hσs, smul_eq_zero] at this
    exact this.elim hcs0 fun h' ↦ hge' ((Pf.σ_ker e g hge).1 h')
  have edr : degβ D F v₀ hF Pf hβ r = d :=
    hdeg (degβ_spec D F v₀ hF Pf hβ r).1 (degβ_spec D F v₀ hF Pf hβ r).2 hr1 hr2
  have eds : degβ D F v₀ hF Pf hβ s = e :=
    hdeg (degβ_spec D F v₀ hF Pf hβ s).1 (degβ_spec D F v₀ hF Pf hβ s).2 hs1 hs2
  -- the product of the presentation is nonzero
  have hM' : β r * β s ∉ F.insertionSpan (k := k) x y z (β r) (β s) := fun h ↦
    hM (((F.rayProduct_independent_of hA hf hf0 hg hg0 hrf hsg).1).2 h)
  have hsome : ((A0Mult D v₀ hF).mul r s).isSome := by
    cases hm : (A0Mult D v₀ hF).mul r s with
    | some _ => rfl
    | none =>
        refine absurd ?_ hM'
        have := hβ.mul_none r s hm hts
        rwa [hrx, hry, hsz] at this
  have key := σ_mul_ne_zero_of_mul D F v₀ hF Pf hP hA hβ hsome
  rw [edr, eds, hσr, hσs, smul_mul_smul_comm] at key
  exact fun h ↦ key (by rw [h, smul_zero])

end Counting

end MeshWalk

/-! ### Theorem 11.8(1): initial forms identify `ray A` with `ray A₀` -/

set_option maxHeartbeats 2000000 in
/-- **Initial forms identify `ray A` with `ray A₀`** (Proposition 8.3(2), Theorem 11.8(1)): the
rays of `A` are presented by the ray table of `A₀` (`rayA_eq_rayA0`), and for the categorical
filtration `J` (`posFiltA`, for any complete set `e` of primitive idempotents) a ray product
`[f][g]` is nonzero iff the product of the initial forms is nonzero, in which case `fg` has the
sum of the degrees and initial form `σ_d f · σ_e g`. With Lemma 3.7 (`rayDegree_J`: the
initial-form bijection), this is the identification of the products. -/
theorem rayA_initialForms (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [Ring A]
    [Algebra k A] [FiniteDimensional k A] (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (hn : Nontrivial A) :
    letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
    ∀ S : IndSkeleton k A, ∃ (b : S.ArrowBases) (v₀ : S.ARVertex)
      (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
      (F : PrimitiveIdempotents A) (ι : (S.arMeshData b).PV ≃ Fin F.m)
      (β : S.rayA0AR b v₀ → A), F.IsRayPres (k := k) (S.A0MultAR b v₀ hF) ι β ∧
      ∀ {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
        (hprim : ∀ i, IsPrimitiveIdempotent (e i))
        (hbas : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
          y * x = e j) → i = j),
        ∀ {x y z : Fin F.m} {f g : A} {d d' : ℕ}, f ∈ F.corner (k := k) x y →
          g ∈ F.corner (k := k) y z →
          f ∈ (S.posFiltA b he hprim hbas).F d → f ∉ (S.posFiltA b he hprim hbas).F (d + 1) →
          g ∈ (S.posFiltA b he hprim hbas).F d' → g ∉ (S.posFiltA b he hprim hbas).F (d' + 1) →
          ((f * g ∉ F.insertionSpan (k := k) x y z f g ↔
              (S.posFiltA b he hprim hbas).σ d f * (S.posFiltA b he hprim hbas).σ d' g ≠ 0) ∧
            ((S.posFiltA b he hprim hbas).σ d f * (S.posFiltA b he hprim hbas).σ d' g ≠ 0 →
              f * g ∈ (S.posFiltA b he hprim hbas).F (d + d') ∧
              f * g ∉ (S.posFiltA b he hprim hbas).F (d + d' + 1) ∧
              (S.posFiltA b he hprim hbas).σ (d + d') (f * g) =
                (S.posFiltA b he hprim hbas).σ d f * (S.posFiltA b he hprim hbas).σ d' g)) := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  intro S
  obtain ⟨b, v₀, hF, F, ι, β, hβ⟩ := rayA_eq_rayA0 k A hbasic hA hn S
  refine ⟨b, v₀, hF, F, ι, β, hβ, fun he hprim hbas x y z f g d d' hf hg h1 h2 h3 h4 ↦ ?_⟩
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  exact MeshWalk.initialForm_products (S.arMeshData b) F v₀ hF (S.posFiltA b he hprim hbas)
    (S.posFiltA_radOne b he hprim hbas) hA hβ hf hg h1 h2 h3 h4

end MultiplicativeBasisDeformations
