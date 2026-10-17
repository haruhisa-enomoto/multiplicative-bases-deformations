import MultiplicativeBasisDeformations.Foundations.TransportFamily
import MultiplicativeBasisDeformations.Refinements.FibreAlgebra

/-!
# Proposition 11.3(2): scalar fibres are positive filtered deformations

`binary-families.tex` (`prop:zero-product-family`(2)): "Every scalar fibre is a
positive filtered deformation of `A₀`." A scalar fibre of the family `m + Σ_E T_E μ_E` is the
product `x · y = xy + Σ_E λ_E μ_E(x, y)`, that is `xy + coch_a(x, y)` for a coefficient
function `a` constant on the classes (`EdgeOK`). For `Θ : kP ≅ Λ` carrying each ray to a
homogeneous element of degree `deg ℓ(r)`: the product is associative (Prop 11.3(1),
`family_assoc`) and unital (corrections vanish at identities, `coch_e_left`, `coch_e_right`);
a correction `u q_y v` has degree at least `deg ℓ(u) + deg ℓ(v) + 1` (`deg_eps`), so the
product agrees with that of `Λ` up to terms of higher degree, and the length filtration makes
the fibre a positive filtered deformation (Definition 6.2, `Fib.posFiltration`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ] (G : LenGrading k Λ)
  {ι : Type*} [Fintype ι] (β : Module.Basis ι k Λ) (δ : ι → ℕ) (hβ : ∀ i, G.IsHom (δ i) (β i))

theorem ge_sum' (m : ℕ) {κ : Type*} (s : Finset κ) (f : κ → Λ) (hf : ∀ i ∈ s, G.Ge m (f i)) :
    G.Ge m (∑ i ∈ s, f i) := fun d hd ↦ by
  rw [map_sum]; exact Finset.sum_eq_zero fun i hi ↦ hf i hi d hd

include hβ in
/-- **A bilinear map raising degrees on basis pairs raises degrees.** -/
theorem ge₂_of_basis (μ : Λ →ₗ[k] Λ →ₗ[k] Λ)
    (h : ∀ i j, G.Ge (δ i + δ j + 1) (μ (β i) (β j))) {d e : ℕ} {a b : Λ} (ha : G.IsHom d a)
    (hb : G.IsHom e b) : G.Ge (d + e + 1) (μ a b) := by
  rw [← β.sum_repr a, ← β.sum_repr b, map_sum]
  refine G.ge_sum' _ _ _ fun j _ ↦ ?_
  rw [map_smul, map_sum, LinearMap.sum_apply, Finset.smul_sum]
  refine G.ge_sum' _ _ _ fun i _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hi : δ i = d
  · by_cases hj : δ j = e
    · subst hi hj
      exact G.ge_smul _ (G.ge_smul _ (h i j))
    · rw [G.repr_eq_zero_of_isHom β δ hβ hb hj, zero_smul]; exact fun _ _ ↦ map_zero _
  · rw [G.repr_eq_zero_of_isHom β δ hβ ha hi, zero_smul, smul_zero]; exact fun _ _ ↦ map_zero _

end LenGrading

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  (hfin : IsRepresentationFinite k (S.P.Lin k))

local notation:max "⌜" r "⌝" => Sys.rr S r

include hfin in
/-- **A correction `u q_y v` raises the degree.** -/
theorem deg_eps {u v t : R} (h : S.eps u v = ⌜t⌝) :
    S.P.deg (S.P.wt u) + S.P.deg (S.P.wt v) + 1 ≤ S.P.deg (S.P.wt t) := by
  have hne : S.eps u v ≠ 0 := by rw [h]; exact S.rr_ne t
  obtain ⟨-, -, -, -, he⟩ := S.eps_ne_zero_spec k hfin hne
  rw [he] at h
  rcases S.q_cases (S.P.tgt u) with hq | ⟨g, hg, g1, -, g3⟩
  · rw [hq, mul_zero, zero_mul] at h; exact absurd h.symm (S.rr_ne t)
  rw [hg] at h
  have h1 : ⌜u⌝ * ⌜g⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← h, h0, zero_mul])
  have h2 : ⌜u⌝ * ⌜g⌝ * ⌜v⌝ ≠ 0 := by rw [h]; exact S.rr_ne t
  have hw := congrArg S.wtM h
  rw [S.wtM_mul _ _ h2, S.wtM_mul _ _ h1, wtM_rr, wtM_rr, wtM_rr, wtM_rr] at hw
  have hd : 0 < S.P.deg (S.P.wt g) := S.P.deg_pos g (by rw [g1]; exact g3)
  rw [← hw, map_add, map_add]
  linarith

variable {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)

include hfin in
theorem coch_one_left (c : R → R → k) (z : S.P.Lin k) : S.coch k c 1 z = 0 := by
  rw [← S.P.sum_b_e k, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun x _ ↦ S.coch_e_left k hfin c x z

include hfin in
theorem coch_one_right (c : R → R → k) (z : S.P.Lin k) : S.coch k c z 1 = 0 := by
  rw [← S.P.sum_b_e k, map_sum]
  exact Finset.sum_eq_zero fun x _ ↦ S.coch_e_right k hfin c x z

/-- **The scalar fibre** with coefficients `a` (constant on the classes): the product
`x · y = xy + coch_a(x, y)` transported to `Λ`. -/
def fibreMul {a : R → R → k} (ha : S.EdgeOK k a) : AssocMul k Λ where
  mm := S.transp k Θ (LinearMap.mul k (S.P.Lin k) + S.coch k a)
  assoc x y z := by
    simp only [transp_apply, LinearMap.add_apply, LinearMap.mul_apply',
      AlgEquiv.symm_apply_apply]
    congr 1
    exact S.family_assoc k k hfin ha _ _ _
  one_left x := by
    simp only [transp_apply, LinearMap.add_apply, LinearMap.mul_apply', map_one, one_mul,
      S.coch_one_left k hfin, add_zero, AlgEquiv.apply_symm_apply]
  one_right x := by
    simp only [transp_apply, LinearMap.add_apply, LinearMap.mul_apply', map_one, mul_one,
      S.coch_one_right k hfin, add_zero, AlgEquiv.apply_symm_apply]

theorem fibreMul_apply {a : R → R → k} (ha : S.EdgeOK k a) (x y : S.P.Lin k) :
    (S.fibreMul k hfin Θ ha).mm (Θ x) (Θ y) = Θ (x * y + S.coch k a x y) := by
  simp [fibreMul, transp_apply]

/-- The fibre of the indicator family at `T_{E_i} = λ_i` is the fibre with coefficients
`Σ_i λ_i [E_i]`. -/
theorem fibreMul_family {n : ℕ} (E : Fin n → Quotient S.pairSetoid) (lam : Fin n → k) :
    (S.fibreMul k hfin Θ (S.edgeOK_indComb k E lam)).mm =
      LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam := by
  ext x y
  rw [← Θ.apply_symm_apply x, ← Θ.apply_symm_apply y, fibreMul_apply, S.transp_family k Θ E lam]

variable {G : LenGrading k Λ}
  (hG : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (Θ (S.P.b k r)))

include hG in
/-- The fibre product agrees with that of `Λ` up to terms of higher degree. -/
theorem fibreMul_hdef {a : R → R → k} (ha : S.EdgeOK k a) (d e : ℕ) (x y : Λ)
    (hx : G.IsHom d x) (hy : G.IsHom e y) :
    G.Ge (d + e + 1) ((S.fibreMul k hfin Θ ha).mm x y - x * y) := by
  have key : (S.fibreMul k hfin Θ ha).mm x y - x * y = S.transp k Θ (S.coch k a) x y := by
    simp only [fibreMul, transp_apply, LinearMap.add_apply, LinearMap.mul_apply', map_add,
      map_mul, AlgEquiv.apply_symm_apply, add_sub_cancel_left]
  rw [key]
  refine G.ge₂_of_basis (S.basisΛ k Θ) (fun r ↦ (S.P.deg (S.P.wt r)).toNat)
    (fun r ↦ by rw [basisΛ_apply]; exact hG r) _ (fun u v ↦ ?_) hx hy
  rw [basisΛ_apply, basisΛ_apply, transp_apply, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply, coch_b]
  rcases S.eps_cases u v with h | ⟨t, ht⟩
  · rw [h, vecM_zero, smul_zero, map_zero]; exact fun _ _ ↦ map_zero _
  · rw [ht, vecM_rr, map_smul]
    refine G.ge_smul _ (G.ge_mono ?_ (G.ge_of_isHom (hG t)))
    have := S.deg_eps k hfin ht
    have := S.P.deg_nonneg u
    have := S.P.deg_nonneg v
    omega

include hG in
/-- **Proposition 11.3(2)** (`prop:zero-product-family`(2)): every scalar fibre of the family
`m + Σ_E T_E μ_E` is a positive filtered deformation of `A₀ ≅ Λ` (Definition 6.2), filtered by
degree. -/
def fibrePosFiltration {a : R → R → k} (ha : S.EdgeOK k a) :
    PosFiltration G (Fib (S.fibreMul k hfin Θ ha)) :=
  Fib.posFiltration G (S.fibreMul_hdef k hfin Θ hG ha)

include hfin hG in
/-- **Proposition 11.3(2)**, for the family of indicators of the classes `E_i` at
`T_{E_i} = λ_i`. -/
theorem zeroProductFamily_fibre {n : ℕ} (E : Fin n → Quotient S.pairSetoid) (lam : Fin n → k) :
    ∃ A : AssocMul k Λ, A.mm = LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam ∧
      Nonempty (PosFiltration G (Fib A)) :=
  ⟨_, S.fibreMul_family k hfin Θ E lam,
    ⟨S.fibrePosFiltration k hfin Θ hG (S.edgeOK_indComb k E lam)⟩⟩

end Sys

end RaySys

end MultiplicativeBasisDeformations
