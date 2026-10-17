import MultiplicativeBasisDeformations.Foundations.Exhaustion

/-!
# Lemma 4.11(2): weights on finite subcategories are divisible

`lem:source-basis-extension`(2) (`scalar-normalization.tex:470–518`): "Let
`Scal(T)` denote the group of multiplicative `k*`-valued weights on the nonzero
morphism lines of `T` […]. Restriction gives a split surjection
`Scal(T) → Scal(T')`, whose kernel is a product of copies of `k*`, one for each
connected component of `R`." The splitting: "Give the new line from `s` to the
root weight one, and propagate this value along the walks by multiplying old
weights […]. Lemma 4.9 ensures that the values satisfy every comparison."

We use the consequence needed in Lemma 4.13: over an algebraically closed field,
the weight group of a finite subcategory is divisible (it is an iterated split
extension by products of `k*`). Given `d` and `n`, an `n`-th root on `T'`
extends over the source `s` by Lemma 4.9 (`ratio_of_mult`), and the defect on
the new lines is constant along comparabilities of the support poset (the
kernel), so it has a consistent `n`-th root.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace Thin

variable {k : Type u} [Field k] {O : Type v} [Category.{w} O] [Preadditive O] [Linear k O]

/-- A multiplicative weight on the nonzero lines among a set of objects. -/
structure IsWeight (S : Set O) (d : O → O → k) : Prop where
  ne : ∀ o ∈ S, ∀ o' ∈ S, ∀ f : o ⟶ o', f ≠ 0 → d o o' ≠ 0
  mul : ∀ o ∈ S, ∀ o' ∈ S, ∀ o'' ∈ S, ∀ (f : o ⟶ o') (g : o' ⟶ o''), f ≫ g ≠ 0 →
    d o o'' = d o o' * d o' o''

theorem IsWeight.self {S : Set O} {d : O → O → k} (hd : IsWeight S d) {o : O} (ho : o ∈ S)
    (h1 : 𝟙 o ≠ 0) : d o o = 1 := by
  have h := hd.mul o ho o ho o ho (𝟙 o) (𝟙 o) (by rwa [Category.comp_id])
  have hne := hd.ne o ho o ho (𝟙 o) h1
  have : d o o * (d o o - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hne
  · exact sub_eq_zero.1 h'

theorem IsWeight.mono {S S' : Set O} {d : O → O → k} (hd : IsWeight S d) (h : S' ⊆ S) :
    IsWeight S' d :=
  ⟨fun o ho o' ho' ↦ hd.ne o (h ho) o' (h ho'),
    fun o ho o' ho' o'' ho'' ↦ hd.mul o (h ho) o' (h ho') o'' (h ho'')⟩

section Div

variable [IsAlgClosed k] [Infinite k] (hT : IsThin k O) (hgt : O → ℤ)
  (hR : ∀ o o', Rl o o' → hgt o < hgt o')
  (hsrcRep : ∀ (s : O) (S : Finset O), SupRepFinite hT (s := s) (P := supp s S)
    (fv := fvec s) (fun y hy ↦ fvec_ne s S hy))
  {n : ℕ} (hn : 0 < n)

include hR hsrcRep hn in
/-- **Weights on finite subcategories are divisible** (Lemma 4.11(2)). -/
theorem weight_divisible [DecidableEq O] : ∀ (m : ℕ) (S : Finset O), S.card = m →
    ∀ d : O → O → k, IsWeight (S : Set O) d →
      ∃ e : O → O → k, IsWeight (S : Set O) e ∧
        ∀ o ∈ S, ∀ o' ∈ S, ∀ f : o ⟶ o', f ≠ 0 → d o o' = e o o' ^ n := by
  intro m
  induction m with
  | zero =>
      intro S hS d hd
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨d, hd, fun o ho ↦ absurd ho (Finset.notMem_empty o)⟩
  | succ m ih =>
      intro S hS d hd
      classical
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image S hgt hne
      set S' := S.erase s with hS'def
      have hS'S : (S' : Set O) ⊆ S := fun x hx ↦ Finset.mem_of_mem_erase hx
      have hS's : ∀ o ∈ S', o ≠ s := fun o ho ↦ Finset.ne_of_mem_erase ho
      have hsrc : ∀ o ∈ S', ∀ f : o ⟶ s, f = 0 := by
        intro o ho f
        by_contra hf
        have := hR o s ⟨hS's o ho, f, hf⟩
        have := hmin o (Finset.mem_of_mem_erase ho)
        omega
      obtain ⟨e', he', hde'⟩ := ih S' (by rw [Finset.card_erase_of_mem hs]; omega) d (hd.mono hS'S)
      -- the support poset of `s`
      set P := supp s S' with hPdef
      let fv : ∀ y : O, s ⟶ y := fvec s
      have hfv : ∀ y ∈ P, fv y ≠ 0 := fun y hy ↦ fvec_ne s S' hy
      have hPS : ∀ y ∈ P, y ∈ S' := fun y hy ↦ (Finset.mem_filter.1 hy).1
      letI : PartialOrder (SupP s P fv) := supOrder hT hfv
      letI : LocallyFiniteOrder (SupP s P fv) := Fintype.toLocallyFiniteOrder
      have hid : ∀ y ∈ P, 𝟙 y ≠ 0 := fun y hy h ↦ hfv y hy (by rw [← Category.comp_id (fv y), h,
        Limits.comp_zero])
      have he'1 : ∀ y ∈ P, e' y y = 1 := fun y hy ↦ he'.self (hPS y hy) (hid y hy)
      have hwit : ∀ a b : SupP s P fv, a ≤ b → a ≠ b → ∃ g : a.1 ⟶ b.1, fv a.1 ≫ g ≠ 0 := by
        intro a b hab hne
        rcases hab with h | h
        · exact absurd h hne
        · exact h
      have hμ0 : ∀ a b : SupP s P fv, a ≤ b → e' a.1 b.1 ≠ 0 := by
        intro a b hab
        by_cases h : a = b
        · subst h; rw [he'1 _ a.2]; exact one_ne_zero
        · obtain ⟨g, hg⟩ := hwit a b hab h
          exact he'.ne _ (hPS _ a.2) _ (hPS _ b.2) g (fun h0 ↦ hg (by rw [h0, Limits.comp_zero]))
      have hμmul : ∀ a b c : SupP s P fv, a ≤ b → b ≤ c →
          e' a.1 c.1 = e' a.1 b.1 * e' b.1 c.1 := by
        intro a b c hab hbc
        by_cases h1 : a = b
        · subst h1; rw [he'1 _ a.2, one_mul]
        by_cases h2 : b = c
        · subst h2; rw [he'1 _ b.2, mul_one]
        obtain ⟨g, hg⟩ := hwit a b hab h1
        obtain ⟨g', hg'⟩ := hwit b c hbc h2
        refine he'.mul _ (hPS _ a.2) _ (hPS _ b.2) _ (hPS _ c.2) g g' fun h0 ↦ ?_
        obtain ⟨c₁, hc₁⟩ := exists_smul hT (hfv _ b.2) (fv a.1 ≫ g)
        have hc0 : c₁ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₁; exact hg hc₁
        apply hg'
        have : fv a.1 ≫ g ≫ g' = c₁ • (fv b.1 ≫ g') := by
          rw [← Category.assoc, hc₁, Linear.smul_comp]
        rw [h0, Limits.comp_zero] at this
        exact (smul_eq_zero.1 this.symm).resolve_left hc0
      obtain ⟨Z, hZ0, hZ⟩ := ratio_of_mult (hsrcRep s S')
        (fun a b : SupP s P fv ↦ e' a.1 b.1) hμ0 hμmul
      let av : O → k := fun y ↦ if h : y ∈ P then (Z (show SupP s P fv from ⟨y, h⟩))⁻¹ else 1
      have hav0 : ∀ y, av y ≠ 0 := fun y ↦ by
        simp only [av]; split_ifs
        · exact inv_ne_zero (hZ0 _)
        · exact one_ne_zero
      have havmul : ∀ a b : SupP s P fv, a ≤ b → av b.1 = av a.1 * e' a.1 b.1 := by
        intro a b hab
        simp only [av, dif_pos a.2, dif_pos b.2]
        change (Z b)⁻¹ = (Z a)⁻¹ * e' a.1 b.1
        rw [show e' a.1 b.1 = Z a / Z b from hZ a b hab]
        have := hZ0 a; have := hZ0 b
        field_simp
      -- roots
      let root : k → k := fun x ↦ Classical.choose (IsAlgClosed.exists_pow_nat_eq x hn)
      have hroot : ∀ x, root x ^ n = x := fun x ↦ Classical.choose_spec
        (IsAlgClosed.exists_pow_nat_eq x hn)
      let κ : O → k := fun y ↦ d s y / av y ^ n
      let e : O → O → k := fun o o' ↦
        if o = s then (if o' = s then 1 else av o' * root (κ o'))
        else (if o' = s then 1 else e' o o')
      -- comparabilities from `s`
      have hcomp : ∀ o' ∈ S', ∀ o'' ∈ S', ∀ (f : s ⟶ o') (g : o' ⟶ o''), f ≫ g ≠ 0 →
          ∃ (h' : o' ∈ P) (h'' : o'' ∈ P),
            (show SupP s P fv from ⟨o', h'⟩) ≤ (show SupP s P fv from ⟨o'', h''⟩) := by
        intro o' ho' o'' ho'' f g hfg
        have hf : f ≠ 0 := fun h0 ↦ hfg (by rw [h0, Limits.zero_comp])
        have h' : o' ∈ P := Finset.mem_filter.2 ⟨ho', f, hf⟩
        have h'' : o'' ∈ P := Finset.mem_filter.2 ⟨ho'', f ≫ g, hfg⟩
        refine ⟨h', h'', Or.inr ⟨g, fun h0 ↦ hfg ?_⟩⟩
        obtain ⟨c, hc⟩ := exists_smul hT (hfv o' h') f
        change fv o' ≫ g = 0 at h0
        rw [hc, Linear.smul_comp, h0, smul_zero]
      have hmemS' : ∀ o ∈ S, o ≠ s → o ∈ S' := fun o ho h ↦ Finset.mem_erase.2 ⟨h, ho⟩
      have hκ : ∀ o' ∈ S', ∀ o'' ∈ S', ∀ (f : s ⟶ o') (g : o' ⟶ o''), f ≫ g ≠ 0 →
          κ o'' = κ o' ∧ av o'' = av o' * e' o' o'' := by
        intro o' ho' o'' ho'' f g hfg
        obtain ⟨h', h'', hle⟩ := hcomp o' ho' o'' ho'' f g hfg
        have hav := havmul _ _ hle
        have hg : g ≠ 0 := fun h0 ↦ hfg (by rw [h0, Limits.comp_zero])
        have hd1 := hd.mul s hs o' (hS'S ho') o'' (hS'S ho'') f g hfg
        have hd2 := hde' o' ho' o'' ho'' g hg
        have he0 := he'.ne o' ho' o'' ho'' g hg
        refine ⟨?_, hav⟩
        simp only [κ]
        change d s o'' / av o'' ^ n = d s o' / av o' ^ n
        change av o'' = av o' * e' o' o'' at hav
        rw [hd1, hd2, hav, mul_pow]
        have := hav0 o'
        field_simp
      refine ⟨e, ⟨?_, ?_⟩, ?_⟩
      · intro o ho o' ho' f hf
        by_cases hos : o = s
        · by_cases ho's : o' = s
          · simp only [e, hos, ho's, if_true]; exact one_ne_zero
          · simp only [e, hos, ho's, if_true, if_false]
            refine mul_ne_zero (hav0 _) fun h0 ↦ ?_
            have hr := hroot (κ o')
            rw [h0, zero_pow hn.ne'] at hr
            have hfs : (hos ▸ f : s ⟶ o') ≠ 0 := by subst hos; exact hf
            have hd0 := hd.ne s hs o' ho' _ hfs
            simp only [κ] at hr
            exact hd0 ((div_eq_zero_iff.1 hr.symm).resolve_right (pow_ne_zero _ (hav0 _)))
        · by_cases ho's : o' = s
          · exfalso
            subst ho's
            exact hf (hsrc o (hmemS' o ho hos) f)
          · simp only [e, hos, ho's, if_false]
            exact he'.ne o (hmemS' o ho hos) o' (hmemS' o' ho' ho's) f hf
      · intro o ho o' ho' o'' ho'' f g hfg
        by_cases hos : o = s
        · subst hos
          by_cases ho's : o' = o
          · subst ho's; simp only [e, if_true, one_mul]
          · by_cases ho''s : o'' = o
            · exfalso; subst ho''s
              exact hfg (by rw [hsrc o' (hmemS' o' ho' ho's) g, Limits.comp_zero])
            · simp only [e, ho's, ho''s, if_true, if_false]
              obtain ⟨hk, hav⟩ := hκ o' (hmemS' o' ho' ho's) o'' (hmemS' o'' ho'' ho''s) f g hfg
              rw [hk, hav]; ring
        · by_cases ho's : o' = s
          · exfalso; subst ho's
            exact hfg (by rw [hsrc o (hmemS' o ho hos) f, Limits.zero_comp])
          · by_cases ho''s : o'' = s
            · exfalso; subst ho''s
              exact hfg (hsrc o (hmemS' o ho hos) _)
            · simp only [e, hos, ho's, ho''s, if_false]
              exact he'.mul o (hmemS' o ho hos) o' (hmemS' o' ho' ho's) o'' (hmemS' o'' ho'' ho''s)
                f g hfg
      · intro o ho o' ho' f hf
        by_cases hos : o = s
        · subst hos
          by_cases ho's : o' = o
          · subst ho's
            simp only [e, if_true, one_pow]
            exact hd.self ho (fun h0 ↦ hf (by rw [← Category.comp_id f, h0, Limits.comp_zero]))
          · simp only [e, ho's, if_true, if_false, mul_pow, hroot]
            simp only [κ]
            have := hav0 o'
            field_simp
        · by_cases ho's : o' = s
          · exfalso; subst ho's; exact hf (hsrc o (hmemS' o ho hos) f)
          · simp only [e, hos, ho's, if_false]
            exact hde' o (hmemS' o ho hos) o' (hmemS' o' ho' ho's) f hf

end Div

end Thin

end MultiplicativeBasisDeformations
