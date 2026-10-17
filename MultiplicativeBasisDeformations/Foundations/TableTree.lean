import MultiplicativeBasisDeformations.Foundations.RayConfigs

/-!
# Tree configurations from arrows

A configuration (`Tab.Conf`) of a finite poset whose cover paths are unique is determined by
rays on the cover arrows, provided every path product is nonzero: `ρ a b` is the product along
the unique path (`Conf.ofArrows`). This is how the paper presents its trees ("every path
survives").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (P : Tab V R L)
  {Q : Type} [PartialOrder Q] [Fintype Q] [DecidableEq Q] [DecidableLE Q] [LocallyFiniteOrder Q]

open PosetRep

section Arrows

variable (v : Q → V) (α : ∀ a b : Q, a ⋖ b → R)

/-- The product of the arrows along a path. -/
def pprod : ∀ {a b : Q}, EPath (· ⋖ ·) a b → M P.toMult
  | a, _, EPath.nil _ => P.rr (P.e (v a))
  | _, _, EPath.cons p h => pprod p * P.rr (α _ _ h)

theorem pprod_nil (a : Q) : P.pprod v α (EPath.nil a) = P.rr (P.e (v a)) := by rw [pprod]

theorem pprod_cons {a b c : Q} (p : EPath (· ⋖ ·) a b) (h : b ⋖ c) :
    P.pprod v α (EPath.cons p h) = P.pprod v α p * P.rr (α _ _ h) := by rw [pprod]

variable {v α} (hsrc : ∀ a b h, P.src (α a b h) = v a) (htgt : ∀ a b h, P.tgt (α a b h) = v b)

include hsrc htgt in
/-- The product along a path is zero or a ray from `v a` to `v b`. -/
theorem pprod_cases : ∀ {a b : Q} (p : EPath (· ⋖ ·) a b),
    P.pprod v α p = 0 ∨ ∃ r, P.pprod v α p = P.rr r ∧ P.src r = v a ∧ P.tgt r = v b
  | a, _, EPath.nil _ => Or.inr ⟨P.e (v a), by rw [pprod_nil], P.src_e _, P.tgt_e _⟩
  | _, _, EPath.cons p h => by
      rw [pprod_cons]
      rcases pprod_cases p with h0 | ⟨r, hr, r1, r2⟩
      · left; rw [h0, zero_mul]
      · rw [hr]
        by_cases hm : P.rr r * P.rr (α _ _ h) = 0
        · exact Or.inl hm
        · obtain ⟨t, -, ht⟩ := P.rr_mul_rr_ne_zero hm
          obtain ⟨t1, t2, -⟩ := P.mul_eq_rr_of ht
          exact Or.inr ⟨t, ht, by rw [t1, r1], by rw [t2, htgt]⟩

include hsrc htgt in
theorem e_mul_pprod : ∀ {a b : Q} (p : EPath (· ⋖ ·) a b),
    P.rr (P.e (v a)) * P.pprod v α p = P.pprod v α p
  | a, _, EPath.nil _ => by
      rw [pprod_nil]; have := P.e_mul_rr (P.e (v a)); rwa [P.src_e] at this
  | _, _, EPath.cons p h => by rw [pprod_cons, ← mul_assoc, e_mul_pprod p]

include hsrc htgt in
theorem pprod_comp {a b : Q} (p : EPath (· ⋖ ·) a b) : ∀ {c : Q} (q : EPath (· ⋖ ·) b c),
    P.pprod v α (p.comp q) = P.pprod v α p * P.pprod v α q
  | _, EPath.nil _ => by
      rw [EPath.comp, pprod_nil]
      rcases P.pprod_cases hsrc htgt p with h0 | ⟨r, hr, -, r2⟩
      · rw [h0, zero_mul]
      · rw [hr, ← r2]; exact (P.rr_mul_e r).symm
  | _, EPath.cons q h => by
      rw [EPath.comp, pprod_cons, pprod_cons, pprod_comp p q, mul_assoc]

variable {g : Q → L} (hwt : ∀ a b h, P.wt (α a b h) = g b - g a)

include hsrc htgt hwt in
theorem pprod_wt : ∀ {a b : Q} (p : EPath (· ⋖ ·) a b) (r : R), P.pprod v α p = P.rr r →
    P.wt r = g b - g a
  | a, _, EPath.nil _, r, h => by
      rw [pprod_nil] at h; rw [← P.rr_injective h, P.wt_e, sub_self]
  | _, _, EPath.cons p h, r, hr => by
      rw [pprod_cons] at hr
      rcases P.pprod_cases hsrc htgt p with h0 | ⟨r', hr', -, -⟩
      · rw [h0, zero_mul] at hr; exact absurd hr.symm (P.rr_ne_zero r)
      · rw [hr'] at hr
        rw [P.wt_of_mul hr, pprod_wt p r' hr', hwt]; abel

variable (hpath : ∀ a b (p : EPath (· ⋖ ·) a b), P.pprod v α p ≠ 0)

include hsrc htgt hpath in
theorem exists_ρ (a b : Q) (h : a ≤ b) :
    ∃ r, P.pprod v α (Classical.choice (nonempty_ePath a b h)) = P.rr r ∧ P.src r = v a ∧
      P.tgt r = v b :=
  (P.pprod_cases hsrc htgt _).resolve_left (hpath _ _ _)

/-- The ray of a comparable pair: the product along its path. -/
def ρA (a b : Q) (h : a ≤ b) : R := (P.exists_ρ hsrc htgt hpath a b h).choose

theorem ρA_spec (a b : Q) (h : a ≤ b) :
    P.pprod v α (Classical.choice (nonempty_ePath a b h)) = P.rr (P.ρA hsrc htgt hpath a b h) ∧
      P.src (P.ρA hsrc htgt hpath a b h) = v a ∧ P.tgt (P.ρA hsrc htgt hpath a b h) = v b :=
  (P.exists_ρ hsrc htgt hpath a b h).choose_spec

variable (huniq : ∀ a b : Q, Subsingleton (EPath (· ⋖ ·) a b))

include huniq in
theorem ρA_path (a b : Q) (p : EPath (· ⋖ ·) a b) :
    P.pprod v α p = P.rr (P.ρA hsrc htgt hpath a b (p.le fun _ _ h ↦ h.lt)) := by
  rw [← (P.ρA_spec hsrc htgt hpath a b (p.le fun _ _ h ↦ h.lt)).1,
    (huniq a b).elim p (Classical.choice (nonempty_ePath a b (p.le fun _ _ h ↦ h.lt)))]

variable
  (retL : ∀ a b c (hab : a ⋖ b) (hac : a ≤ c) (h : R), P.src h = v b → P.tgt h = v c →
    P.wt h = g c - g b → P.mul (P.ρA hsrc htgt hpath a b hab.le) h =
      some (P.ρA hsrc htgt hpath a c hac) → b ≤ c)
  (retR : ∀ a b c (hab : a ⋖ b) (hcb : c ≤ b) (h : R), P.src h = v c → P.tgt h = v a →
    P.wt h = g a - g c → P.mul h (P.ρA hsrc htgt hpath a b hab.le) =
      some (P.ρA hsrc htgt hpath c b hcb) → c ≤ a)

/-- **The configuration of a tree given by its arrows.** -/
def Conf.ofArrows : P.Conf Q where
  v := v
  g := g
  ρ := P.ρA hsrc htgt hpath
  src_ρ a b h := (P.ρA_spec hsrc htgt hpath a b h).2.1
  tgt_ρ a b h := (P.ρA_spec hsrc htgt hpath a b h).2.2
  wt_ρ a b h := P.pprod_wt hsrc htgt hwt _ _ (P.ρA_spec hsrc htgt hpath a b h).1
  mul_ρ a b c h1 h2 := by
    obtain ⟨p⟩ := nonempty_ePath a b h1
    obtain ⟨q⟩ := nonempty_ePath b c h2
    have e := P.pprod_comp hsrc htgt p q
    rw [P.ρA_path hsrc htgt hpath huniq a b p, P.ρA_path hsrc htgt hpath huniq b c q,
      P.ρA_path hsrc htgt hpath huniq a c (p.comp q)] at e
    exact P.rr_mul_rr_eq_rr.1 e.symm
  retL := retL
  retR := retR

end Arrows

/-! ### Configurations of table posets -/

section Table

variable {n : ℕ} {le : Fin n → Fin n → Bool} [Fact (Ax le)]
  (v : Fin n → V) (g : Fin n → L) (ρt : Fin n → Fin n → R)
  (hsrc : ∀ i j, le i j = true → P.src (ρt i j) = v i)
  (htgt : ∀ i j, le i j = true → P.tgt (ρt i j) = v j)
  (hwt : ∀ i j, le i j = true → P.wt (ρt i j) = g j - g i)
  (hmul : ∀ i j l, le i j = true → le j l = true → P.mul (ρt i j) (ρt j l) = some (ρt i l))
  (hretL : ∀ i j l (h : R), covB le i j = true → le i l = true → P.src h = v j → P.tgt h = v l →
    P.wt h = g l - g j → P.mul (ρt i j) h = some (ρt i l) → le j l = true)
  (hretR : ∀ i j l (h : R), covB le i j = true → le l j = true → P.src h = v l → P.tgt h = v i →
    P.wt h = g i - g l → P.mul h (ρt i j) = some (ρt l j) → le l i = true)

/-- **The configuration of a table poset given by a table of rays.** -/
def Conf.ofTable : P.Conf (Pos n le) where
  v a := v a.v
  g a := g a.v
  ρ a b _ := ρt a.v b.v
  src_ρ a b h := hsrc _ _ h
  tgt_ρ a b h := htgt _ _ h
  wt_ρ a b h := hwt _ _ h
  mul_ρ a b c h1 h2 := hmul _ _ _ h1 h2
  retL a b c hab hac h h1 h2 h3 hm :=
    hretL _ _ _ h ((pos_covBy_iff a b).1 hab) hac h1 h2 h3 hm
  retR a b c hab hcb h h1 h2 h3 hm :=
    hretR _ _ _ h ((pos_covBy_iff a b).1 hab) hcb h1 h2 h3 hm

variable (k : Type u) [Field k] [IsAlgClosed k]

include hsrc htgt hwt hmul hretL hretR in
/-- **A forbidden tree configuration contradicts finite representation type.** -/
theorem table_false (hfin : IsRepresentationFinite k (P.Lin k)) (d : Fin n → ℕ)
    (hu : UniqOK le) (hc : CountOK le d) : False :=
  inc_forbidden k (OrderIso.refl _) d hu hc
    ((Conf.ofTable P v g ρt hsrc htgt hwt hmul hretL hretR).isRepresentationFinite k hfin)

omit [Fact (Ax le)] in
include hsrc htgt in
theorem hmul_of_strict (hρe : ∀ i, ρt i i = P.e (v i))
    (hmul' : ∀ i j l, le i j = true → le j l = true → i ≠ j → j ≠ l →
      P.mul (ρt i j) (ρt j l) = some (ρt i l)) :
    ∀ i j l, le i j = true → le j l = true → P.mul (ρt i j) (ρt j l) = some (ρt i l) := by
  intro i j l h1 h2
  by_cases hij : i = j
  · subst hij
    rw [hρe, ← hsrc i l h2]
    exact P.e_mul _
  · by_cases hjl : j = l
    · subst hjl
      rw [hρe, ← htgt i j h1]
      exact P.mul_e _
    · exact hmul' i j l h1 h2 hij hjl

end Table

end Tab

end RaySys

end MultiplicativeBasisDeformations
