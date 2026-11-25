import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import OAI.LinearAlgebra.MatrixExponent.Sphere.Interpolation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Algebra.Basic

section
/-!
# Weighted slot selection

A test can pair only with its target or a strictly heavier slot. If the
available weight cannot exceed the target weight, every test in a
nonzero Wick monomial must occupy its target.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {α β R : Type*} [CommRing R]

theorem contract_skip (f : α → R) (P : List α → R) (s : β → α) (b : List β)
    (l : List α) (h : ∀ p y q, b = p ++ y :: q → f (s y) * P ((p ++ q).map s ++ l) = 0) :
    contract f P (b.map s ++ l) =
      (-1 : R) ^ b.length * contract f (fun xs => P (b.map s ++ xs)) l := by
  induction b generalizing P with
  | nil => simp
  | cons y b ih =>
    have hz := h [] y b rfl
    simp only [List.nil_append] at hz
    have e := ih (fun xs => P (s y :: xs))
      (fun p z q he => h (y :: p) z q (congrArg (y :: ·) he))
    simp only [List.map_cons, List.cons_append, contract_cons, hz, zero_sub, e,
      List.length_cons, pow_succ, mul_neg_one, neg_mul]

variable [DecidableEq β] (k : α → α → R) (t s : β → α) (w : β → ℝ) (valid : β → Prop)
    (hw : ∀ x, valid x → 0 < w x) (ht : ∀ x y, k (t x) (t y) = 0)
    (hp : ∀ x y, valid x → valid y → w y ≤ w x → k (t x) (s y) = if x = y then 1 else 0)

omit [DecidableEq β] in
include ht in
private theorem wick_test (x : β) (a b : List β) :
    wick k ((x :: a).map t ++ b.map s) =
      (-1 : R) ^ a.length * contract (k (t x)) (fun u => wick k (a.map t ++ u)) (b.map s) := by
  rw [List.map_cons, List.cons_append, wick_cons]
  exact contract_skip _ _ t a _ (fun _ _ _ _ => by rw [ht, zero_mul])

include hw ht hp in
private theorem nonzero_perm (a b : List β) (va : ∀ x ∈ a, valid x) (vb : ∀ x ∈ b, valid x)
    (le : (b.map w).sum ≤ (a.map w).sum) (ne : wick k (a.map t ++ b.map s) ≠ 0) :
    a.Perm b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y b =>
      have hy := hw y (vb y (by simp))
      have h : 0 ≤ (b.map w).sum := List.sum_nonneg (by
        simp only [List.forall_mem_map]
        exact fun z hz => (hw z (vb _ (by simp [hz]))).le)
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at le
      linarith
  | cons x a ih =>
    by_contra hn
    apply ne
    rw [wick_test k t s ht]
    have v : ∀ p y q, b = p ++ y :: q →
        k (t x) (s y) * wick k (a.map t ++ (p ++ q).map s) = 0 := by
      intro p y q e
      have perm : b.Perm (y :: (p ++ q)) := by rw [e]; exact List.perm_middle
      have bound : w y + ((p ++ q).map w).sum ≤ w x + (a.map w).sum := by
        rw [(perm.map w).sum_eq] at le
        exact le
      have vx := va x (by simp)
      have vy := vb y (perm.mem_iff.mpr (by simp))
      by_cases h : w y < w x
      · have he : x ≠ y := by rintro rfl; exact h.false
        rw [hp x y vx vy h.le, ite_eq_right he, zero_mul]
      by_cases h' : wick k (a.map t ++ (p ++ q).map s) = 0
      · rw [h', mul_zero]
      have e' : a.Perm (p ++ q) := ih _ (fun z hz => va z (by simp [hz]))
        (fun z hz => vb z (perm.mem_iff.mpr (by simp [hz]))) (by linarith) h'
      have he : x ≠ y := by
        rintro rfl
        exact hn ((e'.cons x).trans perm.symm)
      rw [hp x y vx vy (by linarith [(e'.map w).sum_eq]), ite_eq_right he, zero_mul]
    have h := contract_skip (k (t x)) (fun u => wick k (a.map t ++ u)) s b []
      (by simpa only [List.append_nil] using v)
    simp only [List.append_nil, contract_nil, mul_zero] at h
    rw [h, mul_zero]

include hw ht hp in
private theorem wick_diag (a : List β) (va : ∀ x ∈ a, valid x) (ha : a.Nodup) :
    wick k (a.map t ++ a.reverse.map s) = 1 := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    rw [List.nodup_cons] at ha
    rw [List.forall_mem_cons] at va
    rw [wick_test k t s ht, List.reverse_cons, List.map_append, List.map_singleton]
    have v : ∀ p y q, a.reverse = p ++ y :: q →
        k (t x) (s y) * wick k (a.map t ++ ((p ++ q).map s ++ [s x])) = 0 := by
      intro p y q e
      have perm : a.Perm (y :: (p ++ q)) := by
        apply (List.reverse_perm a).symm.trans
        rw [e]
        exact List.perm_middle
      have hy : y ∈ a := perm.mem_iff.mpr (by simp)
      by_cases h : w y ≤ w x
      · have he : x ≠ y := fun e => ha.1 (e ▸ hy)
        rw [hp x y va.1 (va.2 y hy) h, ite_eq_right he, zero_mul]
      let b := (p ++ q) ++ [x]
      have vb : ∀ z ∈ b, valid z := by
        intro z hz
        rcases List.mem_append.mp hz with h₁ | h₂
        · exact va.2 z (perm.mem_iff.mpr (.tail _ h₁))
        · exact (List.mem_singleton.mp h₂).symm ▸ va.1
      have bound : (b.map w).sum ≤ (a.map w).sum := by
        rw [(perm.map w).sum_eq]
        simp only [b, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
          List.map_nil, List.sum_nil]
        linarith
      have z : wick k (a.map t ++ b.map s) = 0 := by
        by_contra he
        have e' := nonzero_perm k t s w valid hw ht hp a b va.2 vb bound he
        exact ha.1 (e'.mem_iff.mpr (by simp [b]))
      simpa only [b, List.map_append, List.map_singleton, mul_zero] using congrArg (k (t x) (s y) * ·) z
    rw [contract_skip _ _ _ _ _ v, List.length_reverse, contract_cons, contract_nil,
      sub_zero, List.append_nil, hp x x va.1 va.1 le_rfl, ite_eq_left rfl, ih va.2 ha.2]
    simp [← mul_pow]

include hw ht hp in
/-- Under a total weight budget, triangular pairings select precisely
the target slot list. Reversing the tests cancels the pairing signs. -/
theorem wick_pivot (a b : List β) (va : ∀ x ∈ a, valid x) (vb : ∀ x ∈ b, valid x)
    (ha : a.Nodup) (hc : a.Perm b → a = b) (le : (b.map w).sum ≤ (a.map w).sum) :
    wick k (a.reverse.map t ++ b.map s) = if a = b then 1 else 0 := by
  have vr : ∀ x ∈ a.reverse, valid x := by simpa using va
  by_cases he : a = b
  · subst b
    simpa using wick_diag k t s w valid hw ht hp a.reverse vr ((List.reverse_perm a).nodup_iff.mpr ha)
  rw [ite_eq_right he]
  by_contra hn
  have e := nonzero_perm k t s w valid hw ht hp a.reverse b vr vb (by simpa using le) hn
  exact he (hc ((List.reverse_perm a).symm.trans e))

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Wedge duality

Reversing the second list of modes gives the ordinary Kronecker pairing
on the ordered wedge basis.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {α R : Type*} [CommRing R] {r : ℕ} {k : α → α → R}

private theorem contract_last (f : α → R) (P : List α → R) (p : List α) (y : α)
    (h : ∀ z ∈ p, f z = 0) :
    contract f P (p ++ [y]) = (-1 : R) ^ p.length * (f y * P p) := by
  induction p generalizing P with
  | nil => simp [contract_cons]
  | cons x p ih =>
    simp only [List.forall_mem_cons] at h
    rw [List.cons_append, contract_cons, h.1, zero_mul, zero_sub, ih _ h.2,
      List.length_cons, pow_succ, mul_neg_one, neg_mul]

/-- Only the last position can pair with the first. An odd residual
length contributes zero, so no sign survives. -/
theorem wick_last (x y : α) (p : List α) (h : ∀ z ∈ p, k x z = 0) :
    wick k (x :: (p ++ [y])) = k x y * wick k p := by
  rw [wick_cons, contract_last _ _ _ _ h]
  by_cases he : p.length % 2 = 1
  · rw [wick_odd he, mul_zero, mul_zero]
  · have e : Even p.length := ⟨p.length / 2, by omega⟩
    rw [e.neg_one_pow, one_mul]

theorem wick_unpaired (skew : ∀ x y, k y x = -k x y)
    (p s : List α) (x : α) (h : ∀ y ∈ p ++ s, k x y = 0) :
    wick k (p ++ x :: s) = 0 := by
  have e := wick_swap_blocks skew [] p [x] s
  simp only [List.nil_append, List.append_assoc, List.singleton_append] at e
  rw [e, List.cons_append, wick_cons, contract_vanish _ _ _ h, mul_zero]

theorem wick_dual (skew : ∀ x y, k y x = -k x y) (A B : Mode r → α)
    (hA : ∀ x y, k (A x) (A y) = 0) (hB : ∀ x y, k (B x) (B y) = 0)
    (hAB : ∀ x y, k (A x) (B y) = if x = y then 1 else 0)
    (a b : Wedge r) :
    wick k (a.val.map A ++ b.val.reverse.map B) = if a.val = b.val then 1 else 0 := by
  have left (x : Mode r) (a b : List (Mode r)) (hx : x ∉ b) :
      ∀ z ∈ a.map A ++ b.reverse.map B, k (A x) z = 0 := by
    simp only [List.forall_mem_append, List.forall_mem_map, List.mem_reverse]
    refine ⟨fun z _ => hA _ _, fun z hz => ?_⟩
    rw [hAB, ite_eq_right (show x ≠ z from fun e => hx (e ▸ hz))]
  have right (y : Mode r) (a b : List (Mode r)) (hy : y ∉ a) :
      wick k (a.map A ++ (y :: b).reverse.map B) = 0 := by
    rw [List.reverse_cons, List.map_append, List.map_singleton, ← List.append_assoc]
    apply wick_unpaired skew
    simp only [List.append_nil, List.forall_mem_append, List.forall_mem_map, List.mem_reverse]
    refine ⟨fun z hz => ?_, fun z _ => hB _ _⟩
    rw [skew, hAB, ite_eq_right (show z ≠ y from fun e => hy (e ▸ hz)), neg_zero]
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change wick k (a.map A ++ b.reverse.map B) = if a = b then 1 else 0
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp
    | cons y b => rw [right _ _ _ (by simp)]; simp
  | cons x a ih =>
    cases b with
    | nil =>
      rw [List.map_cons, List.cons_append, wick_cons, contract_vanish _ _ _ (left _ _ _ (by simp))]
      simp
    | cons y b =>
      rw [List.pairwise_cons] at ha hb
      rcases lt_trichotomy (toLex x) (toLex y) with h | h | h
      · have hx : x ∉ y :: b := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun e => h.ne (congrArg toLex e), fun e => h.asymm (hb.1 _ e)⟩
        rw [List.map_cons, List.cons_append, wick_cons, contract_vanish _ _ _ (left _ _ _ hx)]
        simp [show x ≠ y from fun e => hx (by simp [e])]
      · have h' := toLex.injective h
        subst y
        have hx : x ∉ b := fun e => (hb.1 _ e).false
        rw [List.map_cons, List.cons_append, List.reverse_cons, List.map_append, ← List.append_assoc,
          List.map_singleton, wick_last _ _ _ (left _ _ _ hx), hAB, ite_eq_left rfl, one_mul, ih ha.2 b hb.2]
        simp
      · have hy : y ∉ x :: a := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun e => h.ne (congrArg toLex e), fun e => h.asymm (ha.1 _ e)⟩
        rw [right _ _ _ hy]
        simp [show x ≠ y from fun e => hy (by simp [e])]

theorem fusion_empty (R : Type*) [CommRing R] {r : ℕ} (a b : Wedge r) :
    fusion R a.val [] b.val = if a.val = b.val then 1 else 0 := by
  simp only [fusion, marks, List.map_nil, List.append_nil]
  apply wick_dual (pairing_skew R)
  · intro x y
    change (if x.1 = y.1 then (0 : R) else 0) = 0
    simp
  · intro x y
    change (if x.1 = y.1 then (0 : R) else 0) = 0
    simp
  · intro x y
    change (if x.1 = y.1 then (if x.2 = y.2 then (1 : R) else 0) else 0) = _
    simp only [Prod.ext_iff, ite_and]

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Auxiliary marks of bounded weight

A probe is an even ordered subset of the auxiliary marks, with just the
lowest mode at each selected mark. Removing all probe-probe contractions
uses only shorter probe lists. Linear combinations then implement arbitrary
covectors. Kronecker covectors detect a longest nonzero word.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset

abbrev Probe (n d : ℕ) :=
  {w : Wedge n // (∀ x ∈ w.val, x.2 = 0) ∧ w.val.length ≤ d ∧ w.val.length % 2 = 0}

variable {F A I : Type*} [Field F] {n d : ℕ}

def mark (a : A → F × ℕ) (i : A) : Site F 1 := ((a i).1, 0, (a i).2)

def probeEval (a : A → F × ℕ) (z : Fin n → F) (w : Probe n d) (xs : List A) : F :=
  wick fieldKernel (w.val.val.map (fun j => (z j.1, 0, j.2)) ++ xs.map (mark a))

private theorem ordered_mem (a : A → F × ℕ) (z : Fin n → F) (xs : I → List A)
    (M : Submodule F (I → F)) (heven : ∀ i, (xs i).length % 2 = 0)
    (hM : ∀ w : Probe n d, (fun i => probeEval a z w (xs i)) ∈ M)
    (p : List (Fin n)) (hp : p.length ≤ d) :
    (fun i => wick fieldKernel (p.map (fun j => (z j, 0, 0)) ++ (xs i).map (mark a))) ∈ M := by
  classical
  by_cases ho : p.length % 2 = 0
  · let q := p.map (fun j => (j, 0))
    let g (j : Mode n) : Site F 1 := (z j.1, 0, j.2)
    obtain ⟨v, hv, h⟩ := normalize F q
    have ok (w : Wedge n) (hw : w ∈ v.support) :
        (fun i => wick fieldKernel (w.val.map g ++ (xs i).map (mark a))) ∈ M := by
      have hperm := hv w hw
      have hl : w.val.length = p.length := by rw [← hperm.length_eq]; simp [q]
      have hz (x) (hx : x ∈ w.val) : x.2 = 0 := by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mpr hx)
        rfl
      exact hM ⟨w, hz, hl.trans_le hp, by rw [hl, ho]⟩
    convert M.sum_mem (fun w hw => M.smul_mem (v w) (ok w hw)) using 1
    funext i
    simpa [q, g, Function.comp_def, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
      using h _ (alternates_map fieldKernel_skew fieldKernel_self g ((xs i).map (mark a)))
  · convert M.zero_mem using 1
    funext i
    apply wick_odd
    simp only [List.length_append, List.length_map]
    have := heven i
    omega

private abbrev Entry (A F : Type*) := (A → F) ⊕ A

private def test (a : A → F × ℕ) : Entry A F → Entry A F → F
  | .inl _, .inl _ => 0
  | .inl f, .inr j => -f j
  | .inr j, .inl f => f j
  | .inr i, .inr j => fieldKernel (mark a i) (mark a j)

private theorem test_skew (a : A → F × ℕ) (x y : Entry A F) :
    test a y x = - test a x y := by
  cases x <;> cases y <;> simp [test]
  exact fieldKernel_skew _ _

private def pole (a : A → F × ℕ) (z : F) (i : A) : F :=
  (z - (a i).1)⁻¹ ^ ((a i).2 + 1)

private theorem pole_eq (a : A → F × ℕ) (z : F) (i : A) :
    fieldKernel (mark a i) (z, 0, 0) = pole a z i := by
  simp [fieldKernel, coeff, mark, pole]

private theorem remove_pairs (a : A → F × ℕ) (z : Fin n → F) (xs : I → List A)
    (M : Submodule F (I → F)) (heven : ∀ i, (xs i).length % 2 = 0)
    (hM : ∀ w : Probe n d, (fun i => probeEval a z w (xs i)) ∈ M)
    (p : List (Fin n)) (hp : p.length ≤ d) :
    (fun i => wick (test a)
      (p.map (fun j => .inl (pole a (z j))) ++ (xs i).map .inr)) ∈ M := by
  let f : Fin n ⊕ A → Site F 1 := Sum.elim (fun j => (z j, 0, 0)) (mark a)
  let g : Fin n ⊕ A → Entry A F := Sum.elim (fun j => .inl (pole a (z j))) .inr
  let k x y := fieldKernel (f x) (f y)
  let l x y := test a (g x) (g y) - k x y
  let X (i : I) : List (Fin n ⊕ A) := (xs i).map .inr
  let Y : List (Fin n ⊕ A) := p.map .inl
  have skip (i : I) (x y : Fin n ⊕ A) (hy : y ∈ X i) : l x y = 0 := by
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hy
    cases x with
    | inl j =>
      change -pole a (z j) s - fieldKernel (z j, 0, 0) (mark a s) = 0
      rw [fieldKernel_skew, pole_eq, sub_self]
    | inr j => exact sub_self _
  have hv := partial_mem M l (fun i q => wick k (q ++ X i)) Y (by
    intro q hq
    obtain ⟨q, hqp, rfl⟩ := List.sublist_map_iff.mp hq
    have hw := ordered_mem a z xs M heven hM q (hqp.length_le.trans hp)
    convert hw using 1
    funext i
    unfold k
    rw [← wick_map fieldKernel f]
    simp [X, f, Function.comp_def])
  convert hv using 1
  funext i
  rw [← wick_add_append l k _ _ (skip i)]
  simp only [l, sub_add_cancel]
  rw [← wick_map (test a) g]
  simp [X, Y, g, Function.comp_def]

private theorem covectors_mem (a : A → F × ℕ) (z : Fin n → F) (xs : I → List A)
    (M : Submodule F (I → F)) (heven : ∀ i, (xs i).length % 2 = 0)
    (hM : ∀ w : Probe n d, (fun i => probeEval a z w (xs i)) ∈ M)
    (q : List (A → F)) (hc : ∀ f ∈ q, f ∈ Submodule.span F (Set.range (fun j => pole a (z j))))
    (p : List (Fin n)) (hp : p.length + q.length ≤ d) :
    (fun i => wick (test a) (p.map (fun j => .inl (pole a (z j))) ++ q.map .inl ++
      (xs i).map .inr)) ∈ M := by
  classical
  induction q generalizing p with
  | nil => simpa using remove_pairs a z xs M heven hM p hp
  | cons f q ih =>
    obtain ⟨hf, hq⟩ := List.forall_mem_cons.mp hc
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hf
    have he (s : Entry A F) :
        test a (.inl f) s = ∑ j, c j * test a (.inl (pole a (z j))) s := by
      cases s with
      | inl _ => simp [test]
      | inr i =>
        simpa [test, Finset.sum_apply] using congrArg Neg.neg (congrFun hc.symm i)
    have hj (j : Fin n) : (p ++ [j]).length + q.length ≤ d := by
      simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
      omega
    convert M.sum_mem (fun j (_ : j ∈ univ) => M.smul_mem (c j) (ih hq _ (hj j))) using 1
    funext i
    simpa [Finset.sum_apply] using wick_linear (test_skew a) he
      (p.map (fun j => .inl (pole a (z j)))) (q.map .inl ++ (xs i).map .inr)

private def delta [DecidableEq A] (i j : A) : F := if i = j then -1 else 0

private def dualRow [DecidableEq A] (i : A) : Entry A F := .inl (delta i)

private theorem detect_self [DecidableEq A] (a : A → F × ℕ) (s : List A) (hs : s.Nodup) :
    wick (test a) (s.map dualRow ++ s.reverse.map .inr) = 1 := by
  induction s with
  | nil => simp
  | cons x s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.cons_append, List.reverse_cons, List.map_append, ← List.append_assoc,
      List.map_singleton, wick_last, ih hs.2, mul_one]
    · simp [test, dualRow, delta]
    · simp only [List.forall_mem_append, List.forall_mem_map, List.mem_reverse]
      refine ⟨fun _ _ => rfl, fun b hb => ?_⟩
      have h : x ≠ b := fun e => hs.1 (e ▸ hb)
      simp [test, dualRow, delta, h]

private theorem detect_other [DecidableEq A] (a : A → F × ℕ) (s t : List A) (h : ¬s ⊆ t) :
    wick (test a) (s.reverse.map dualRow ++ t.map .inr) = 0 := by
  obtain ⟨x, hx, hy⟩ : ∃ x, x ∈ s ∧ x ∉ t := by simpa [List.subset_def, not_forall] using h
  obtain ⟨p, q, he⟩ := List.append_of_mem (List.mem_reverse.mpr hx)
  rw [he, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
  apply wick_unpaired (test_skew a)
  simp only [List.forall_mem_append, List.forall_mem_map]
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun b hb => ?_⟩
  have hn : x ≠ b := fun e => hy (e ▸ hb)
  simp [test, dualRow, delta, hn]

private theorem probe_span [Fintype I]
    (a : A → F × ℕ) (z : Fin n → F) (xs : I → List A)
    (hc : Submodule.span F (Set.range (fun j => pole a (z j))) = ⊤)
    (heven : ∀ i, (xs i).length % 2 = 0) (hw : ∀ i, (xs i).length ≤ d)
    (hn : ∀ i, (xs i).Nodup) (hinj : ∀ i j, (xs i).Perm (xs j) → i = j) :
    Submodule.span F (Set.range (fun (w : Probe n d) i => probeEval a z w (xs i))) = ⊤ := by
  classical
  apply span_of_separates
  intro c h
  by_contra hne
  let s := univ.filter fun i => c i ≠ 0
  have hs : s.Nonempty := by
    contrapose! hne
    funext i
    have : i ∉ s := by rw [hne]; simp
    simpa [s] using this
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => (xs j).length) hs
  let L : (I → F) →ₗ[F] F :=
    { toFun := fun x => ∑ j, c j * x j
      map_add' := by intros; simp [mul_add, sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm] }
  have hM (w : Probe n d) : (fun j => probeEval a z w (xs j)) ∈ L.ker := h w
  have h' := covectors_mem a z xs L.ker heven hM ((xs i).reverse.map delta)
    (by rw [hc]; simp) []
    (by simpa using hw i)
  simp only [List.map_nil, List.nil_append, List.map_map, Function.comp_def] at h'
  change (∑ j, c j * wick (test a) ((xs i).reverse.map dualRow ++ (xs j).map .inr)) = 0 at h'
  have he : wick (test a) ((xs i).reverse.map dualRow ++ (xs i).map .inr) = 1 := by
    simpa using detect_self a (xs i).reverse (List.nodup_reverse.mpr (hn i))
  rw [Fintype.sum_eq_single i, he, mul_one] at h'
  · exact (mem_filter.mp hi).2 h'
  · intro j hj
    by_cases hz : c j = 0
    · simp [hz]
    · have hnsub : ¬ xs i ⊆ xs j := fun sub =>
        hj (hinj i j (((hn i).subperm sub).perm_of_length_le
          (hmax j (mem_filter.mpr ⟨mem_univ _, hz⟩)))).symm
      rw [detect_other a _ _ hnsub, mul_zero]

/-- One mode at each of the prescribed auxiliary positions suffices to
realize every even form on a family of distinct ordered monomials. -/
theorem auxiliary_marks [Fintype A] [Fintype I] (a : A ↪ F × ℕ) (z : Fin n ↪ F) (q : ℕ)
    (ha : ∀ i, (a i).2 < q) (hz : ∀ j i, z j ≠ (a i).1)
    (hcard : (1 + Fintype.card A) * q < n)
    (xs : I → List A) (hw : ∀ i, (xs i).length ≤ d)
    (hn : ∀ i, (xs i).Nodup) (hinj : ∀ i j, (xs i).Perm (xs j) → i = j)
    (v : I → F) (hv : ∀ i, (xs i).length % 2 = 1 → v i = 0) :
    ∃ c : Probe n d →₀ F, ∀ i, ∑ w ∈ c.support, c w * probeEval a z w (xs i) = v i := by
  classical
  let E := {i : I // (xs i).length % 2 = 0}
  have hc : Submodule.span F (Set.range (fun j => pole a (z j))) = ⊤ :=
    cauchy_span a z q ha hz (by simpa using hcard)
  let T (w : Probe n d) (j : E) := probeEval a z w (xs j.val)
  have h : (fun j : E => v j.val) ∈ (Finsupp.linearCombination F T).range := by
    rw [Finsupp.range_linearCombination, probe_span a z (fun j : E => xs j.val) hc
      (fun j => j.property) (fun j => hw j.val) (fun j => hn j.val)
      (fun i j he => Subtype.ext (hinj i.val j.val he))]
    trivial
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i => ?_⟩
  by_cases hi : (xs i).length % 2 = 0
  · simpa [T, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply] using
      congrFun hc ⟨i, hi⟩
  · rw [hv i (by omega)]
    apply sum_eq_zero
    intro w _
    have he : probeEval a z w (xs i) = 0 := by
      apply wick_odd
      simp only [List.length_append, List.length_map]
      have := w.property.2.2
      omega
    rw [he, mul_zero]

/-- A triangular family of interpolated covectors detects one monomial
under a total weight budget. Values on heavier slots are unrestricted. -/
theorem weighted_probe [DecidableEq A] (a : A → F × ℕ) (z : Fin n → F) (w : A → ℝ)
    (hw : ∀ i, 0 < w i) (xs : List A) (hn : xs.Nodup) (hl : xs.length ≤ d)
    (he : xs.length % 2 = 0) (row : A → A → F)
    (hr : ∀ i j, w j ≤ w i → -row i j = if i = j then 1 else 0)
    (hc : ∀ i ∈ xs, ∃ c : Fin n → F, ∀ j, ∑ k, c k * (z k - (a j).1)⁻¹ ^ ((a j).2 + 1) = row i j) :
    ∃ c : Probe n d →₀ F, ∀ ys : List A, (xs.Perm ys → xs = ys) →
      (ys.map w).sum ≤ (xs.map w).sum →
      ∑ p ∈ c.support, c p * probeEval a z p ys = if xs = ys then 1 else 0 := by
  classical
  let E := {s : List A // s.length % 2 = 0}
  let T (p : Probe n d) (ys : E) := probeEval a z p ys.val
  let M := (Finsupp.linearCombination F T).range
  have hM (p : Probe n d) : T p ∈ M := by
    refine ⟨Finsupp.single p 1, ?_⟩
    simp
  have mem : ∀ f ∈ xs.reverse.map row, f ∈ Submodule.span F (Set.range (fun j => pole a (z j))) := by
    simp only [List.forall_mem_map, List.mem_reverse]
    intro i hi
    obtain ⟨c, he⟩ := hc i hi
    refine (Submodule.mem_span_range_iff_exists_fun F).mpr ⟨c, funext fun j => ?_⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pole] using he j
  obtain ⟨c, h⟩ := covectors_mem a z (fun y : E => y.val) M (fun y => y.property)
    hM (xs.reverse.map row) mem [] (by simpa using hl)
  refine ⟨c, fun ys hp hs => ?_⟩
  by_cases hy : ys.length % 2 = 0
  · have piv := wick_pivot (test a) (fun i => .inl (row i)) .inr w (fun _ => True)
      (fun i _ => hw i) (fun _ _ => rfl) (fun i j _ _ => hr i j)
      xs ys (by simp) (by simp) hn hp hs
    rw [← piv]
    simpa [T, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Function.comp_def]
      using congrFun h ⟨ys, hy⟩
  · have ne : xs ≠ ys := fun e => hy (e ▸ he)
    rw [ite_eq_right ne]
    refine sum_eq_zero fun p _ => mul_eq_zero_of_right _ ?_
    apply wick_odd
    simp only [List.length_append, List.length_map]
    have := p.property.2.2
    omega

universe u

/-- A finite extension and one set of auxiliary marks work simultaneously
for all even forms and all prescribed length bounds on these modes. -/
theorem probe_extension {F : Type u} [Field F] [Fintype A] (a : A ↪ F × ℕ) (q n : ℕ)
    (ha : ∀ i, (a i).2 < q) (hcard : (1 + Fintype.card A) * q < n) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : Module.Finite F K)
      (z : Fin n ↪ K),
      (∀ j i, z j ≠ algebraMap F K (a i).1) ∧
      ∀ (I : Type*) (_ : Fintype I) (xs : I → List A) (d : ℕ),
        (∀ i, (xs i).length ≤ d) → (∀ i, (xs i).Nodup) →
        (∀ i j, (xs i).Perm (xs j) → i = j) → ∀ (v : I → K),
        (∀ i, (xs i).length % 2 = 1 → v i = 0) →
        ∃ c : Probe n d →₀ K, ∀ i, ∑ w ∈ c.support,
          c w * probeEval (fun j => (algebraMap F K (a j).1, (a j).2)) z w (xs i) = v i := by
  classical
  let poles : Set (AlgebraicClosure F) := Set.range (fun i => algebraMap F _ (a i).1)
  have h : polesᶜ.Infinite := (Set.finite_range _).infinite_compl
  let y : Fin n ↪ ↥polesᶜ := Fin.valEmbedding.trans (Set.Infinite.natEmbedding _ h)
  let t := Set.range (fun j => (y j).val)
  let K := IntermediateField.adjoin F t
  have : Finite t := Set.finite_coe_iff.mpr (Set.finite_range _)
  have hK : Module.Finite F K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  let z : Fin n ↪ K :=
    ⟨fun j => ⟨(y j).val, IntermediateField.subset_adjoin F t ⟨j, rfl⟩⟩,
      fun _ _ e => y.injective (Subtype.ext (congrArg (fun x : K => x.val) e))⟩
  have hz (j i) : z j ≠ algebraMap F K (a i).1 :=
    fun e => (y j).property ⟨i, (congrArg (fun x : K => x.val) e).symm⟩
  refine ⟨K, inferInstance, inferInstance, hK, z, hz, ?_⟩
  intro I _ xs d hw hn hinj v hv
  let k : F ↪ K := ⟨algebraMap F K, (algebraMap F K).injective⟩
  exact auxiliary_marks (a.trans (k.prodMap (.refl ℕ))) z q ha hz hcard xs hw hn hinj v hv

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

/-- A pair of independent wires splits as a sum across the two other cuts. -/
def Crossing (K : Type*) [Field K] (a b p q : ℕ) : Prop :=
  ∃ (A B : Fin a → Fin b → Fin p → K) (C D : Fin a → Fin b → Fin q → K),
    ∀ i i' j j', (if i = i' ∧ j = j' then 1 else 0) =
      (∑ z, A i j z * B i' j' z) + (∑ z, C i j' z * D i' j z)

/-- The growth rates can trade off across the two cuts. -/
def ShiftedCrossing (K : Type*) [Field K] : Prop :=
  ∀ t u α β : ℝ, 0 < t → 0 < u → 0 < α → 0 < β → 2 * (t ^ 2 + u ^ 2) < α ^ 2 + β ^ 2 →
    ∀ N : ℝ, ∃ (n : ℝ) (a b p q : ℕ),
      N ≤ n ∧ 0 < p ∧ 0 < q ∧ Real.exp (t * n) ≤ a ∧ Real.exp (u * n) ≤ b ∧
      (p : ℝ) ≤ Real.exp (α * n) ∧ (q : ℝ) ≤ Real.exp (β * n) ∧ Crossing K a b p q

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-! Simultaneous motion of marked points about cluster centers. -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {A F R : Type*} [CommRing R] [Field F] [Algebra F R] {r : ℕ}

open Classical in
noncomputable def clusterKernel (u : R) (N : ℕ) (center offset : A → F)
    (x y : A × Mode r) : R :=
  let Δ := center y.1 - center x.1
  let δ := offset y.1 - offset x.1
  coeff x.2 y.2 (if Δ = 0 then algebraMap F R δ⁻¹
    else u ^ 2 * shifted u (algebraMap F R Δ⁻¹) (algebraMap F R (-δ)) N)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# A colliding cluster and its residual modes

Internal contractions use the site offsets. Every uncontracted generator
is translated to its center. Pairing with a reversed output wedge gives
the coefficient at that wedge.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R] {r : ℕ}

/-- Translation by the offset of a site. -/
def translate (x : Site F r) (y : Mode r) : F :=
  if x.2.1 = y.1 then y.2.choose x.2.2 * x.1 ^ (y.2 - x.2.2) else 0

def blockPair : Site F r ⊕ Mode r → Site F r ⊕ Mode r → F
  | .inl x, .inl y => fieldKernel x y
  | .inl x, .inr y => translate x y
  | .inr x, .inl y => -translate y x
  | .inr _, .inr _ => 0

def blockCoeff (xs : List (Site F r)) (b : Wedge r) : F :=
  wick blockPair (xs.map Sum.inl ++ b.val.reverse.map Sum.inr)

namespace Cluster

/-- A site still in motion, a fused generator, or a dual coordinate test. -/
inductive Leg (F : Type*) (r : ℕ) where
  | moving (c : F) (x : Site F r)
  | fused (x : Site F r)
  | test (center : F) (x : Mode r)

def weight (u : R) (x : Mode r) : R := u ^ (2 * x.2 + 1)

def sep (u : R) (N : ℕ) (c d a b : F) : R :=
  shifted u (algebraMap F R (d - c)⁻¹) (algebraMap F R (a - b)) N

open Classical in
def dualCoeff (x : Site F r) (c : F) (y : Mode r) : R :=
  if x.1 = c then (if x.2 = y then 1 else 0)
  else algebraMap F R (translate (x.1 - c, x.2) y)

open Classical in
def movingDual (u : R) (N : ℕ) (c : F) (x : Site F r) (d : F) (y : Mode r) : R :=
  if c = d then weight u y * algebraMap F R (translate x y)
  else ∑ f ∈ Finset.range N,
    (u ^ (2 * f + 1) * (f.choose x.2.2 : R) * algebraMap F R x.1 ^ (f - x.2.2)) *
      dualCoeff (c, x.2.1, f) d y

open Classical in
def pair (u : R) (N : ℕ) : Leg F r → Leg F r → R
  | .moving c x, .moving d y =>
      if c = d then algebraMap F R (fieldKernel x y) else
      weight u x.2 * weight u y.2 * coeff x.2 y.2 (sep u N c d x.1 y.1)
  | .moving c x, .fused y => weight u x.2 * coeff x.2 y.2 (sep u N c y.1 x.1 0)
  | .fused x, .moving d y => weight u y.2 * coeff x.2 y.2 (sep u N x.1 d 0 y.1)
  | .fused x, .fused y => algebraMap F R (fieldKernel x y)
  | .moving c x, .test d y => movingDual u N c x d y
  | .test d x, .moving c y => -movingDual u N c y d x
  | .fused x, .test d y => dualCoeff x d y
  | .test d x, .fused y => -dualCoeff y d x
  | .test _ _, .test _ _ => 0

variable (u : R) (N : ℕ)

private theorem sep_skew (c d a b : F) : sep u N d c b a = -sep u N c d a b := by
  unfold sep shifted
  rw [← neg_sub d c, ← neg_sub a b, inv_neg, map_neg, map_neg]
  simp only [neg_mul, mul_neg, neg_neg]

theorem pair_skew (x y : Leg F r) : pair u N y x = -pair u N x y := by
  classical
  rcases x with ⟨c, x⟩|x|⟨_, x⟩ <;> rcases y with ⟨d, y⟩|y|⟨_, y⟩ <;> simp only [pair, neg_neg, neg_zero]
  · by_cases h : c = d
    · simp only [ite_eq_left h, ite_eq_left h.symm, fieldKernel_skew x y, map_neg]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), sep_skew u N c d, coeff_skew, mul_neg, mul_comm (weight u y.2)]
  · rw [sep_skew u N c y.1, coeff_skew, mul_neg]
  · rw [sep_skew u N x.1 d, coeff_skew, mul_neg]
  · rw [fieldKernel_skew x y, map_neg]

theorem pair_self (x : Leg F r) : pair u N x x = 0 := by
  cases x <;> simp [pair, fieldKernel_self]

private theorem field_map (x y : Site F r) :
    algebraMap F R (fieldKernel x y) = coeff x.2 y.2 (algebraMap F R (y.1 - x.1)⁻¹) := by
  unfold fieldKernel coeff
  split_ifs <;> simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_zero]

theorem pair_moving (c d : F) (x y : Site F r) :
    pair u N (.moving c x) (.moving d y) =
      clusterKernel u N Prod.fst Prod.snd ((c, x.1), x.2) ((d, y.1), y.2) := by
  classical
  simp only [pair, clusterKernel, sub_eq_zero, neg_sub]
  by_cases h : c = d
  · simp only [ite_eq_left h, ite_eq_left h.symm, field_map]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    unfold weight coeff sep
    split_ifs
    · rw [mul_pow, ← pow_mul, ← pow_add]
      have he : 2 * x.2.2 + 1 + (2 * y.2.2 + 1) = 2 * (x.2.2 + y.2.2 + 1) := by omega
      rw [he]
      ring
    · simp

variable (c : F)

def belongs : Leg F r → Prop
  | .moving d _ => c = d
  | _ => False

open Classical in
private def external (x y : Leg F r) :=
  if belongs c x ∧ belongs c y then 0 else pair u N x y

private theorem external_skew (x y : Leg F r) :
    external u N c y x = -external u N c x y := by
  by_cases h : belongs c x ∧ belongs c y
  · simp [external, h]
  · have ht : ¬ (belongs c y ∧ belongs c x) := fun hy => h hy.symm
    simp only [external, h, ht, ↓reduceIte, pair_skew u N x y]

private theorem external_self (x : Leg F r) : external u N c x x = 0 := by
  simp [external, pair_self]

private theorem translate_row (hu : u ^ N = 0) (x : Site F r) (y : Leg F r) :
    external u N c (.moving c x) y = ∑ f ∈ Finset.range N,
      (u ^ (2 * f + 1) * (f.choose x.2.2 : R) * algebraMap F R x.1 ^ (f - x.2.2)) *
        external u N c (.fused (c, x.2.1, f)) y := by
  classical
  cases y with
  | test d y =>
    by_cases hd : c = d
    swap
    · simp only [external, belongs, and_false, ↓reduceIte, pair, movingDual, ite_eq_right hd]
    subst d
    obtain ⟨i, b⟩ := y
    simp only [external, belongs, and_false, ↓reduceIte, pair, movingDual, dualCoeff, translate, weight, Prod.mk.injEq]
    by_cases hi : x.2.1 = i
    · simp only [hi, ↓reduceIte, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_range, map_mul, map_pow, map_natCast]
      split_ifs with hb
      · exact (mul_assoc _ _ _).symm
      · rw [pow_eq_zero_of_le (by omega : N ≤ 2 * b + 1) hu, zero_mul]
    · simp [hi]
  | fused y =>
    simp only [external, belongs, and_false, ↓reduceIte, pair, field_map, sep, sub_zero, weight]
    exact coeff_shifted _ _ _ _ hu _ _
  | moving d y =>
    simp only [external, belongs, true_and, false_and, ↓reduceIte, pair]
    by_cases h : c = d
    · subst d
      simp [sep, shifted, coeff]
    · simp only [ite_eq_right h]
      have sep_eq : sep u N c d x.1 y.1 =
          shifted u (sep u N c d 0 y.1) (algebraMap F R x.1) N := by
        unfold sep
        rw [shifted_add _ _ _ _ _ hu, ← map_add, zero_sub, neg_add_eq_sub]
      rw [sep_eq, mul_comm (weight u x.2), mul_assoc, weight, weight,
        coeff_shifted _ _ _ _ hu, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)

private theorem weight_prod (xs : List (Mode r)) :
    (xs.map (weight u)).prod = u ^ energy xs := by
  induction xs with
  | nil => simp [energy]
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, ih, weight, ← pow_add]
    rfl

private theorem probe (xs : List (Site F r)) (b : Wedge r) :
    wick (pair u N) (xs.map (Leg.moving c) ++ b.val.reverse.map (Leg.test c)) =
      u ^ energy b.val * algebraMap F R (blockCoeff xs b) := by
  let label : Site F r ⊕ Mode r → Leg F r := Sum.elim (Leg.moving c) (Leg.test c)
  let s : Site F r ⊕ Mode r → R := Sum.elim (fun _ => 1) (weight u)
  have e (x y : Site F r ⊕ Mode r) :
      pair u N (label x) (label y) = s x * s y * algebraMap F R (blockPair x y) := by
    cases x <;> cases y <;> simp [label, pair, movingDual, s, blockPair]
  let z := xs.map Sum.inl ++ b.val.reverse.map Sum.inr
  have he : z.map label = xs.map (Leg.moving c) ++ b.val.reverse.map (Leg.test c) := by
    simp [z, label, Function.comp_def]
  rw [← he, wick_map]
  simp only [e, wick_scale_rows, ← wick_hom]
  congr 1
  simpa [z, s, Function.comp_def] using weight_prod u b.val

private theorem center_probe (a b : Wedge r) :
    wick (pair u N) (a.val.map (fun i => .fused (c, i)) ++ b.val.reverse.map (Leg.test c)) =
      if a.val = b.val then 1 else 0 := by
  apply wick_dual (pair_skew u N)
  · intro x y
    simp [pair, fieldKernel, coeff]
  · intro x y; rfl
  · intro x y; simp only [pair, dualCoeff, ↓reduceIte]

private theorem factor (hu : u ^ N = 0) (xs : List (Site F r)) :
    ∃ v : Wedge r →₀ R,
      ∀ ys : List (Leg F r), (∀ y ∈ ys, ¬ belongs c y) →
      wick (pair u N) (xs.map (Leg.moving c) ++ ys) =
        ∑ b ∈ v.support, v b * wick (pair u N) (b.val.map (fun i => .fused (c, i)) ++ ys) := by
  let internal (x y : Leg F r) := pair u N x y - external u N c x y
  obtain ⟨v, hv⟩ := wick_factor internal (external_skew u N c) (external_self u N c)
    (fun i => .fused (c, i)) (xs.map (Leg.moving c)) (by
      simp only [List.forall_mem_map]
      intro x _
      exact ⟨Finset.range N, _, _, translate_row u N c hu x⟩)
  refine ⟨v, fun ys hy => ?_⟩
  have h := hv ys (fun x y h => by simp [internal, external, hy y h])
  have e (b : Wedge r) :
      wick (external u N c) (b.val.map (fun i => .fused (c, i)) ++ ys) =
        wick (pair u N) (b.val.map (fun i => .fused (c, i)) ++ ys) := by
    apply wick_eq_on
    have hm : ∀ z ∈ b.val.map (fun i => Leg.fused (c, i)) ++ ys, ¬ belongs c z := by
      simp only [List.forall_mem_append, List.forall_mem_map]
      exact ⟨fun _ _ => not_false, hy⟩
    exact fun x hx y _ => by simp [external, hm x hx]
  simpa only [internal, sub_add_cancel, e] using h

private theorem block_front (hu : u ^ N = 0) (xs : List (Site F r))
    (ys : List (Leg F r)) (hy : ∀ y ∈ ys, ¬ belongs c y) :
    wick (pair u N) (xs.map (Leg.moving c) ++ ys) =
      ∑ b : LevelLE r N, u ^ energy b.val.val * algebraMap F R (blockCoeff xs b.val) *
        wick (pair u N) (b.val.val.map (fun i => .fused (c, i)) ++ ys) := by
  classical
  obtain ⟨v, hv⟩ := factor u N c hu xs
  have val (b : Wedge r) : v b = u ^ energy b.val * algebraMap F R (blockCoeff xs b) := by
    have h := hv (b.val.reverse.map (Leg.test c)) (by simp only [List.forall_mem_map, belongs, not_false_eq_true, implies_true])
    simp only [probe, center_probe] at h
    have eq (z : Wedge r) : z.val = b.val ↔ z = b := Subtype.ext_iff.symm
    simp only [eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] at h
    by_cases hb : b ∈ v.support <;> simpa [hb, Finsupp.notMem_support_iff.mp] using h.symm
  have sub : v.support ⊆ Finset.univ.image (fun b : LevelLE r N => b.val) := by
    intro b hb
    have he : energy b.val ≤ N := by
      by_contra hn
      rw [Finsupp.mem_support_iff, val, pow_eq_zero_of_le (by omega : N ≤ energy b.val) hu,
        zero_mul] at hb
      exact hb rfl
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨b, he⟩ : LevelLE r N))
  rw [hv ys hy, Finset.sum_subset sub (fun b _ hb => by rw [Finsupp.notMem_support_iff.mp hb, zero_mul]),
    Finset.sum_image Subtype.val_injective.injOn]
  simp only [val]

theorem blockCoeff_parity (xs : List (Site F r)) (b : Wedge r)
    (h : blockCoeff xs b ≠ 0) : xs.length % 2 = b.val.length % 2 := by
  by_contra hn
  apply h
  apply wick_odd
  simp only [List.length_append, List.length_map, List.length_reverse]
  omega

/-- Fuse one cluster in place. Only equal-parity output blocks contribute,
so moving the cluster past the preceding sites creates no net sign. -/
theorem block (hu : u ^ N = 0) (xs : List (Site F r)) (pre post : List (Leg F r))
    (hpre : ∀ y ∈ pre, ¬ belongs c y) (hpost : ∀ y ∈ post, ¬ belongs c y) :
    wick (pair u N) (pre ++ xs.map (Leg.moving c) ++ post) =
      ∑ b : LevelLE r N, u ^ energy b.val.val * algebraMap F R (blockCoeff xs b.val) *
        wick (pair u N) (pre ++ b.val.val.map (fun i => .fused (c, i)) ++ post) := by
  classical
  have move (s : List (Leg F r)) :
      wick (pair u N) (pre ++ s ++ post) =
        (-1 : R) ^ (s.length * pre.length) * wick (pair u N) (s ++ (pre ++ post)) := by
    simpa only [List.nil_append, List.append_assoc, Nat.mul_comm] using
      wick_swap_blocks (pair_skew u N) [] pre s post
  rw [move, block_front u N c hu xs _ (List.forall_mem_append.mpr ⟨hpre, hpost⟩), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : blockCoeff xs b.val = 0
  · simp [hb]
  · have sign : (-1 : R) ^ xs.length = (-1 : R) ^ b.val.val.length := by
      rw [neg_one_pow_eq_pow_mod_two xs.length, blockCoeff_parity xs b.val hb,
        ← neg_one_pow_eq_pow_mod_two]
    rw [move]
    simp only [List.length_map, pow_mul, sign]
    exact mul_left_comm _ _ _

end Cluster
end OAI.LinearAlgebra.MatrixExponent.Sphere
end
