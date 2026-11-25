import OAI.Computability.BorderVNP.CellPrefixGenerator
import OAI.Computability.BorderVNP.CellProfileCounts
import OAI.Computability.BorderVNP.CellSparseTable

/-!
# The compiled private profile checker

The loops use original copy order, candidate count order, and lane order. Original
data wires start after the auxiliary prefix, and rank flags select the precise
destination copy. The program stores each copy-loop body once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix
open scoped Classical

/-- Conjunctive compiled test for a proposition about an immutable value bank. -/
def Tests (s : Stmt) (e : List ℕ) (P : (ℕ → Bool) → Prop) : Prop :=
  Checks s e fun bank => decide (P bank)

private theorem tests_congr {s : Stmt} {e : List ℕ} {p q : (ℕ → Bool) → Prop}
    (h : Tests s e p) (he : ∀ b, p b ↔ q b) : Tests s e q :=
  checks_congr h (fun bank => by simp only [he bank])

private theorem tests_term (a : Term) (e : List ℕ) (P : (ℕ → Bool) → Prop)
    (h : ∀ b, a.eval e b = true ↔ P b) : Tests a.guard e P :=
  checks_congr (term_checks a e) (fun b => Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact h b))

private theorem tests_loop (n : ℕ) (s : Stmt) (e : List ℕ) (P : ℕ → (ℕ → Bool) → Prop)
    (h : ∀ i < n, Tests s (i::e) (P i)) :
    Tests (.loop (.lit n) s) e (fun b => ∀ i < n, P i b) :=
  checks_congr (loop_checks (.lit n) s e (fun i b => decide (P i b)) h)
    (fun b => Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true,List.mem_range,decide_eq_true_eq,NatExpr.eval]))

private theorem tests_seq {a b : Stmt} {e : List ℕ} {P Q : (ℕ → Bool) → Prop}
    (h : Tests a e P) (j : Tests b e Q) : Tests (.seq a b) e (fun v => P v ∧ Q v) :=
  checks_congr (seq_checks h j) fun v => by simp

private theorem tests_list {α : Type*} (xs : List α) (s : α → Stmt) (e : List ℕ)
    (P : α → (ℕ → Bool) → Prop) (h : ∀ x ∈ xs, Tests (s x) e (P x)) :
    Tests (sequence (xs.map s)) e (fun b => ∀ x ∈ xs, P x b) :=
  checks_congr (sequence_checks xs s e (fun x b => decide (P x b)) h)
    (fun b => Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true,decide_eq_true_eq]))

/-- Data-bank lookup after the separately guessed auxiliary prefix. -/
def data (off : ℕ) (b : ℕ → Bool) : ℕ → Bool := fun j => b (off+j)

/-- Physical address expression for one original port after the auxiliary prefix. -/
def portExpr (off : ℕ) (p : Port) (i k : NatExpr) := NatExpr.add (.lit off) (p.expr i k)

/-- The selector match test reads its little-endian lanes and checks even the high
bits of the constant term code. -/
def selectTerm (off : ℕ) (p : Port) (w t : ℕ) (i : NatExpr) : Term :=
  wordIs ((List.range w).map fun k => portExpr off p i (.lit k)) t

private theorem word_shift (bank : ℕ → Bool) (off : ℕ) (js : List ℕ) :
    word bank (js.map (off+·)) = word (data off bank) js := by
  induction js with
  | nil => rfl
  | cons j js ih => cases h : bank (off+j) <;> simp [word,data,ih,h]

/-- Interpreting the match predicate is equality to the true selector label. -/
theorem selectTerm_correct (off : ℕ) (p : Port) (w t : ℕ) (i : NatExpr) (e : List ℕ) (b : ℕ → Bool) :
    (selectTerm off p w t i).eval e b = true ↔ label (data off b) p w (i.eval e) = t := by
  rw [selectTerm,wordIs_correct,label,← word_shift]
  simp [Port.lanes,List.map_map,Function.comp_def,portExpr,NatExpr.eval]

/-- Every copy's selector must name one of the actual terms. -/
def rangeGen (off copies : ℕ) (s : Port) (w terms : ℕ) : Stmt :=
  .loop (.lit copies) ((Term.any ((List.range terms).map fun t => selectTerm off s w t (.index 0))).guard)

private theorem rangeGen_checks (off copies : ℕ) (s : Port) (w terms : ℕ) (e : List ℕ) :
    Tests (rangeGen off copies s w terms) e (fun b => ∀ i < copies, label (data off b) s w i < terms) := by
  apply tests_loop
  intro i _
  apply tests_term
  intro b
  simp only [Term.eval_any, List.any_eq_true, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_,⟨t,ht,rfl⟩, hm⟩
    have he := (selectTerm_correct ..).mp hm
    change label (data off b) s w i = t at he
    omega
  · intro h
    refine ⟨_, ⟨label (data off b) s w i,h,rfl⟩, (selectTerm_correct ..).mpr rfl⟩

/-- Generate one auxiliary prefix table and check its final count. An advertised
count beyond the table cap fails immediately. -/
def termGen (base off copies : ℕ) (s : Port) (w t advertised : ℕ) : Stmt :=
  let origin := termBase base copies t
  .seq (generator origin copies copies (selectTerm off s w t))
    ((if advertised ≤ copies then flagTerm origin copies (.lit copies) (.lit advertised) else .lit false).guard)

private theorem termGen_checks (base off copies : ℕ) (s : Port) (w t advertised : ℕ) (e : List ℕ) :
    Tests (termGen base off copies s w t advertised) e
      (fun b => CountCheck (data off b) copies s w t advertised (bankFlags b base copies)) := by
  apply tests_seq
  · apply generator_checks
    intro bank i
    apply Bool.eq_iff_iff.mpr
    rw [selectTerm_correct, selects, decide_eq_true_eq]
    rfl
  · apply tests_term
    intro b
    by_cases h : advertised ≤ copies <;> simp [h,Term.eval,flagTerm,address,bankFlags,NatExpr.eval]

/-- The one-lane comparison conditional on the selector and its active rank. -/
def laneTest (base off copies : ℕ) (s : Port) (w : ℕ) (r : Route) : Term :=
  let i := NatExpr.index 2
  let k := NatExpr.index 1
  let lane := NatExpr.index 0
  let enabled := (selectTerm off s w r.term i).and (flagTerm (termBase base copies r.term) copies i k)
  enabled.implies ((Term.wire (portExpr off r.original i lane)).equal (.wire (portExpr off r.compact k lane)))

/-- One route record checks each occupied rank/copy pair using the forced flag
at the strictly earlier prefix. Lane comparisons are separate instructions. -/
def routeGen (base off copies : ℕ) (s : Port) (w terms : ℕ) (r : Route) : Stmt :=
  .seq ((Term.lit (decide (r.term < terms))).guard) (.loop (.lit copies)
    (.loop (.lit (copies+1)) (.loop (.lit r.lanes) (laneTest base off copies s w r).guard)))

private theorem implies_eval (a b : Term) (e : List ℕ) (v : ℕ → Bool) :
    (a.implies b).eval e v = true ↔ (a.eval e v = true → b.eval e v = true) := by
  cases ha : a.eval e v <;> simp [Term.implies,Term.eval,ha]

private theorem routeGen_checks (base off copies : ℕ) (s : Port) (w terms : ℕ) (r : Route) (e : List ℕ) :
    Tests (routeGen base off copies s w terms r) e
      (fun b => RouteCheck (data off b) copies s w terms (bankFlags b base copies) r) := by
  apply tests_seq
  · apply tests_term; intro b; simp [Term.eval]
  · apply tests_congr (tests_loop copies _ e (fun i b => ∀ k < copies+1, ∀ l < r.lanes,
      label (data off b) s w i = r.term → bankFlags b base copies r.term i k = true →
        data off b (r.original.atBit i l) = data off b (r.compact.atBit k l)) ?_)
    · intro b; simp only [Nat.lt_succ_iff]
    · intro i _
      apply tests_loop
      intro k _
      apply tests_loop
      intro l _
      apply tests_term
      intro b
      simp only [laneTest,implies_eval,Term.eval, Bool.and_eq_true, selectTerm_correct, Term.eval_equal,
        decide_eq_true_eq, eval_flagTerm, portExpr, Port.eval_expr, NatExpr.eval, List.getD_cons_zero,
        List.getD_cons_succ, bankFlags, data, and_imp]

/-- Full compact descriptor for the private profile tests. -/
def profileGen (base off copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ) (routes : List Route) : Stmt :=
  .seq (rangeGen off copies s w hist.length) (.seq
    (sequence (hist.zipIdx.map fun p => termGen base off copies s w p.2 p.1))
    (sequence (routes.map (routeGen base off copies s w hist.length))))

/-- The compact generator checks all and only the profile constraints, including
the uniquely forced private count flags, and preserves the bank for its continuation. -/
theorem profileGen_checks (base off copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ)
    (routes : List Route) (e : List ℕ) :
    Tests (profileGen base off copies s w hist routes) e
      (fun b => Accept (data off b) copies s w hist routes (bankFlags b base copies)) := by
  apply tests_seq (rangeGen_checks off copies s w hist.length e)
  apply tests_seq
  · apply tests_congr (tests_list hist.zipIdx (fun p => termGen base off copies s w p.2 p.1) e
      (fun p b => CountCheck (data off b) copies s w p.2 p.1 (bankFlags b base copies))
      (fun p _ => termGen_checks base off copies s w p.2 p.1 e))
    intro b
    constructor
    · intro h t
      exact h (hist[t],t.val) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
    · rintro h ⟨v,i⟩ hm
      obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hm)
      change hist[i] = v at he
      change CountCheck (data off b) copies s w i v (bankFlags b base copies)
      rw [← he]
      exact h ⟨i,hi⟩
  · apply tests_list
    intro r _
    exact routeGen_checks base off copies s w hist.length r e

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
