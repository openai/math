import OAI.Computability.BorderVNP.CellReportedWord

/-! # Traversing privately repeated boxes for gadget counts and range checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro
open Profile (data)
open scoped Classical

/-- Number of factor occurrences, computed by multiplying sparse multiplicities. -/
def Directory.visitCount (D : Directory) : ℕ :=
  (D.blocks.map fun b => b.copies * b.factors.length).sum

/-- The compact count agrees with the number of rows visited by the private scan. -/
theorem Directory.visitCount_eq (D : Directory) : D.visitCount = D.occurrences.length := by
  rw [visitCount, ← D.blocks_visits, List.length_flatMap]
  simp only [BoxBlock.length_visits]

private theorem foldl_checks {α : Type*} (xs : List α) (p : α → Bool) (f : Flags) :
    xs.foldl (fun s x => (⟨s.ok && p x, s.minus⟩ : Flags)) f =
      ⟨f.ok && xs.all p, f.minus⟩ := by
  induction xs generalizing f with
  | nil => simp
  | cons a xs ih => simp [ih, Bool.and_assoc]

/-- A compact box sweep checks every indexed occurrence and preserves its sign and bank. -/
theorem sweep_tests (body : FactorBody) (D : Directory) (e : List ℕ)
    (p : (ℕ → Bool) → Occurrence → ℕ → Prop)
    (h : ∀ f j off i env, Profile.Tests (body f j off i) env (fun b =>
      p b ⟨f,off.eval env,i.eval env⟩ (j.eval env))) :
    Profile.Tests (sweep body D.blocks 0) e (fun b => ∀ z ∈ D.occurrences.zipIdx, p b z.1 z.2) := by
  intro ops st v
  have hs := sweep_acts body D.blocks 0 e
    (fun b s z => (⟨s.ok && decide (p b z.1 z.2), s.minus⟩ : Flags)) h ops st v
  rw [D.blocks_visits] at hs
  rw [hs]
  simp only []
  rw [foldl_checks D.occurrences.zipIdx (fun z => decide (p (lookup v) z.1 z.2)) st]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

/-- A missing gadget entry has no identifier. A present one must lie in the
directory of announced counts. The ordinary factor scan also checks presence. -/
def rangeTerm (limit : ℕ) (off : NatExpr) : Factor → Term
  | .gadget ws rows => (rowTest (tableWires off ws) (fun id => decide (limit ≤ id)) rows).not
  | _ => .lit true

/-- A range guard only removes an assignment with an actually selected out-of-range identifier. -/
theorem rangeTerm_correct (limit : ℕ) (f : Factor) (off copy : NatExpr) (e : List ℕ) (b : ℕ → Bool) :
    (rangeTerm limit off f).eval e b =
      ((f.observe b (off.eval e) (copy.eval e)).bind Prod.snd).all (fun a => decide (a < limit)) := by
  cases f with
  | gadget ws rows =>
    have he : (rowTest (tableWires off ws) (fun id => decide (limit ≤ id)) rows).eval e b =
        (rows[word b (ws.map (off.eval e + ·))]?).any (fun id => decide (limit ≤ id)) := by
      apply Bool.eq_iff_iff.mpr
      rw [rowTest_correct, tableWires_eval]
      cases rows[word b (ws.map (off.eval e + ·))]? <;> simp
    simp only [rangeTerm, Term.eval, he, Factor.observe]
    cases rows[word b (ws.map (off.eval e + ·))]? <;> simp
    rename_i a
    by_cases h : limit ≤ a <;> simp [h, show a < limit ↔ ¬ limit ≤ a by omega]
  | truth ws rows => simp [rangeTerm, Term.eval, Factor.observe]; split <;> rfl
  | sign ws rows => simp [rangeTerm, Term.eval, Factor.observe]; cases rows[word b (ws.map (off.eval e + ·))]? <;> rfl
  | unary i p => simp [rangeTerm, Term.eval, Factor.observe]; split <;> rfl

/-- Scan the sparse boxes to reject every observed identifier outside the report list. -/
def Directory.rangeGuard (D : Directory) : Stmt :=
  sweep (fun f _ off _ => (rangeTerm D.reportedCounts.length off f).guard) D.blocks 0

/-- Exact semantics of the range check, including missing entries. -/
theorem Directory.rangeGuard_checks (D : Directory) (e : List ℕ) :
    Profile.Tests D.rangeGuard e (fun b => ∀ o ∈ D.occurrences,
      ((o.factor.observe b o.offset o.copy).bind Prod.snd).all (fun a => decide (a < D.reportedCounts.length)) = true) := by
  apply Prefix.checks_congr (sweep_tests _ D e (fun b o _ =>
    ((o.factor.observe b o.offset o.copy).bind Prod.snd).all (fun a => decide (a < D.reportedCounts.length)) = true) ?_)
  · intro b
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h o ho
      have hm : o ∈ D.occurrences.zipIdx.map Prod.fst := by simpa using ho
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hm
      exact h z hz
    · intro h z hz
      have hm : z.1 ∈ D.occurrences.zipIdx.map Prod.fst := List.mem_map.mpr ⟨z,hz,rfl⟩
      exact h z.1 (by simpa using hm)
  · intro f j off copy env ops st v
    rw [Term.value_guard, rangeTerm_correct _ f off copy]
    simp

namespace Gadget

/-- One sparse body of the count traversal. The prefix index and physical bit
offset vary with the lexical copy counter. -/
def stepBody (cap aux id : ℕ) : FactorBody := fun f idx off _ =>
  Prefix.stepGen 0 cap idx (factorSelect (.add (.lit aux) off) id (f.shift aux))

/-- The sparse traversal generates each and every transition of the rectangular count table. -/
theorem steps_checks (D : Directory) (cap aux id : ℕ) (e : List ℕ) :
    Profile.Tests (sweep (stepBody cap aux id) D.blocks 0) e (fun bank =>
      ∀ i < D.occurrences.length, Prefix.Step cap i
        ((D.occurrences[i]?).any (selected id (data aux bank)))
        (fun j k => bank (Prefix.address 0 cap j k))) := by
  apply Prefix.checks_congr (sweep_tests _ D e (fun b o idx => Prefix.Step cap idx
    (selected id (data aux b) o) (fun j k => b (Prefix.address 0 cap j k))) ?_)
  · intro b
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h i hi
      have hm : (D.occurrences[i], i) ∈ D.occurrences.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
      simpa [List.getElem?_eq_getElem hi] using h (D.occurrences[i],i) hm
    · intro h z hz
      have he := List.mem_zipIdx_iff_getElem?.mp hz
      have hi : z.2 < D.occurrences.length := by
        by_contra! hf
        simp [List.getElem?_eq_none_iff.mpr hf] at he
      simpa [he] using h z.2 hi
  · intro f j off copy env
    apply Prefix.checks_congr (Prefix.stepGen_checks 0 cap j (factorSelect (.add (.lit aux) off) id (f.shift aux)) env)
    intro b
    rw [factorSelect_total id aux f off copy]

end Gadget
end CellSparse

end BorderVNP
end Computability
end OAI
