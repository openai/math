import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.BorderVNP.CellProfileCost

/-! # Actual private work of the factor, range and count-row scans

The scalar table is addressed by the original list of private wires. Bounds below separately
charge the number of table rows, the width of their keys, and the actual physical read addresses.
Repeated sites are charged exactly once for each visited copy and factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro
open private wordIs_nodes wordIs_bounded from OAI.Computability.BorderVNP.CellProfileCost

/-- Bound both the arity of each key and the number of stored rows. -/
def Factor.TableBound (f : Factor) (M : ℕ) : Prop :=
  match f with
  | .truth ws rs | .sign ws rs => ws.length ≤ M ∧ rs.length ≤ M
  | .gadget ws rs => ws.length ≤ M ∧ rs.length ≤ M
  | .unary .. => True

/-- Bound the literal wire addresses consulted by a factor at a particular copy. -/
def Factor.ReadBound (f : Factor) (off copy A : ℕ) : Prop :=
  match f with
  | .truth ws _ | .sign ws _ | .gadget ws _ => ∀ w ∈ ws, off + w ≤ A
  | .unary w p => off + w ≤ A ∧ p.atBit copy 0 ≤ A

/-- Relocating the public use bit never changes table dimensions. -/
@[simp] theorem Factor.tableBound_shift (f : Factor) (aux M : ℕ) :
    (f.shift aux).TableBound M ↔ f.TableBound M := by cases f <;> rfl

/-- A bank prefix shifts the address bound of every original wire by its length. -/
theorem Factor.readBound_shift (f : Factor) (aux off copy A : ℕ) (h : f.ReadBound off copy A) :
    (f.shift aux).ReadBound (aux + off) copy (aux + A) := by
  cases f <;> simp only [Factor.shift, Factor.ReadBound, Port.atBit_shift, Nat.add_assoc,
    Nat.add_le_add_iff_left] at h ⊢ <;> exact h

/-- Uniform syntax-node bound for any pass, sign, range or gadget-ID test. -/
def factorNodeBound (M : ℕ) := (10*M+10)*(M+1)

private theorem rowTest_member {α : Type} (as : List NatExpr) (p : α → Bool) (rs : List α)
    (t : Term) (h : t ∈ rs.zipIdx.filterMap (fun z => if p z.1 then some (wordIs as z.2) else none)) :
    ∃ j, t = wordIs as j := by
  obtain ⟨z, _, hz⟩ := List.mem_filterMap.mp h
  split at hz
  · exact ⟨z.2, (Option.some.inj hz).symm⟩
  · contradiction

/-- Each selected row contributes at most one word equality and one disjunction node. -/
theorem rowTest_nodes_le {α : Type} (as : List NatExpr) (p : α → Bool) (rs : List α) :
    (rowTest as p rs).nodes ≤ rs.length*(10*as.length+2)+1 := by
  let ts := rs.zipIdx.filterMap fun z => if p z.1 then some (wordIs as z.2) else none
  have hlen : ts.length ≤ rs.length := by
    exact (List.length_filterMap_le ..).trans_eq (List.length_zipIdx ..)
  have hs := sum_map_le ts Term.nodes (10*as.length+1) (fun t ht => by
    obtain ⟨j,rfl⟩ := rowTest_member as p rs t ht
    rw [wordIs_nodes])
  change (Term.any ts).nodes ≤ _
  rw [Term.nodes_any]
  calc
    _ ≤ ts.length*(10*as.length+2)+1 := by rw [show 10*as.length+2 = 10*as.length+1+1 by omega, Nat.mul_succ]; omega
    _ ≤ _ := by gcongr

private theorem row_nodes {α : Type} (off : NatExpr) (ws : List ℕ) (p : α → Bool) (rs : List α)
    {M : ℕ} (h : ws.length ≤ M ∧ rs.length ≤ M) :
    (rowTest (tableWires off ws) p rs).nodes + 1 ≤ factorNodeBound M := by
  have hr := rowTest_nodes_le (tableWires off ws) p rs
  rw [show (tableWires off ws).length = ws.length by simp [tableWires]] at hr
  have hb := Nat.mul_le_mul h.2 (show 10*ws.length+2 ≤ 10*M+2 by omega)
  unfold factorNodeBound
  nlinarith

private theorem row_bounded {α : Type} (off : NatExpr) (ws : List ℕ) (p : α → Bool) (rs : List α)
    (e : List ℕ) {A : ℕ} (h : ∀ w ∈ ws, off.eval e + w ≤ A) :
    (rowTest (tableWires off ws) p rs).Bounded e A := by
  apply Term.bounded_any
  intro t ht
  obtain ⟨j,rfl⟩ := rowTest_member _ _ _ t ht
  apply wordIs_bounded
  intro a ha
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
  exact h _ hw

/-- Size of the positive-or-present factor test, including the unary-use equality. -/
theorem factorPass_nodes_le (off copy : NatExpr) (f : Factor) {M : ℕ} (h : f.TableBound M) :
    (factorPass off copy f).nodes ≤ factorNodeBound M := by
  cases f with
  | truth w r => exact (Nat.le_succ _).trans (row_nodes off w id r h)
  | sign w r | gadget w r => exact (Nat.le_succ _).trans (row_nodes off w (fun _ => true) r h)
  | unary w p => simp [factorPass, Term.nodes, factorNodeBound]; nlinarith

/-- Size of the sign parity test. -/
theorem factorSign_nodes_le (off : NatExpr) (f : Factor) {M : ℕ} (h : f.TableBound M) :
    (factorSign off f).nodes ≤ factorNodeBound M := by
  cases f with
  | sign w r => exact (Nat.le_succ _).trans (row_nodes off w id r h)
  | _ => change 1 ≤ (10*M+10)*(M+1); nlinarith

/-- Size of one gadget selector, used in every generated count candidate. -/
theorem factorSelect_nodes_le (off : NatExpr) (id : ℕ) (f : Factor) {M : ℕ} (h : f.TableBound M) :
    (factorSelect off id f).nodes ≤ factorNodeBound M := by
  cases f with
  | gadget w r => exact (Nat.le_succ _).trans (row_nodes off w (fun x => decide (x = id)) r h)
  | _ => change 1 ≤ (10*M+10)*(M+1); nlinarith

/-- Size of the test for an out-of-range identifier. -/
theorem rangeTerm_nodes_le (limit : ℕ) (off : NatExpr) (f : Factor) {M : ℕ} (h : f.TableBound M) :
    (rangeTerm limit off f).nodes ≤ factorNodeBound M := by
  cases f with
  | gadget w r => exact row_nodes off w (fun x => decide (limit ≤ x)) r h
  | _ => change 1 ≤ (10*M+10)*(M+1); nlinarith

/-- All reads of the factor-presence test are covered by its physical address bound. -/
theorem factorPass_bounded (off copy : NatExpr) (f : Factor) (e : List ℕ) {A : ℕ}
    (h : f.ReadBound (off.eval e) (copy.eval e) A) : (factorPass off copy f).Bounded e A := by
  cases f with
  | truth w r => exact row_bounded off w id r e h
  | sign w r | gadget w r => exact row_bounded off w (fun _ => true) r e h
  | unary w p => exact (Term.bounded_equal ..).mpr h

/-- All reads of a sign table occur at its original wires. -/
theorem factorSign_bounded (off copy : NatExpr) (f : Factor) (e : List ℕ) {A : ℕ}
    (h : f.ReadBound (off.eval e) (copy.eval e) A) : (factorSign off f).Bounded e A := by
  cases f with
  | sign w r => exact row_bounded off w id r e h
  | _ => trivial

/-- The gadget-ID test is bounded even for a missing or out-of-range table row. -/
theorem factorSelect_bounded (off copy : NatExpr) (id : ℕ) (f : Factor) (e : List ℕ) {A : ℕ}
    (h : f.ReadBound (off.eval e) (copy.eval e) A) : (factorSelect off id f).Bounded e A := by
  cases f with
  | gadget w r => exact row_bounded off w (fun x => decide (x = id)) r e h
  | _ => trivial

/-- The range test inspects only its actual private table wires. -/
theorem rangeTerm_bounded (limit : ℕ) (off copy : NatExpr) (f : Factor) (e : List ℕ) {A : ℕ}
    (h : f.ReadBound (off.eval e) (copy.eval e) A) : (rangeTerm limit off f).Bounded e A := by
  cases f with
  | gadget w r => exact row_bounded off w (fun x => decide (limit ≤ x)) r e h
  | _ => trivial

/-- One sign update costs the same five-symbol opcode as a guard. -/
theorem Term.work_sign_le (t : Term) (e : List ℕ) {A N : ℕ} (hA : t.Bounded e A) (hN : t.nodes ≤ N) :
    work t.sign e ≤ guardCost A N := by
  have hw := t.work_guard_le e hA hN
  simpa only [sign, guard, work_seq, work_fixed, guardCost, Op.bits, List.length_cons, List.length_nil] using hw

/-- One box contributes its copy multiplicity times its one-copy row count. The
per-row hypothesis can use both the occurring factor and its absolute row number. -/
theorem BoxBlock.fragment_work_le (b : BoxBlock) (start : ℕ) (body : FactorBody) (e : List ℕ) (C : ℕ)
    (h : ∀ f j off i env, (⟨f, off.eval env, i.eval env⟩ : Occurrence) ∈ b.visits →
      j.eval env < start + b.visits.length → work (body f j off i) env ≤ C) :
    work (b.fragment start body) e ≤ b.visits.length*C := by
  rw [BoxBlock.length_visits, Nat.mul_assoc]
  apply work_loop_le
  intro i hi
  change i < b.copies at hi
  rw [work_sequence]
  simp only [List.map_map]
  apply (sum_map_le b.factors.zipIdx _ C ?_).trans_eq (by simp)
  intro z hz
  have hi' := List.mem_zipIdx_iff_getElem?.mp hz
  have hzlt : z.2 < b.factors.length := by
    by_contra! hh
    simp [List.getElem?_eq_none_iff.mpr hh] at hi'
  have hzmem : z.1 ∈ b.factors := List.mem_of_getElem? hi'
  apply h
  · exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨z.1,hzmem,rfl⟩⟩
  · simp only [NatExpr.eval, List.getD_cons_zero, BoxBlock.length_visits]
    have hu : (i+1)*b.factors.length ≤ b.copies*b.factors.length := by gcongr; omega
    rw [Nat.succ_mul] at hu
    omega

/-- Aggregate any uniform per-occurrence work bound over the compact repeated-box sweep. -/
theorem sweep_work_le (body : FactorBody) (bs : List BoxBlock) (start : ℕ) (e : List ℕ) (C : ℕ)
    (h : ∀ f j off i env, (⟨f, off.eval env, i.eval env⟩ : Occurrence) ∈ bs.flatMap BoxBlock.visits →
      j.eval env < start + (bs.flatMap BoxBlock.visits).length → work (body f j off i) env ≤ C) :
    work (sweep body bs start) e ≤ (bs.flatMap BoxBlock.visits).length*C := by
  induction bs generalizing start with
  | nil => simp [sweep, work, Stmt.expand, stream]
  | cons b bs ih =>
    rw [sweep, work_seq, List.flatMap_cons, List.length_append, Nat.add_mul]
    apply Nat.add_le_add
    · apply b.fragment_work_le
      intro f j off i env hz hj
      apply h _ _ _ _ _ (List.mem_append_left _ hz)
      simp only [List.flatMap_cons, List.length_append]; omega
    · apply ih
      intro f j off i env hz hj
      apply h _ _ _ _ _ (List.mem_append_right _ hz)
      simp only [List.flatMap_cons, List.length_append, BoxBlock.length_visits]
      omega

/-- Bound a directory sweep by the privately expanded number of visited factors. -/
theorem Directory.sweep_work_le (D : Directory) (body : FactorBody) (e : List ℕ) (C : ℕ)
    (h : ∀ f j off i env, (⟨f, off.eval env, i.eval env⟩ : Occurrence) ∈ D.occurrences →
      j.eval env < D.visitCount → work (body f j off i) env ≤ C) :
    work (sweep body D.blocks 0) e ≤ D.visitCount*C := by
  rw [D.visitCount_eq, ← D.blocks_visits]
  apply BorderVNP.CellSparse.sweep_work_le
  simpa only [D.blocks_visits, Nat.zero_add, D.visitCount_eq] using h

/-- Physical span and table dimensions for every occurrence, prior to adding a scratch bank. -/
def Directory.BoxBounds (D : Directory) (M A : ℕ) : Prop :=
  ∀ o ∈ D.occurrences, o.factor.TableBound M ∧ o.factor.ReadBound o.offset o.copy A

/-- Expanded work of the sign/presence scan, charging both tests on each row. -/
theorem factorSweep_work_le (D : Directory) (aux : ℕ) (e : List ℕ) {M A : ℕ} (h : D.BoxBounds M A) :
    work (sweep (factorBody aux) D.blocks 0) e ≤ D.visitCount*(2*guardCost (aux+A) (factorNodeBound M)) := by
  apply D.sweep_work_le
  intro f j off i env hz _
  obtain ⟨ht,hr⟩ := h _ hz
  have hA := f.readBound_shift aux _ _ _ hr
  have hM := (f.tableBound_shift aux M).mpr ht
  let physical := NatExpr.add (.lit aux) off
  have h₁ := Term.work_guard_le _ env (factorPass_bounded physical i (f.shift aux) env hA)
    (factorPass_nodes_le physical i (f.shift aux) hM)
  have h₂ := Term.work_sign_le _ env (factorSign_bounded physical i (f.shift aux) env hA)
    (factorSign_nodes_le physical (f.shift aux) hM)
  rw [factorBody, work_seq]
  change _ ≤ 2*guardCost (aux+A) (factorNodeBound M)
  exact (Nat.add_le_add h₁ h₂).trans_eq (by simp [two_mul, guardCost])

/-- Expanded work of all gadget range checks. -/
theorem Directory.rangeGuard_work_le (D : Directory) (e : List ℕ) {M A : ℕ} (h : D.BoxBounds M A) :
    work D.rangeGuard e ≤ D.visitCount*guardCost A (factorNodeBound M) := by
  apply D.sweep_work_le
  intro f j off i env hz _
  obtain ⟨ht,hr⟩ := h _ hz
  exact Term.work_guard_le _ _ (rangeTerm_bounded _ off i f env hr) (rangeTerm_nodes_le _ off f ht)

/-- All candidate prefix flags and gadget selectors are charged for every original row. -/
theorem Gadget.steps_work_le (D : Directory) (cap aux id : ℕ) (e : List ℕ) {M A : ℕ}
    (h : D.BoxBounds M A)
    (ha : ∀ i ≤ D.visitCount, ∀ k ≤ cap, Prefix.address 0 cap i k ≤ aux + A) :
    work (sweep (stepBody cap aux id) D.blocks 0) e ≤
      D.visitCount*((cap+1)*guardCost (aux+A) (4*factorNodeBound M+19)) := by
  apply D.sweep_work_le
  intro f j off i env hz hj
  obtain ⟨ht,hr⟩ := h _ hz
  let physical := NatExpr.add (.lit aux) off
  have hn := factorSelect_nodes_le physical id (f.shift aux) ((f.tableBound_shift aux M).mpr ht)
  apply Prefix.stepGen_work_le _ _ _ _ _ _ _
  · exact factorSelect_bounded physical i id (f.shift aux) env (f.readBound_shift aux _ _ _ hr)
  · dsimp only [physical] at hn
    omega
  · exact fun k hk => ⟨ha _ hj.le k hk, ha _ hj k hk⟩

/-- Physical interpreter clock of the signed scan, including terminal dispatch. -/
theorem factorSweep_budget_le (D : Directory) (aux : ℕ) (e : List ℕ) {M A : ℕ} (h : D.BoxBounds M A) :
    budget ((sweep (factorBody aux) D.blocks 0).expand e) ≤
      5*(D.visitCount*(2*guardCost (aux+A) (factorNodeBound M)))+2 :=
  (budget_le _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (factorSweep_work_le D aux e h)) _)

/-- Physical interpreter clock of the range scan, including terminal dispatch. -/
theorem Directory.rangeGuard_budget_le (D : Directory) (e : List ℕ) {M A : ℕ} (h : D.BoxBounds M A) :
    budget (D.rangeGuard.expand e) ≤ 5*(D.visitCount*guardCost A (factorNodeBound M))+2 :=
  (budget_le _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (D.rangeGuard_work_le e h)) _)

end CellSparse

end BorderVNP
end Computability
end OAI
