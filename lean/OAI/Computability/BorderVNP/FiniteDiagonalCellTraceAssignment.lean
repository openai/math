import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceCompact
import OAI.Computability.BorderVNP.RoutingISAExternalBank
import OAI.Computability.BorderVNP.CellPrivateTranslate
import OAI.Computability.BorderVNP.CellDirectoryDepth
import OAI.Computability.BorderVNP.RoutingISACompactPacket

/-! # Private assignments in the native cell-checker trace

Private wire guesses form a fixed-length prefix of the consumed choice tape.
External bits are deterministic and consume no choice. After fixing the prefix,
the signed sum of the remaining checker leaves is precisely the sparse
directory entry at that wire assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.Compact

open VPVNP RAMTape BurstRAM RoutingISA RoutingISA.CompactMachine
open CellMacro CellMacro.Generator CellSparse
open private deterministic_run guess_decode setValues from OAI.Computability.BorderVNP.CellBytecode

/-- All successfully consumed bytecode tapes, with the Boolean terminal sign. -/
def instructionTraces (ops : List Op) (f : Flags) (v : List Bool) :=
  FieldReplay.leaves code CellMacro.negative (budget ops) (f,.fetch) (bank (stream ops) v [])

/-- A nonbranching opcode changes the flags and value stack without consuming a choice. -/
theorem deterministic (o : Op) (ho : o ≠ .guess) (ops : List Op) (f : Flags) (v : List Bool) :
    instructionTraces (o::ops) f v =
      instructionTraces ops (o.effect f v false).1 (o.effect f v false).2 := by
  obtain ⟨d,hd,run⟩ := deterministic_run o ho f (stream ops) v
  have h : budget ops ≤ budget (o::ops) - d := by simp [budget] at *; omega
  change FieldReplay.leaves code CellMacro.negative (budget (o::ops)) (f,.fetch)
    (bank (o.bits ++ stream ops) v []) = _
  rw [show budget (o::ops) = (budget (o::ops)-d)+d by simp [budget] at *; omega,FieldSelect.leaves_segment run]
  exact stableLeaves _ _ (CellMacro.execute ops _ _ _ le_rfl).1 h

private theorem literalPrefix (bits : List Bool) (ops : List Op) (f : Flags) (v : List Bool) :
    instructionTraces (bits.map Op.literal ++ ops) f v = instructionTraces ops f (bits.reverse ++ v) := by
  induction bits generalizing v with
  | nil => rfl
  | cons b bits ih =>
    rw [List.map_cons,List.cons_append,deterministic (.literal b) (by intro h; cases h)]
    simpa [Op.effect] using ih (b::v)

/-- A genuine guess consumes one leading bit and pushes precisely that bit. -/
theorem guess (ops : List Op) (f : Flags) (v : List Bool) (bs : List Bool) (sg : Bool) :
    (bs,sg) ∈ instructionTraces (.guess::ops) f v ↔
      ∃ b tail, bs = b::tail ∧ (tail,sg) ∈ instructionTraces ops f (b::v) := by
  let n := budget ops
  have h : budget (.guess::ops) = (n+1+1)+2 := by simp [n,budget,Op.ticks]; omega
  change (bs,sg) ∈ FieldReplay.leaves code CellMacro.negative _ (f,.fetch)
    (bank (Op.guess.bits ++ stream ops) v []) ↔ _
  rw [h,FieldSelect.leaves_segment (guess_decode f (stream ops) v)]
  rw [FieldReplay.mem_choose_iff _ _ _ _ _ _ _ (show code (f,.choose) = _ from rfl)]
  simp only [FieldReplay.leaves,code,setValues]
  cases bs with
  | nil => simp
  | cons b bs => cases b <;> simp [instructionTraces,n,bank]

/-- The first bits in chronological order are exactly the private wire bits in
reverse address order. Every remaining bit belongs to the sparse validator. -/
theorem guess_prefix (k : ℕ) (ops : List Op) (f : Flags) (v bs : List Bool) (sg : Bool) :
    (bs,sg) ∈ instructionTraces (List.replicate k .guess ++ ops) f v ↔
      k ≤ bs.length ∧ (bs.drop k,sg) ∈ instructionTraces ops f ((bs.take k).reverse ++ v) := by
  induction k generalizing v bs with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,guess]
    cases bs with
    | nil => simp
    | cons b bs => simp [ih,List.reverse_cons,List.append_assoc]

/-- The directory's traces conditioned on one particular wire assignment.
Its temporary guesses are still ordinary native choice tapes. -/
def assignmentTails (D : Directory) (e : List ℕ) (wires external : List Bool) :=
  instructionTraces (D.checkAssignment.expand e) ⟨true,false⟩ (wires ++ external)

private theorem program_eq (D : Directory) (k : ℕ) (e : List ℕ) :
    (D.program k).expand e = List.replicate k .guess ++ D.checkAssignment.expand e := by
  simp [Directory.program,Stmt.expand,NatExpr.eval,List.flatMap_def,List.map_const']

/-- Decode the true private-wire assignment and the exact remaining choice
tape from a successful trace of the fully seeded directory. -/
theorem directory_prefix (D : Directory) (k : ℕ) (external : List Bool) (e : List ℕ)
    (bs : List Bool) (sg : Bool) :
    (bs,sg) ∈ instructionTraces ((withExternal external (D.program k)).expand e) ⟨true,false⟩ [] ↔
      k ≤ bs.length ∧ (bs.drop k,sg) ∈ assignmentTails D e (bs.take k).reverse external := by
  rw [withExternal,expand_push,literalPrefix,List.reverse_reverse,List.append_nil,program_eq,guess_prefix]
  rfl

/-- Every returning native tape in the physical checker has the advertised
wire prefix and exactly one chronological residual tape. The converse
constructs a true private call trace for every such residual tape. -/
theorem native_assignment_iff {w : ℕ} (gen : Fragment IO) (n : ℕ) (hw : 0 < w)
    (payload : List Bool) (D : Directory) (k : ℕ) (external : List Bool) (e : List ℕ) {genCost : ℕ}
    (compiled : gen.Runs genCost (io payload [] [])
      (io [] [] (stream ((withExternal external (D.program k)).expand e)).reverse))
    (time : let ops := (withExternal external (D.program k)).expand e
      2*(3*((CompactFrame.pack w payload).length*w)+genCost+(2*(stream ops).length+1)+budget ops) ≤ n^25)
    (bs : List Bool) (sg : Bool) :
    (bs,TeamPrivateCall.sign (some sg)) ∈ choices gen n (CompactFrame.pack w payload) ↔
      k ≤ bs.length ∧ (bs.drop k,sg) ∈ assignmentTails D e (bs.take k).reverse external := by
  rw [packed_choices_iff gen n hw payload _ compiled time]
  exact directory_prefix D k external e bs sg

/-- A prescribed assignment and residual checker tape encode a unique full
native tape, including the order in which guessed wires are pushed onto the stack. -/
theorem native_assignment_encode {w : ℕ} (gen : Fragment IO) (n : ℕ) (hw : 0 < w)
    (payload : List Bool) (D : Directory) {k : ℕ} (external : List Bool) (e : List ℕ) {genCost : ℕ}
    (compiled : gen.Runs genCost (io payload [] [])
      (io [] [] (stream ((withExternal external (D.program k)).expand e)).reverse))
    (time : let ops := (withExternal external (D.program k)).expand e
      2*(3*((CompactFrame.pack w payload).length*w)+genCost+(2*(stream ops).length+1)+budget ops) ≤ n^25)
    (x : Fin k → Bool) (tail : List Bool) (sg : Bool) :
    ((List.ofFn x).reverse ++ tail,TeamPrivateCall.sign (some sg)) ∈ choices gen n (CompactFrame.pack w payload) ↔
      (tail,sg) ∈ assignmentTails D e (List.ofFn x) external := by
  rw [native_assignment_iff gen n hw payload D k external e compiled time]
  have hlen : (List.ofFn x).reverse.length = k := by simp
  have hd : ((List.ofFn x).reverse ++ tail).drop k = tail := by
    simpa only [hlen] using (List.drop_left (l₁ := (List.ofFn x).reverse) (l₂ := tail))
  have ht : ((List.ofFn x).reverse ++ tail).take k = (List.ofFn x).reverse := by
    simpa only [hlen] using (List.take_left (l₁ := (List.ofFn x).reverse) (l₂ := tail))
  simp [hd,ht]

/-- Native choices of the fixed typed directory translator and evaluator, with
the metadata parser, literal seeding and clock of the actual library slot. -/
theorem typed_native_assignment {w n : ℕ} (D : Directory) (k : ℕ) (external : List Bool)
    (width : 0 < w) (profile : D.ProfileWidths)
    (time : let payload := Packet.input D k external
      let ops := (withExternal external (D.program k)).expand []
      2*(3*((CompactFrame.pack w payload).length*w)+
        CompactPacket.generationCost 8 (Packet.bits D k) external (D.program k) (CellPrivate.translateClock D k)+
        (2*(stream ops).length+1)+budget ops) ≤ n^25)
    (x : Fin k → Bool) (tail : List Bool) (sg : Bool) :
    ((List.ofFn x).reverse ++ tail,TeamPrivateCall.sign (some sg)) ∈
      choices (CompactPacket.driver CellPrivate.translate 8 3) n (CompactFrame.pack w (Packet.input D k external)) ↔
      (tail,sg) ∈ assignmentTails D [] (List.ofFn x) external := by
  obtain ⟨t,ht,translation⟩ := CellPrivate.translate_run D k external profile
  obtain ⟨cost,hc,run⟩ := CompactPacket.driver_run CellPrivate.translate 8 3 (Packet.bits D k)
    external (D.program k) (D.program_fitsDepth k) translation
  apply native_assignment_encode _ n width _ D external [] run _ x tail sg
  dsimp only [Packet.input,CompactPacket.generationCost] at time hc ⊢
  omega

private theorem signedSum {K Q : Type} [DecidableEq K] (C : StackCode K Q) (neg : Q → Bool)
    (t : ℕ) (q : Q) (s : Stacks K) :
    (∑ p ∈ FieldReplay.leaves C neg t q s, TeamTape.haltWeight true p.2) = TeamStack.paths C neg t q s := by
  induction t generalizing q s with
  | zero => simp [TeamStack.paths,FieldReplay.leaves]
  | succ t ih =>
    cases h : C q with
    | choose l r =>
      simp only [TeamStack.paths,FieldReplay.leaves,h,Finset.sum_disjUnion,Finset.sum_map]
      exact congrArg₂ (·+·) (ih l s) (ih r s)
    | halt a => cases a <;> simp [TeamStack.paths,FieldReplay.leaves,h,TeamTape.haltWeight]
    | _ => simp [TeamStack.paths,FieldReplay.leaves,h,ih]

/-- Summing actual residual native paths for one fixed wire assignment gives
its signed directory weight. Distinct wire assignments are separated before
any sum over the auxiliary checker choices. -/
theorem assignmentTails_sum (D : Directory) (e : List ℕ) (wires external : List Bool) :
    (∑ p ∈ assignmentTails D e wires external, TeamTape.haltWeight true p.2) =
      D.weight (lookup (wires ++ external)) := by
  rw [assignmentTails,instructionTraces,signedSum,(CellMacro.execute _ _ _ _ le_rfl).2,D.value_checkAssignment]
  simp [TeamTape.haltWeight]

end FiniteDiagonal.CellTrace.Compact

end BorderVNP
end Computability
end OAI
