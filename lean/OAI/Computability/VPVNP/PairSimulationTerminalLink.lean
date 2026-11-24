import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveStageOperands

/-!
# The fixed eleven-operand terminal controller for compressed pairs

The entry word zero starts the descriptor bootstrap unconditionally. Every
continuation returns the marker one and writes its worker ordinal and full
persistent word into the terminal header. Thus an ordinary zero returned by
a worker is a valid local cursor. An accepting worker advances to the next
worker with local state zero, except at the final vertex stage, where it
accepts the whole terminal program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM LiveProgram
open scoped Fin.CommRing

/-- The five successive workers in a compressed pair's terminal computation. -/
abbrev Stage := Fin 5
namespace Stage
/-- The worker that publishes the terminal header. -/
abbrev bootstrap : Stage := 0
/-- The worker that computes the prefix sums of final wire widths. -/
abbrev prefixRows : Stage := 1
/-- The worker that writes role tags and child rows for the selected layers. -/
abbrev traversalRows : Stage := 2
/-- The worker that chooses the final shared wire values. -/
abbrev sharedBits : Stage := 3
/-- The worker that processes the final vertices in increasing ordinal order. -/
abbrev vertices : Stage := 4
end Stage

/-- The stage entered after this worker accepts, if another worker remains. -/
def next (s : Stage) : Option Stage := if h : s.val+1 < 5 then some ⟨s.val+1,h⟩ else none

/-- Fixed worker bank, sharing the low registers and retaining the complete
eleven-word live pair ABI in each relocated instruction. -/
def registers (workers : Stage → PairTable) := Finset.univ.sup fun s => (workers s).regs

/-- Place a worker's registers in the common register bank. -/
def embedding (workers : Stage → PairTable) (s : Stage) : Fin (workers s).regs ↪ Fin (registers workers) :=
  ⟨fun i => i.castLE (Finset.le_sup (Finset.mem_univ s)), fun _ _ h => Fin.ext (congrArg (fun x : Fin (registers workers) => x.val) h)⟩

/-- Relocate a worker to the shared register bank, preserving its public operands. -/
def component (workers : Stage → PairTable) (s : Stage) :=
  LiveStageLink.widen (workers s).table (embedding workers s) id

/-- Control locations for entry, stage comparisons, worker bodies and return instructions. -/
abbrev Label (pcs : Stage → ℕ) :=
  Fin 17 ⊕ (Fin 6 ⊕ (Stage ⊕ (((s : Stage) × Fin (pcs s)) ⊕ (Stage ⊕ Fin 3))))

/-- Number of instructions after placing the five workers and their dispatch code. -/
def codeSize (pcs : Stage → ℕ) := 17+(6+(5+((∑ i,pcs i)+(5+3))))

/-- Number the controller and worker labels in their physical instruction order. -/
def labels (pcs : Stage → ℕ) : Label pcs ≃ Fin (codeSize pcs) :=
  ((Equiv.refl _).sumCongr (((Equiv.refl _).sumCongr (((Equiv.refl _).sumCongr
    ((finSigmaFinEquiv.sumCongr finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv

/-- Address of an instruction in the terminal entry sequence. -/
def enter (pcs : Stage → ℕ) (i : Fin 17) := labels pcs (.inl i)
/-- Address of a stage-tag load or the exhausted-scan rejection. -/
def scan (pcs : Stage → ℕ) (i : Fin 6) := labels pcs (.inr (.inl i))
/-- Address of the comparison that selects a particular worker. -/
def compare (pcs : Stage → ℕ) (s : Stage) := labels pcs (.inr (.inr (.inl s)))
/-- Physical address of an instruction in the selected worker. -/
def bodyPC (pcs : Stage → ℕ) (s : Stage) (i : Fin (pcs s)) := labels pcs (.inr (.inr (.inr (.inl ⟨s,i⟩))))
/-- Address of the instruction that stages a tag for the next call. -/
def storeTag (pcs : Stage → ℕ) (s : Stage) := labels pcs (.inr (.inr (.inr (.inr (.inl s)))))
/-- Address of a control-word write or the return to the host. -/
def save (pcs : Stage → ℕ) (i : Fin 3) := labels pcs (.inr (.inr (.inr (.inr (.inr i)))))

variable {r w : ℕ} {pcs : Stage → ℕ}

/-- Physical index of a register used by the worker. -/
abbrev ordinary (i : Fin r) : Fin (r+6) := i.castAdd 6
/-- Physical index of a register reserved by the terminal controller. -/
abbrev extra (r : ℕ) (i : Fin 6) : Fin (r+6) := i.natAdd r
/-- Register containing the address of the stage-tag cell. -/
abbrev phaseAddress (r : ℕ) := extra r 0
/-- Register containing the address of the saved worker state. -/
abbrev savedAddress (r : ℕ) := extra r 1
/-- Register holding the persistent word supplied to the worker. -/
abbrev stateValue (r : ℕ) := extra r 2
/-- Register holding the current or next stage tag. -/
abbrev phaseValue (r : ℕ) := extra r 3
/-- Register used in computing the header and comparing stage tags. -/
abbrev temporary (r : ℕ) := extra r 4
/-- Register containing the continuation marker one. -/
abbrev unitReg (r : ℕ) := extra r 5

/-- Values of the six controller registers while the worker executes. -/
def extras (addr state tag tmp : Word w) : Fin 6 → Word w := ![addr,addr+31,state,tag,tmp,1]

/-- Relocate the worker's current instruction and registers, retaining its private memory. -/
def bodyConfig (s : Stage) (host addr tag tmp : Word w) (c : Config w (pcs s) r) : Config w (codeSize pcs) (r+6) :=
  ⟨bodyPC pcs s c.pc,host,Fin.append c.reg (extras addr c.persistent tag tmp),c.privateMem⟩

/-- Address of the first of the 32 terminal-header words in the pair workspace. -/
def header (pub : Fin 11 → Word w) : Word w :=
  let radix := BinaryOp.shiftLeft.eval 1 (pub 7)
  pub 2 + radix*radix-32

/-- Machine-word representation of the stage ordinal. -/
def tagWord (w : ℕ) (s : Stage) : Word w := (s.val : Word w)

/-- Translate a worker instruction, including restoration of its state and handling of its exit. -/
def bodyInstr (s : Stage) : Instr w (pcs s) r 11 → Instr w (codeSize pcs) (r+6) 11
  | .constant a v j => .constant (ordinary a) v (bodyPC pcs s j)
  | .publicWord a i j => .publicWord (ordinary a) i (bodyPC pcs s j)
  | .stateWord a j => .copy (ordinary a) (stateValue r) (bodyPC pcs s j)
  | .copy a b j => .copy (ordinary a) (ordinary b) (bodyPC pcs s j)
  | .binary op a b c j => .binary op (ordinary a) (ordinary b) (ordinary c) (bodyPC pcs s j)
  | .loadPrivate a b j => .loadPrivate (ordinary a) (ordinary b) (bodyPC pcs s j)
  | .storePrivate a b j => .storePrivate (ordinary a) (ordinary b) (bodyPC pcs s j)
  | .jumpEq a b y n => .jumpEq (ordinary a) (ordinary b) (bodyPC pcs s y) (bodyPC pcs s n)
  | .jumpLt a b y n => .jumpLt (ordinary a) (ordinary b) (bodyPC pcs s y) (bodyPC pcs s n)
  | .choose y n => .choose (bodyPC pcs s y) (bodyPC pcs s n)
  | .readExternal a b j => .readExternal (ordinary a) (ordinary b) (bodyPC pcs s j)
  | .writeExternal a b j => .writeExternal (ordinary a) (ordinary b) (bodyPC pcs s j)
  | .returnState a => .copy (stateValue r) (ordinary a) (storeTag pcs s)
  | .reject => .reject
  | .accept => match next s with
    | none => .accept
    | some t => .constant (stateValue r) 0 (storeTag pcs t)

variable (T : (s : Stage) → Template (pcs s) r 11)

/-- A width sufficient for the controller literals and every worker literal. -/
def literalWidth := max 6 (Finset.univ.sup fun s => (T s).literalWidth)

/-- Compute header addresses, check the host marker and enter or resume the terminal program. -/
def enterInstr (W : ℕ) : Fin 17 → Instr W (codeSize pcs) (r+6) 11 :=
  ![.publicWord (phaseAddress r) 2 (enter pcs 1),.publicWord (phaseValue r) 7 (enter pcs 2),
    .constant (unitReg r) 1 (enter pcs 3),
    .binary .shiftLeft (temporary r) (unitReg r) (phaseValue r) (enter pcs 4),
    .binary .mul (temporary r) (temporary r) (temporary r) (enter pcs 5),
    .binary .add (phaseAddress r) (phaseAddress r) (temporary r) (enter pcs 6),
    .constant (temporary r) 32 (enter pcs 7),
    .binary .sub (phaseAddress r) (phaseAddress r) (temporary r) (enter pcs 8),
    .constant (temporary r) 31 (enter pcs 9),
    .binary .add (savedAddress r) (phaseAddress r) (temporary r) (enter pcs 10),
    .stateWord (temporary r) (enter pcs 11),
    .constant (stateValue r) 0 (enter pcs 12),
    .jumpEq (temporary r) (stateValue r) (bodyPC pcs 0 (T 0).entry) (enter pcs 13),
    .jumpEq (temporary r) (unitReg r) (enter pcs 14) (enter pcs 16),
    .readExternal (phaseValue r) (phaseAddress r) (enter pcs 15),
    .readExternal (stateValue r) (savedAddress r) (scan pcs 0),.reject]

/-- Write the stage and worker state, then return the host continuation marker. -/
def saveInstr (W : ℕ) : Fin 3 → Instr W (codeSize pcs) (r+6) 11 :=
  ![.writeExternal (phaseAddress r) (phaseValue r) (save pcs 1),
    .writeExternal (savedAddress r) (stateValue r) (save pcs 2), .returnState (unitReg r)]

/-- The instruction assigned to each physical controller or worker label. -/
def instruction : Label pcs → Instr (literalWidth T) (codeSize pcs) (r+6) 11
  | .inl i => enterInstr T _ i
  | .inr (.inl i) => if h : i.val < 5 then .constant (temporary r) (tagWord _ ⟨i.val,h⟩) (compare pcs ⟨i.val,h⟩) else .reject
  | .inr (.inr (.inl s)) => .jumpEq (phaseValue r) (temporary r) (bodyPC pcs s (T s).entry) (scan pcs s.succ)
  | .inr (.inr (.inr (.inl ⟨s,i⟩))) => bodyInstr s (((T s).code i).resize _)
  | .inr (.inr (.inr (.inr (.inl s)))) => .constant (phaseValue r) (tagWord _ s) (save pcs 0)
  | .inr (.inr (.inr (.inr (.inr i)))) => saveInstr _ i

/-- Static eleven-operand template linking the five relocated workers. -/
def linked : Template (codeSize pcs) (r+6) 11 where
  literalWidth := literalWidth T
  entry := enter pcs 0
  code j := instruction T ((labels pcs).symm j)

/-- Finite terminal table obtained from the supplied numerical worker tables. -/
def table (workers : Stage → PairTable) : PairTable :=
  ⟨_, _, linked (component workers)⟩

variable (pub : Fin 11 → Word w)

/-- Instantiate the terminal template at the host word width and public input. -/
abbrev machine := (linked T).instantiate w pub

private theorem width_ge : 6 ≤ literalWidth T := le_max_left _ _

@[simp] theorem code_enter (i : Fin 17) : (machine T pub).code (enter pcs i) = enterInstr T w i := by
  have h : 32 < 2^literalWidth T := (by decide : 32 < 2^6).trans_le (Nat.pow_le_pow_right (by decide) (width_ge T))
  simp only [machine,linked,Template.instantiate,enter,Equiv.symm_apply_apply,instruction]
  have one : 1 < 2^literalWidth T := by omega
  have thirty : 31 < 2^literalWidth T := by omega
  fin_cases i <;> first | rfl | (simp [enterInstr,Instr.resize,Nat.mod_eq_of_lt h,Nat.mod_eq_of_lt one,Nat.mod_eq_of_lt thirty])

private theorem tag_fits (s : Stage) : s.val < 2^literalWidth T :=
  s.isLt.trans ((by decide : 5 < 2^6).trans_le (Nat.pow_le_pow_right (by decide) (width_ge T)))

@[simp] theorem code_scan (s : Stage) : (machine T pub).code (scan pcs s.castSucc) =
    .constant (temporary r) (tagWord w s) (compare pcs s) := by
  simp [machine,linked,Template.instantiate,scan,instruction,s.isLt,tagWord,Instr.resize,Nat.mod_eq_of_lt (tag_fits T s)]

@[simp] theorem code_scan_end : (machine T pub).code (scan pcs (Fin.last 5)) = .reject := by
  simp [machine,linked,Template.instantiate,scan,instruction,Instr.resize]

@[simp] theorem code_compare (s : Stage) : (machine T pub).code (compare pcs s) =
    .jumpEq (phaseValue r) (temporary r) (bodyPC pcs s (T s).entry) (scan pcs s.succ) := by
  simp [machine,linked,Template.instantiate,compare,instruction,Instr.resize]

@[simp] theorem code_tag (s : Stage) : (machine T pub).code (storeTag pcs s) =
    .constant (phaseValue r) (tagWord w s) (save pcs 0) := by
  simp [machine,linked,Template.instantiate,storeTag,instruction,Instr.resize,tagWord,Nat.mod_eq_of_lt (tag_fits T s)]

@[simp] theorem code_save (i : Fin 3) : (machine T pub).code (save pcs i) = saveInstr w i := by
  simp only [machine,linked,Template.instantiate,save,Equiv.symm_apply_apply,instruction]
  fin_cases i <;> rfl

@[simp] theorem code_body (s : Stage) (i : Fin (pcs s)) :
    (machine T pub).code (bodyPC pcs s i) = bodyInstr s (((T s).instantiate w pub).code i) := by
  have le : (T s).literalWidth ≤ literalWidth T := (Finset.le_sup (f := fun s => (T s).literalWidth) (Finset.mem_univ s)).trans (le_max_right _ _)
  simp only [machine,linked,Template.instantiate,bodyPC,Equiv.symm_apply_apply,instruction]
  generalize (T s).code i = op
  have hc (a : Word (T s).literalWidth) : a.val < 2^literalWidth T :=
    a.isLt.trans_le (Nat.pow_le_pow_right (by decide) le)
  cases op <;> cases h : next s <;> simp [bodyInstr,Instr.resize,h,Nat.mod_eq_of_lt (hc _)]

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
