import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete

/-!
# The native live-mode dispatch of Section 14.1

Processor zero supplies the mode at each nonempty incident cut in header
slots 2 and 3. A boundary group reads its one incident mode. An interior
group rejects unequal modes. The result tag selects the unit check, the
primed pair, or the evaluator tail.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

namespace Mode

/-- The three live continuations selected by cut-mode agreement and group phase. -/
inductive Tag | unit | pair | tail deriving DecidableEq

/-- Encode the unit, pair, and evaluator-tail continuations as machine tags zero, one, and two. -/
def Tag.code : Tag → Word 2
  | .unit => 0
  | .pair => 1
  | .tail => 2

/-- Choose unit mode for a cleared mode bit, otherwise select pair or evaluator tail according
to the group half. -/
def selectTag (mode first : Bool) : Tag :=
  if mode then (if first then .pair else .tail) else .unit

/-- Both-empty is outside the chain domain and is rejected. -/
def selected (left right : ℕ) (incoming outgoing first : Bool) : Option Tag :=
  if left = 0 then
    if right = 0 then none else some (selectTag outgoing first)
  else if right = 0 ∨ incoming = outgoing then some (selectTag incoming first) else none

private abbrev Code := Flow 48 16

/-- Public words 0 through 3 give the scratch addresses of the left and
right lengths, first-half flag and output tag. The packed site header is at
address zero. Registers 10 and 11 receive its two mode bits. -/
private def prepare : Code := Opcodes.sequence (Opcodes.set 0 0)
  [Opcodes.set 1 1, Opcodes.set 2 2, Opcodes.set 3 3,
   Opcodes.load 4 0, Opcodes.read 5 4, Opcodes.load 4 1, Opcodes.read 6 4,
   Opcodes.load 4 2, Opcodes.read 7 4, Opcodes.load 8 3, Opcodes.read 9 0,
   Opcodes.bin .shiftRight 10 9 2, Opcodes.bin .bitAnd 10 10 1,
   Opcodes.bin .shiftRight 11 9 3, Opcodes.bin .bitAnd 11 11 1]

/-- Select a mode in register 12, checking nonemptiness and agreement. -/
private def chooseMode : Code :=
  .ifEq 5 0
    (.seq (.line (.guardLt 0 6)) (.line (.copy 12 11)))
    (.ifEq 6 0 (.line (.copy 12 10)) (.seq (.line (.guardEq 10 11)) (.line (.copy 12 10))))

/-- The chosen tag goes into register 13 and the designated scratch word. -/
private def emitTag : Code := .seq
  (.ifEq 12 0 (Opcodes.set 13 0) (.ifEq 7 0 (Opcodes.set 13 2) (Opcodes.set 13 1)))
  (Opcodes.write 8 13)

/-- The native routine that checks the applicable incident mode bits and publishes the
resulting continuation tag. -/
def program : Flow 48 16 := .seq prepare (.seq chooseMode emitTag)

/-- The instruction list and register count are independent of the chain length. -/
theorem program_length : program.length = 29 := by decide

private def simple {r k : ℕ} : Flow r k → Prop
  | .line _ => True
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b => simple a ∧ simple b
  | .branch .. | .whileLt .. => False

/-- A successful derivation of a deterministic acyclic block must be the
one computed by the straight-line interpreter. -/
private theorem once_of_exec {w r k : ℕ} {pub : Fin k → Word w} {state : Word w} {a : Flow r k}
    {rs rs' : Regs w r} {m m' : Memory w} {es : List (Event w)}
    (h : Flow.Exec pub state a rs m es rs' m') (hs : simple a) :
    Flow.once pub state false a rs m = some (es, rs', m') := by
  induction h with
  | line he => simp [Flow.once, he]
  | seq h₁ h₂ ih₁ ih₂ => simp [Flow.once, ih₁ hs.1, ih₂ hs.2]
  | ifEqYes ht hb ih | ifLtYes ht hb ih => simp [Flow.once, ht, ih hs.1]; rfl
  | ifEqNo ht hb ih | ifLtNo ht hb ih => simp [Flow.once, ht, ih hs.2]; rfl
  | branchYes | branchNo | whileDone | whileStep => contradiction

private theorem program_simple : simple program := by
  simp [program, prepare, chooseMode, emitTag, Opcodes.sequence, Opcodes.set, Opcodes.load, Opcodes.read,
    Opcodes.write, Opcodes.line, Opcodes.bin, simple]

variable {w : ℕ} (pub : Fin 16 → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)

private def before (h : Word w) : List (Event w) :=
  [.tick, .tick, .tick, .tick, .tick, .read (pub 0) (m (pub 0).val), .tick,
   .read (pub 1) (m (pub 1).val), .tick, .read (pub 2) (m (pub 2).val), .tick, .read 0 h,
   .tick, .tick, .tick, .tick]

private def prepared (h l r : Word w) : Regs w 48 := by
  let a := Function.update (Function.update (Function.update (Function.update rs (0 : Fin 48) 0) 1 1) 2 2) 3 3
  let b := Function.update (Function.update a (4 : Fin 48) (pub 0)) 5 (m (pub 0).val)
  let c := Function.update (Function.update b (4 : Fin 48) (pub 1)) 6 (m (pub 1).val)
  let d := Function.update (Function.update c (4 : Fin 48) (pub 2)) 7 (m (pub 2).val)
  exact Function.update (Function.update (Function.update (Function.update d (8 : Fin 48) (pub 3)) 9 h) 10 l) 11 r

set_option maxHeartbeats 2000000 in
private theorem once_prepare (hw : 4 ≤ w) (header : ProcessorInput.Header)
    (hh : m 0 = ProcessorInput.headerWord hw header) :
    Flow.once pub state false prepare rs m = some (before pub m (ProcessorInput.headerWord hw header),
      prepared pub rs m (ProcessorInput.headerWord hw header)
        (encodeBit w (header 2)) (encodeBit w (header 3)), m) := by
  have h₂ := extract_packed_bit hw header (2 : Fin 4)
  have h₃ := extract_packed_bit hw header (3 : Fin 4)
  change BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval _ 2) 1 = _ at h₂
  change BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval _ 3) 1 = _ at h₃
  simp (config := { decide := true }) [prepare, Opcodes.sequence, Opcodes.set, Opcodes.load,
    Opcodes.bin, Opcodes.read, Opcodes.line, Flow.once, Op.effect, Function.update, before, hh, h₂, h₃]
  rfl

private def activeBit (left right : ℕ) (incoming outgoing : Bool) : Option Bool :=
  if left = 0 then (if right = 0 then none else some outgoing)
  else if right = 0 ∨ incoming = outgoing then some incoming else none

private def chooseTicks (left right : ℕ) : ℕ := if left = 0 ∨ right = 0 then 3 else 4

private theorem choose_once (hw : 4 ≤ w) (left right : Word w) (incoming outgoing : Bool)
    (h0 : rs 0 = 0) (h5 : rs 5 = left) (h6 : rs 6 = right)
    (h10 : rs 10 = encodeBit w incoming) (h11 : rs 11 = encodeBit w outgoing) :
    Flow.once pub state false chooseMode rs m = (activeBit left.val right.val incoming outgoing).map
      (fun b => (List.replicate (chooseTicks left.val right.val) .tick, Function.update rs 12 (encodeBit w b), m)) := by
  have hone : (1 : Word w) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (show w ≠ 0 by omega))] at hv
  cases incoming <;> cases outgoing <;> by_cases hl : left = 0 <;> by_cases hr : right = 0 <;>
    simp (config := { decide := true }) [chooseMode, Flow.once, Op.effect, h0, h5, h6, h10, h11,
      activeBit, chooseTicks, Fin.pos_iff_ne_zero', Fin.val_eq_zero_iff, hl, hr, encodeBit, hone, Ne.symm hone]
  all_goals rfl

private theorem emit_once (hw : 4 ≤ w) (mode first : Bool) (h0 : rs 0 = 0)
    (h7 : rs 7 = encodeBit w first) (h12 : rs 12 = encodeBit w mode) :
    let value := Fin.ofNat (2 ^ w) (selectTag mode first).code.val
    Flow.once pub state false emitTag rs m =
      some (List.replicate (if mode then 3 else 2) .tick ++ [.write (rs 8) value],
        Function.update rs 13 value, writeMemory m (rs 8) value) := by
  have hone : (1 : Word w) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (show w ≠ 0 by omega))] at hv
  cases mode <;> cases first <;>
    simp (config := { decide := true }) [emitTag, Flow.once, Opcodes.set, Opcodes.write, Opcodes.line,
      Op.effect, selectTag, Tag.code, h0, h7, h12, encodeBit, hone]
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- The trace has four reads, one tag write, and no nondeterministic choices.
Its length is at most 24, including both comparison tests at an interior cut. -/
private def events (header : Word w) (left right : ℕ) (mode : Bool) (value : Word w) :=
  before pub m header ++ (List.replicate (chooseTicks left right) .tick ++
    (List.replicate (if mode then 3 else 2) .tick ++ [.write (pub 3) value]))

private theorem once_program (hw : 4 ≤ w) (header : ProcessorInput.Header) (first : Bool)
    (hh : m 0 = ProcessorInput.headerWord hw header) (hf : m (pub 2).val = encodeBit w first) :
    let l := m (pub 0).val
    let r := m (pub 1).val
    let R := prepared pub rs m (ProcessorInput.headerWord hw header) (encodeBit w (header 2)) (encodeBit w (header 3))
    Flow.once pub state false program rs m = (activeBit l.val r.val (header 2) (header 3)).map
      (fun b =>
        let v := Fin.ofNat (2 ^ w) (selectTag b first).code.val
        (events pub m (ProcessorInput.headerWord hw header) l.val r.val b v,
          Function.update (Function.update R 12 (encodeBit w b)) 13 v, writeMemory m (pub 3) v)) := by
  intro l r R
  have hc := choose_once pub state R m hw l r (header 2) (header 3) rfl rfl rfl rfl rfl
  simp only [program, Flow.once, once_prepare pub state rs m hw header hh]
  change (do
      let (eb,rb,mb) ← (do
        let (ec,rc,mc) ← Flow.once pub state false chooseMode R m
        let (ed,rd,md) ← Flow.once pub state false emitTag rc mc
        pure (ec ++ ed,rd,md))
      pure (before pub m (ProcessorInput.headerWord hw header) ++ eb,rb,mb)) = _
  rw [hc]
  cases he : activeBit l.val r.val (header 2) (header 3) with
  | none => rfl
  | some b =>
    simp only [Option.map_some, bind, Option.bind_some]
    have hu : (Function.update R (12 : Fin 48) (encodeBit w b)) 7 = encodeBit w first := hf
    rw [emit_once pub state _ m hw b first rfl hu (Function.update_self ..)]
    rfl

private theorem selected_eq_map (l r : ℕ) (a b first : Bool) :
    selected l r a b first = (activeBit l r a b).map (fun bit => selectTag bit first) := by
  simp only [selected, activeBit]
  split_ifs <;> rfl

private theorem events_bounds (h : Word w) (l r : ℕ) (b : Bool) (v : Word w) :
    (events pub m h l r b v).length ≤ 24 ∧ countProbes (events pub m h l r b v) = 5 ∧
      choiceBits (events pub m h l r b v) = [] ∧ after m (events pub m h l r b v) = writeMemory m (pub 3) v := by
  cases b <;> by_cases hz : l = 0 ∨ r = 0 <;>
    simp [events, before, chooseTicks, hz, countProbes, choiceBits, after, update]

/-- The executable mode block reads the packed word and dispatches to its
unique tag in at most 24 events and exactly five probes. -/
theorem exec_selected (hw : 4 ≤ w) (header : ProcessorInput.Header) (first : Bool) (tag : Tag)
    (hh : m 0 = ProcessorInput.headerWord hw header) (hf : m (pub 2).val = encodeBit w first)
    (hsel : selected (m (pub 0).val).val (m (pub 1).val).val (header 2) (header 3) first = some tag) :
    let v := Fin.ofNat (2 ^ w) tag.code.val
    ∃ es rs', Flow.Exec pub state program rs m es rs' (writeMemory m (pub 3) v) ∧ rs' 13 = v ∧
      es.length ≤ 24 ∧ countProbes es = 5 ∧ choiceBits es = [] ∧ after m es = writeMemory m (pub 3) v := by
  rw [selected_eq_map] at hsel
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hsel
  let v := Fin.ofNat (2 ^ w) (selectTag b first).code.val
  have ho := once_program pub state rs m hw header first hh hf
  simp only [hb, Option.map_some] at ho
  exact ⟨_, _, (Flow.once_sound pub state false program rs m ho).1, Function.update_self ..,
    events_bounds pub m _ _ _ b v⟩

/-- A correctly selected tag is written by the compiled standalone call.
The normal exit hands control to the next stage of a linked live program. -/
theorem native_selected (hw : 4 ≤ w) (header : ProcessorInput.Header) (first : Bool) (tag : Tag)
    (hh : m 0 = ProcessorInput.headerWord hw header) (hf : m (pub 2).val = encodeBit w first)
    (hsel : selected (m (pub 0).val).val (m (pub 1).val).val (header 2) (header 3) first = some tag) :
    let v := Fin.ofNat (2 ^ w) tag.code.val
    let machine := (program.template none).instantiate w pub
    ∃ es, execute machine.program 25 (machine.program.start state) m [] = some ⟨es, none⟩ ∧
      es.length ≤ 24 ∧ countProbes es = 5 ∧ choiceBits es = [] ∧ after m es = writeMemory m (pub 3) v := by
  obtain ⟨es, rs', he, _, ht, hp, hb, hm⟩ := exec_selected pub state (fun _ => 0) m hw header first tag hh hf hsel
  exact ⟨es, (Flow.template_execute_iff program none pub state (fun _ => 0) (fun _ => 0) m 25 [] _).mpr
    ⟨rs', _, he, rfl, Nat.lt_succ_of_le ht, hb⟩, ht, hp, hb, hm⟩

/-- Unequal modes on two nonempty cuts, or two absent cuts, reject at every
fuel bound and for every supplied list of choices. -/
theorem native_rejected (hw : 4 ≤ w) (header : ProcessorInput.Header) (first : Bool)
    (hh : m 0 = ProcessorInput.headerWord hw header) (hf : m (pub 2).val = encodeBit w first)
    (hsel : selected (m (pub 0).val).val (m (pub 1).val).val (header 2) (header 3) first = none)
    (fuel : ℕ) (bits : List Bool) :
    let machine := (program.template none).instantiate w pub
    execute machine.program fuel (machine.program.start state) m bits = none := by
  rw [selected_eq_map, Option.map_eq_none_iff] at hsel
  have ho := once_program pub state (fun _ => 0) m hw header first hh hf
  simp only [hsel, Option.map_none] at ho
  dsimp only
  cases he : execute _ _ _ _ _ with
  | none => rfl
  | some out =>
    obtain ⟨rs', m', hr, _⟩ := (Flow.template_execute_iff program none pub state (fun _ => 0)
      (fun _ => 0) m fuel bits out).mp he
    rw [once_of_exec hr program_simple] at ho
    contradiction

end Mode
end LiveHeader

end VPVNP
end Computability
end OAI
