import OAI.Computability.BorderVNP.DiagonalResidueRAMScan
import OAI.Computability.BorderVNP.RoutingISANatural
import OAI.Computability.BorderVNP.RoutingISABlockAppend
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Scattering routed and locally chosen bits to one physical packet

The selector and crossing words have separate read cursors. Every visited packet
position advances the write cursor, including unused reserved positions. Only a
private position issues a binary choice. The ordinary assembly trace, including
the old value observed at each store, is determined by these choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

/-- Origin of a bit in the owned part of the fixed packet reservation. -/
inductive Mode
  | selector | crossing | privateBit | unused
  deriving DecidableEq

/-- Realization of a position. A private position supplies exactly one Boolean choice. -/
inductive Digit
  | selector | crossing | privateBit (bit : Bool) | unused
  deriving DecidableEq

/-- Instruction kind determined before guessing a local bit. -/
def Digit.mode : Digit → Mode
  | .selector => .selector | .crossing => .crossing | .privateBit _ => .privateBit | .unused => .unused

/-- Ordered nondeterministic input consumed by this one instruction fragment. -/
def Digit.choices : Digit → List Bool
  | .privateBit b => [b] | _ => []

/-- The fixed code for one locally guessed bit once its branch is selected. -/
def writeLocal (b : Bool) : Code := .block [
  .constant 60 (if b then 1 else 0), .store 38 60, .binary .add 38 38 59]

/-- One physical source word is loaded at the source cursor and stored at the packet cursor. -/
def copyDigit (src : Reg) : Code := .block [
  .load 60 src, .store 38 60, .binary .add src src 59, .binary .add 38 38 59]

/-- Read cursors are 36 and 37, the destination cursor is 38, and 59 contains one. -/
def Mode.code : Mode → Code
  | .selector => copyDigit 36 | .crossing => copyDigit 37
  | .privateBit => .choose (writeLocal true) (writeLocal false)
  | .unused => .binary .add 38 38 59

/-- Symbolic result of the native opcodes, including chronological read and write events. -/
def Digit.step {w : ℕ} (d : Digit) (s : Bank w) (m : Memory w) : Effect w :=
  effect (match d with | .privateBit b => b | _ => false) s m d.mode.code

/-- Each selected digit has its actual physical execution. -/
theorem step_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (d : Digit) (s : Bank w) (m : Memory w) :
    Runs pub mac d.mode.code s m (d.step s m).trace (d.step s m).bank (d.step s m).mem := by
  apply effect_runs
  cases d <;> rfl

/-- Every returning single-slot execution is the realization of one matching digit. -/
theorem step_inv {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {k : Mode} {s : Bank w} {m es t mt} (run : Runs pub mac k.code s m es t mt) :
    ∃ d : Digit, d.mode = k ∧ es = (d.step s m).trace ∧ t = (d.step s m).bank ∧ mt = (d.step s m).mem := by
  cases k with
  | selector => exact ⟨.selector,rfl,run.unique_of_deterministic (by decide) (step_run _ _ .selector ..)⟩
  | crossing => exact ⟨.crossing,rfl,run.unique_of_deterministic (by decide) (step_run _ _ .crossing ..)⟩
  | unused => exact ⟨.unused,rfl,run.unique_of_deterministic (by decide) (step_run _ _ .unused ..)⟩
  | privateBit =>
    cases run with
    | atom ha _ _ => cases ha
    | choose bit body =>
      cases bit
      all_goals
        have equal := body.unique_of_deterministic (by decide)
          (effect_runs _ _ false s m _ (by decide))
        obtain ⟨rfl,rfl,rfl⟩ := equal
      · exact ⟨.privateBit false,rfl,rfl,rfl,rfl⟩
      · exact ⟨.privateBit true,rfl,rfl,rfl,rfl⟩

/-- A digit contributes at most four positive ordinary events. -/
theorem Digit.trace_spec {w : ℕ} (d : Digit) (s : Bank w) (m : Memory w) :
    let tr := (d.step s m).trace
    TraceOK tr d.choices tr.length ∧ tr.length ≤ 4 ∧ traceCost tr = tr.length := by
  cases d with
  | privateBit bit => cases bit <;> simp [Digit.step, Digit.mode, Digit.choices, Mode.code,
      writeLocal,Code.block,effect,TraceOK,choiceTick,tick,traceCost,VPVNP.RAMBuckets.cost,
      TeamTranscript.Action.extra]
  | _ => simp [Digit.step, Digit.mode, Digit.choices, Mode.code,copyDigit,Code.block,
      effect,TraceOK,tick,traceCost,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra]

/-- A fixed packet layout compiles into actual byte-ISA statements, one per reserved word. -/
def program : List Mode → Code
  | [] => .nop
  | a::as => .seq a.code (program as)

/-- Execution on the stream of locally chosen bits. -/
def result {w : ℕ} : List Digit → Bank w → Memory w → Effect w
  | [],s,m => ⟨s,m,[tick w]⟩
  | d::ds,s,m =>
    let head := d.step s m
    let tail := result ds head.bank head.mem
    {tail with trace := head.trace++tail.trace}

/-- Every local-choice assignment realizes a path with exactly the corresponding memory image. -/
theorem program_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (ds : List Digit) (s : Bank w) (m : Memory w) :
    Runs pub mac (program (ds.map Digit.mode)) s m (result ds s m).trace (result ds s m).bank
      (result ds s m).mem := by
  induction ds generalizing s m with
  | nil => exact Runs.localStep _ rfl rfl
  | cons d ds ih => exact (step_run _ _ _ _ _).seq (ih _ _)

/-- Conversely, every returning run determines the local bit assignment and its complete trace. -/
theorem program_run_inv {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (ks : List Mode) {s : Bank w} {m es t mt} (h : Runs pub mac (program ks) s m es t mt) :
    ∃ ds, ds.map Digit.mode = ks ∧ es = (result ds s m).trace ∧ t = (result ds s m).bank ∧
      mt = (result ds s m).mem := by
  induction ks generalizing s m es t mt with
  | nil => exact ⟨[],rfl,h.unique_of_deterministic (by decide) (program_run _ _ [] ..)⟩
  | cons k ks ih =>
    obtain ⟨_,_,_,_,he,h1,h2⟩ := Runs.seq_iff.mp h
    obtain ⟨d,hd,rfl,rfl,rfl⟩ := step_inv h1
    obtain ⟨ds,hs,rfl,rfl,rfl⟩ := ih h2
    exact ⟨d::ds,by simp [hd,hs],he,rfl,rfl⟩

/-- Native choices, sign, and word-operation cost of a packet layout with all reserved positions. -/
theorem result_trace {w : ℕ} (ds : List Digit) (s : Bank w) (m : Memory w) :
    let tr := (result ds s m).trace
    TraceOK tr (ds.flatMap Digit.choices) tr.length ∧ traceCost tr ≤ 4*ds.length+1 := by
  induction ds generalizing s m with
  | nil => simp [result,TraceOK,tick,traceCost,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra]
  | cons d ds ih =>
    obtain ⟨h₁,h₂,h₃⟩ := d.trace_spec s m
    obtain ⟨t₁,t₂⟩ := ih (d.step s m).bank (d.step s m).mem
    refine ⟨by simpa [result] using h₁.append t₁, ?_⟩
    simp only [result, traceCost, VPVNP.RAMBuckets.cost_append, List.length_cons]
    change traceCost (d.step s m).trace + traceCost _ ≤ _
    omega

/-- Once the fixed layout is known, the sequence of private choices distinguishes every realization. -/
theorem choices_injective {a b : List Digit} (hm : a.map Digit.mode = b.map Digit.mode)
    (hc : a.flatMap Digit.choices = b.flatMap Digit.choices) : a = b := by
  induction a generalizing b with
  | nil => simpa using hm.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at hm
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at hm
      obtain ⟨hh,ht⟩ := hm
      cases x <;> cases y <;> simp [Digit.mode] at hh <;>
        simp [Digit.choices] at hc <;> first
        | exact congrArg (List.cons _) (ih ht hc)
        | exact congrArg₂ List.cons (congrArg Digit.privateBit hc.1) (ih ht hc.2)

end Cube.Scatter

end BorderVNP
end Computability
end OAI
