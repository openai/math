import OAI.Computability.VPVNP.RAMPrivateLog
import OAI.Computability.VPVNP.RAMWordBits
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype

/-!
# Finite bit-stack control for a private RAM write log

Parallel streams store the newest-first addresses, values, and one occupancy
bit per entry. The query stack itself sets the word width. Even width zero
therefore permits distinct entries. Bits visited during lookup are saved and
restored before return.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AddressLog

open BurstRAM BurstRAM.PrivateRAM

/-- Stack labels for a private write-log lookup, including the address, result, three log
streams, and five restoration stacks. -/
inductive Port where
  | query | out | keys | values | occupied | keySave | valueSave | querySave | countSave | resultSave
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Contents of the lookup stacks, with parallel streams for addresses, written values, and
entry marks. -/
structure Bank where
  /-- Bits of the query address. Its length determines how many bits to read per log word. -/
  q : List Bool
  /-- Output stack onto which the lookup restores the selected value. -/
  o : List Bool
  /-- Address words of the private write log in newest-first order. -/
  ks : List Bool
  /-- Written values in the same entry order as the address stream. -/
  vs : List Bool
  /-- One occupancy mark per log entry, including entries with zero-width words. -/
  marks : List Bool
  /-- Address bits saved in reverse order during the lookup. -/
  sk : List Bool
  /-- Written-value bits saved for restoration after the scan. -/
  sv : List Bool
  /-- Query bits temporarily removed while comparing an address. -/
  sq : List Bool
  /-- Occupancy marks removed from entries already visited. -/
  sm : List Bool
  /-- Bits of the selected value staged for transfer to the output. -/
  so : List Bool

/-- Select the bit stack of a lookup bank by its port. -/
def Bank.stacks (s : Bank) : Stacks Port
  | .query => s.q
  | .out => s.o
  | .keys => s.ks
  | .values => s.vs
  | .occupied => s.marks
  | .keySave => s.sk
  | .valueSave => s.sv
  | .querySave => s.sq
  | .countSave => s.sm
  | .resultSave => s.so

/-- Replace the bit stack at one lookup port. -/
def Bank.set (s : Bank) (p : Port) (x : List Bool) : Bank :=
  match p with
  | .query => {s with q := x}
  | .out => {s with o := x}
  | .keys => {s with ks := x}
  | .values => {s with vs := x}
  | .occupied => {s with marks := x}
  | .keySave => {s with sk := x}
  | .valueSave => {s with sv := x}
  | .querySave => {s with sq := x}
  | .countSave => {s with sm := x}
  | .resultSave => {s with so := x}

@[simp] theorem Bank.update_stacks (s : Bank) (p : Port) (x : List Bool) :
    Function.update s.stacks p x = (s.set p x).stacks := by
  funext k
  cases p <;> cases k <;> rfl

variable {w : ℕ}

/-- Store every key in increasing order of bit significance. -/
def keys (log : WriteLog w) : List Bool := log.flatMap fun e => wordBits e.1

/-- Concatenate the bit encodings of the written values in log order. -/
def values (log : WriteLog w) : List Bool := log.flatMap fun e => wordBits e.2

/-- Initialize lookup with the query, output tail, encoded write log, one mark per entry, and
empty restoration stacks. -/
def bank (a : Word w) (out : List Bool) (log : WriteLog w) : Bank :=
  ⟨wordBits a, out, keys log, values log, List.replicate log.length true, [], [], [], [], []⟩

/-- The common rewind loop specializes to each saved stream. -/
inductive Rewind where
  | query | keys | values | marks | result
  deriving DecidableEq

instance : Fintype Rewind := derive_fintype% _

/-- Finite lookup control for comparing keys, selecting a value or zero, and restoring the
scanned stacks. -/
inductive State where
  | record | saveMark
  | key (eq : Bool) | saveQ (eq b : Bool) | getK (eq b : Bool) | saveK (eq bit : Bool)
  | value (hit : Bool) | putQ (hit b : Bool) | getV (hit : Bool) | saveV (hit bit : Bool)
  | copyV (bit : Bool)
  | zero | saveZeroQ (bit : Bool) | emitZero
  | rewind (phase : Rewind) | put (phase : Rewind) (bit : Bool)
  | done | reject
  deriving DecidableEq, Fintype

/-- Scratch port holding the reversed bits for the current restoration pass. -/
def Rewind.src : Rewind → Port
  | .query => .querySave | .keys => .keySave | .values => .valueSave
  | .marks => .countSave | .result => .resultSave

/-- Port that receives the bits restored in the current pass. -/
def Rewind.dst : Rewind → Port
  | .query => .query | .keys => .keys | .values => .values
  | .marks => .occupied | .result => .out

/-- Advance through restoration of the query, keys, values, occupancy marks, and result, then
finish. -/
def Rewind.next : Rewind → State
  | .query => .rewind .keys | .keys => .rewind .values | .values => .rewind .marks
  | .marks => .rewind .result | .result => .done

/-- A load stops at the first matching full word. The key and value scans
both have width determined by the query, independently of its numeric value. -/
def loadCode : StackCode Port State
  | .record => .pop .occupied fun | none => .zero | some true => .saveMark | some false => .reject
  | .saveMark => .push .countSave true (.key true)
  | .key eq => .pop .query fun | none => .value eq | some b => .saveQ eq b
  | .saveQ eq b => .push .querySave b (.getK eq b)
  | .getK eq b => .pop .keys fun | none => .reject | some d => .saveK (eq && (b == d)) d
  | .saveK eq d => .push .keySave d (.key eq)
  | .value hit => .pop .querySave fun
    | none => if hit then .rewind .keys else .record
    | some b => .putQ hit b
  | .putQ hit b => .push .query b (.getV hit)
  | .getV hit => .pop .values fun | none => .reject | some v => .saveV hit v
  | .saveV hit v => .push .valueSave v (if hit then .copyV v else .value false)
  | .copyV v => .push .resultSave v (.value true)
  | .zero => .pop .query fun | none => .rewind .query | some b => .saveZeroQ b
  | .saveZeroQ b => .push .querySave b .emitZero
  | .emitZero => .push .resultSave false .zero
  | .rewind phase => .pop phase.src fun | none => phase.next | some b => .put phase b
  | .put phase b => .push phase.dst b (.rewind phase)
  | .done => .halt true
  | .reject => .halt false

/-- Elementary instruction proofs can be stated directly in terms of a bank. -/
theorem stepPush {Q : Type*} {code : StackCode Port Q} (s : Bank) {u v p b}
    (h : code u = .push p b v) :
    StackStep code u s.stacks v (s.set p (b :: s.stacks p)).stacks := by
  simpa only [Bank.update_stacks] using StackStep.push (s := s.stacks) h

theorem stepPop {Q : Type*} {code : StackCode Port Q} (s : Bank) {u p f}
    (h : code u = .pop p f) :
    StackStep code u s.stacks (f (s.stacks p).head?) (s.set p (s.stacks p).tail).stacks := by
  simpa only [Bank.update_stacks] using StackStep.pop (s := s.stacks) h

end RAMTape.AddressLog

end VPVNP
end Computability
end OAI
