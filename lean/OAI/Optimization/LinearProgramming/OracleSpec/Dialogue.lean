import OAI.Optimization.LinearProgramming.OracleSpec.BitStack
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding

/-! An oracle dialogue with one pure dispatch between each pair of consecutive oracle calls.
The finite machine stores the suspended state as first-order `Carry` data in a fixed encoding. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace Dialogue

variable {k : ℕ} {I : Type*} {C : Type*}

open ExactQuantumFactoring.BitStackProgram
open BitCode

def inputCode (ei : I → Word) (ec : C → Word) : I ⊕ (Bool × C) → Word
  | .inl i => false :: ei i
  | .inr (reply, carry) => true :: reply :: ec carry

def actionCode (ec : C → Word) : Bool ⊕ (Word × C) → Word
  | .inl b => [false, b]
  | .inr (packet, carry) => true :: (frame packet ++ ec carry)

/-- One work wire, one query/reply stack, and two temporary stacks for unframing. The
last of these is also the outer loop's continuation marker between calls. -/
structure Ports (k : ℕ) where
  slot : Fin 4 ↪ Fin k

namespace Ports

abbrev wire (d : Ports k) := d.slot 0
abbrev io (d : Ports k) := d.slot 1
abbrev tmp (d : Ports k) := d.slot 2
abbrev ctrl (d : Ports k) := d.slot 3

def store (d : Ports k) (w packet flag : Word) : Store (Fin k) := fun i =>
  if i = d.wire then w else if i = d.io then packet else if i = d.ctrl then flag else []

def mem (d : Ports k) (w packet flag buf : Word) (hist : Transcript) : Memory k :=
  ⟨d.store w packet flag, buf, hist⟩

@[simp] theorem read_wire (d : Ports k) (w a f : Word) : d.store w a f d.wire = w := by simp [store]
@[simp] theorem read_io (d : Ports k) (w a f : Word) : d.store w a f d.io = a := by
  simp [store, wire, io]
@[simp] theorem read_tmp (d : Ports k) (w a f : Word) : d.store w a f d.tmp = [] := by
  simp [store, wire, io, tmp, ctrl]
@[simp] theorem read_ctrl (d : Ports k) (w a f : Word) : d.store w a f d.ctrl = f := by
  simp [store, wire, io, ctrl]

@[simp] theorem write_wire (d : Ports k) (w a f v : Word) :
    Function.update (d.store w a f) d.wire v = d.store v a f := by
  funext i
  by_cases he : i = d.wire <;> simp [store, he]
@[simp] theorem write_io (d : Ports k) (w a f v : Word) :
    Function.update (d.store w a f) d.io v = d.store w v f := by
  funext i
  by_cases he : i = d.io
  · subst i; simp
  · simp [store, he]
@[simp] theorem write_ctrl (d : Ports k) (w a f v : Word) :
    Function.update (d.store w a f) d.ctrl v = d.store w a v := by
  funext i
  by_cases he : i = d.ctrl
  · subst i; simp
  · simp [store, he]

@[simp] theorem pop_wire (d : Ports k) (w a f b : Word) (h : Transcript) :
    (d.mem w a f b h).pop d.wire = d.mem w.tail a f b h := by simp [mem, Memory.pop]
@[simp] theorem pop_io (d : Ports k) (w a f b : Word) (h : Transcript) :
    (d.mem w a f b h).pop d.io = d.mem w a.tail f b h := by simp [mem, Memory.pop]
@[simp] theorem pop_ctrl (d : Ports k) (w a f b : Word) (h : Transcript) :
    (d.mem w a f b h).pop d.ctrl = d.mem w a f.tail b h := by simp [mem, Memory.pop]
@[simp] theorem push_wire (d : Ports k) (w a f b : Word) (h : Transcript) (x : Bool) :
    (d.mem w a f b h).push d.wire x = d.mem (x::w) a f b h := by simp [mem, Memory.push]
@[simp] theorem push_ctrl (d : Ports k) (w a f b : Word) (h : Transcript) (x : Bool) :
    (d.mem w a f b h).push d.ctrl x = d.mem w a (x::f) b h := by simp [mem, Memory.push]

/-- Read one bit from the oracle reply and prefix it to the continuation on the work wire. -/
def prependReply (d : Ports k) : BitCode k := .cases d.io .skip (.push d.wire false) (.push d.wire true)

theorem prependReply_exec (d : Ports k) (o : WordOracle) (w : Word) (b : Bool) (h : Transcript) :
    Executes d.io o d.prependReply (d.mem w [b] [] [] h) (d.mem (b::w) [] [] [] h) 2 := by
  have hp := Executes.push (answer := d.io) (o := o) (d.mem w [] [] [] h) d.wire b
  simp only [push_wire] at hp
  unfold prependReply
  cases b with
  | false => apply Executes.casesFalse (a := 1) (xs := []) (by simp [mem]); simpa using hp
  | true => apply Executes.casesTrue (a := 1) (xs := []) (by simp [mem]); simpa using hp

/-- Unframe a request, send only the request bytes, and retain the encoded continuation. -/
def nextStep (d : Ports k) : BitCode k :=
  .seq (ofBitStack (unquoteMove d.wire d.io d.tmp d.ctrl))
    (.seq (queryFromStack d.io) (.seq d.prependReply (.seq (.push d.wire true) (.push d.ctrl true))))

theorem nextStep_exec (d : Ports k) (reply : Transcript → Word → Bool) (packet carry : Word)
    (h : Transcript) :
    let b := reply h packet
    Executes d.io (fun hist q => [reply hist q]) d.nextStep (d.mem (frame packet ++ carry) [] [] [] h)
      (d.mem (true::b::carry) [] [true] [] ((packet,[b])::h)) (10*packet.length+13) := by
  let o : WordOracle := fun hist q => [reply hist q]
  let h' := (packet,[reply h packet]) :: h
  have split := unquoteMove_runs d.wire d.io d.tmp d.ctrl (by simp [wire, io]) (by simp [wire,tmp])
    (by simp [wire,ctrl]) (by simp [io,tmp]) (by simp [io,ctrl]) (by simp [tmp,ctrl])
    packet carry (d.store (frame packet ++ carry) [] [])
    (by simp [quoteBits_eq_frame]) (by simp) (by simp)
  have u := ofBitStack_exec split d.io o [] h
  simp only [read_io, List.append_nil, write_wire, write_io] at u
  have send := queryFromStack_exec d.io d.io o (d.mem carry packet [] [] h) rfl
  have send' : Executes d.io o (queryFromStack d.io) (d.mem carry packet [] [] h)
      (d.mem carry [reply h packet] [] [] h') (3*packet.length+3) := by
    simpa [mem, Memory.drained, Memory.receive, h', o, Nat.add_assoc] using send
  have prepend := d.prependReply_exec o carry (reply h packet) h'
  have pw := Executes.push (answer := d.io) (o := o) (d.mem (reply h packet::carry) [] [] [] h') d.wire true
  have pc := Executes.push (answer := d.io) (o := o) (d.mem (true::reply h packet::carry) [] [] [] h') d.ctrl true
  simp only [push_wire] at pw
  simp only [push_ctrl] at pc
  have complete := Executes.seq u (Executes.seq send' (Executes.seq prepend (Executes.seq pw pc)))
  rw [show 10*packet.length+13 = (7*packet.length+6) + ((3*packet.length+3)+(2+(1+1))) by omega]
  exact complete

/-- The flag written by `pureStep` selects final output or an adaptive query. -/
def body (d : Ports k) (pureStep : BitCode k) : BitCode k :=
  .seq pureStep (.cases d.wire .skip (drain d.wire) d.nextStep)

def loopCode (d : Ports k) (pureStep : BitCode k) : BitCode k := .loop d.ctrl .skip (d.body pureStep)

def code (d : Ports k) (pureStep : BitCode k) : BitCode k :=
  .seq (.push d.wire false) (.seq (.push d.ctrl true) (d.loopCode pureStep))

end Ports
end Dialogue
end OracleSpec
end LinearProgramming
end Optimization
end OAI
