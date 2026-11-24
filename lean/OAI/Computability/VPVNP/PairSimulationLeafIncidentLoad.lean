import OAI.Computability.VPVNP.PairSimulationLeafFieldCopy
import OAI.Computability.VPVNP.CursorInitialCheck

/-!
# Loading a selected incident field from the four resident cursor arcs

The direction and selected arc are finite control. The source offset, length,
four half-buffer bases and descending destination cursor are runtime words.
An endpoint selects the zero source. The local program never consults a
global wire assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentLoad

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorNetwork CursorRouting RAMLayout
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {bits w D H p r k : ℕ}

/-- First five operands are shared with the descending field mover, then
length, arc offset, and the two outgoing and two incoming buffer bases. -/
def baseReg : LocalPort → Fin 11
  | .outgoing false => 7
  | .outgoing true => 8
  | .incoming false => 9
  | .incoming true => 10

/-- Registers of the field mover inside the incident-loader register file. -/
def copyRegs (reg : Fin 11 ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 6).trans reg

/-- Select resident input for an available port and zeros at a missing endpoint. -/
def mode : Option LocalPort → LeafFieldCopy.Source
  | none => .zero
  | some _ => .resident

/-- Private address of a field within its half-wire buffer. -/
def sourceAddress (base : LocalPort → ℕ) (offset : ℕ) : Option LocalPort → ℕ
  | none => 0
  | some port => base port+offset

/-- The two address setup rows followed by the five-row move loop. -/
def prepare (port : Option LocalPort) (pc : Fin 2 → Fin p) (reg : Fin 11 ↪ Fin r) (copy : Fin p) :
    Fin 2 → Instr bits p r k :=
  ![(match port with
     | none => .constant (reg 0) 0 (pc 1)
     | some a => .binary .add (reg 0) (reg (baseReg a)) (reg 6) (pc 1)),
    .binary .sub (reg 1) (reg 2) (reg 5) copy]

theorem resize_prepare (port : Option LocalPort) (pc : Fin 2 → Fin p) (reg : Fin 11 ↪ Fin r)
    (copy : Fin p) (i : Fin 2) :
    (prepare (bits := 1) (k := k) port pc reg copy i).resize bits = prepare port pc reg copy i := by
  cases port <;> fin_cases i <;> rfl

/-- All four resident half-wire arrays encode their declared bits. -/
def Stored (base : LocalPort → ℕ) (buf : Buffers D H w) (m : Word bits → Word bits) :=
  ∀ port i, m (word bits (base port+i.val)) = PrivateFields.bitValue bits (buf port i)

/-- The selected consecutive bits of one port, or zeros when that port is absent. -/
def Field (port : Option LocalPort) (offset : ℕ) (n : ℕ)
    (fit : offset+n ≤ ramPayloadWidth D H w) (buf : Buffers D H w) : List Bool :=
  List.ofFn fun i : Fin n => match port with
    | none => false
    | some a => buf a ⟨offset+i.val, by have := i.isLt; omega⟩

@[simp] theorem length_field (port : Option LocalPort) (offset n : ℕ) (fit) (buf : Buffers D H w) :
    (Field port offset n fit buf).length = n := List.length_ofFn

theorem place_append (lo : ℕ) (xs ys : List Bool) (m : Word bits → Word bits) :
    LeafFieldCopy.place lo (xs++ys) m =
      LeafFieldCopy.place lo ys (LeafFieldCopy.place (lo+ys.length) xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => simp [LeafFieldCopy.place, ih, Nat.add_assoc, Nat.add_comm xs.length ys.length]

/-- State and continuation of a completed native field copy. -/
structure Result (reg : Fin 11 ↪ Fin r) (done : Fin p) (c out : Config bits p r)
    (lo : ℕ) (bs : List Bool) : Prop where
  pc : out.pc = done
  cursor : out.reg (reg 2) = word bits lo
  frame : ∀ i, i ≠ reg 0 → i ≠ reg 1 → i ≠ reg 2 → i ≠ reg 4 → out.reg i = c.reg i
  mem : out.privateMem = LeafFieldCopy.place lo bs c.privateMem
  persistent : out.persistent = c.persistent

/-- Copy or clamp the chosen whole field. This theorem accounts for both
address setup instructions, every bit movement and the terminal test. -/
theorem copy_run (M : Machine bits p r k) (port : Option LocalPort)
    (pc : Fin 2 → Fin p) (copy : Fin 5 → Fin p) (reg : Fin 11 ↪ Fin r) (done : Fin p)
    (hprep : ∀ i, M.code (pc i) = prepare port pc reg (copy 0) i)
    (hcopy : LeafFieldCopy.Linked M (mode port) copy (copyRegs reg) done)
    (base : LocalPort → ℕ) (buf : Buffers D H w) (offset n lo : ℕ)
    (inside : offset+n ≤ ramPayloadWidth D H w) (fit : lo+n < 2^bits)
    (apart : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+n ≤ base a)
    (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^bits)
    (c : Config bits p r) (hc : c.pc = pc 0) (hbase : ∀ a, c.reg (reg (baseReg a)) = word bits (base a))
    (hlen : c.reg (reg 5) = word bits n) (hoff : c.reg (reg 6) = word bits offset)
    (hdst : c.reg (reg 2) = word bits (lo+n)) (hone : c.reg (reg 3) = 1)
    (stored : Stored base buf c.privateMem) :
    ∃ out, Prefix M c (List.replicate (5*n+3) .tick) out ∧
      Result reg done c out lo (Field port offset n inside buf) := by
  let src := sourceAddress base offset port
  let a := c.put (pc 1) (reg 0) (word bits src)
  let b := a.put (copy 0) (reg 1) (word bits lo)
  have s₀ : M.program.step c = .localStep a := by
    cases port <;> simp [Machine.program, hc, hprep 0, prepare, Instr.run, BinaryOp.eval,
      hbase,hoff, src, sourceAddress, a, word]
  have s₁ : M.program.step a = .localStep b := by
    change (M.code (pc 1)).run M.publicData a = _
    rw [hprep 1]
    simp [prepare, Instr.run, BinaryOp.eval, b, a, Config.put, hdst, hlen, word]
  have pre : Prefix M c (List.replicate 2 .tick) b := .tick s₀ (.tick s₁ (.nil _))
  let bs := Field port offset n inside buf
  have length : bs.length = n := length_field ..
  have data (i : Fin bs.length) :
      (mode port).value b.privateMem (word bits (src+i.val)) = PrivateFields.bitValue bits bs[i.val] := by
    cases port with
    | none => simp [bs, Field, mode, LeafFieldCopy.Source.value, PrivateFields.bitValue]
    | some port =>
      have hi : offset+i.val < ramPayloadWidth D H w := by have := i.isLt; omega
      simpa [bs, Field, mode, LeafFieldCopy.Source.value, src, sourceAddress, b, a, Config.put,
        Nat.add_assoc] using stored port ⟨offset+i.val,hi⟩
  have safe (h : mode port = .resident) : src+bs.length ≤ 2^bits ∧
      (src+bs.length ≤ lo ∨ lo+bs.length ≤ src) := by
    cases port with
    | none => contradiction
    | some port =>
      have := sourceFit port
      have := apart port
      simp only [src,sourceAddress,length]
      omega
  obtain ⟨out,tail,res⟩ := LeafFieldCopy.run hcopy b rfl src lo bs
    (by change b.reg (reg 0) = _; simp [b,a,Config.put]) (by change b.reg (reg 1) = _; simp [b])
    (by change b.reg (reg 2) = _; simp [b,a,Config.put,hdst,length])
    (by change b.reg (reg 3) = _; simp [b,a,Config.put,hone])
    (by rwa [length]) safe data
  refine ⟨out, ?_, res.pc, res.destination, ?_, res.privateMem, res.persistent⟩
  · convert pre.append tail using 1
    rw [← List.replicate_add, length]
    congr 1; omega
  · intro i h0 h1 h2 h4
    rw [res.frame i h0 h2 h4]
    simp [b,a,Config.put,Function.update_of_ne h0,Function.update_of_ne h1]

end PairSimulation.LeafIncidentLoad

end VPVNP
end Computability
end OAI
