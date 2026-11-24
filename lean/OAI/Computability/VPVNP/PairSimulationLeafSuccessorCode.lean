import OAI.Computability.VPVNP.PairSimulationLeafIncidentLoad
import OAI.Computability.VPVNP.PairSimulationLeafSuccessorClass

/-!
# Native table for the successor fields at cursor zero

The first eleven registers are the shared incident-field mover. Registers
11–14 hold the dimension, last cursor, site, and site count. Register 16
holds zero. The three temporaries 17–19 hold the sender, mask, and class.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorFields

open BurstRAM PrivateRAM CursorNetwork CursorRouting PrimedCounter.GuessWord
open LeafFieldCopy (word)

variable {D H w W p r k : ℕ}

/-- Control labels for testing outgoing and incoming endpoints, classifying the sender,
choosing a half-wire and copying its successor field. -/
inductive Stage where
  | sendNext | sendTest | recvTest | sender (recv : Bool) | zeroOffset (recv : Bool)
  | classify (recv : Bool) (i : Fin 6) | offset (recv : Bool) | side
  | prepare (recv : Bool) (use : Option Bool) (i : Fin 2)
  | move (recv : Bool) (use : Option Bool) (i : Fin 5)
  deriving DecidableEq, Fintype

/-- Embed the incident-field mover's eleven registers in the first eleven slots of the
successor loader. -/
def subRegs (reg : Fin 20 ↪ Fin r) : Fin 11 ↪ Fin r := (Fin.castAddEmb 9).trans reg

/-- Wire the classifier's sender, unit, mask and class registers to successor-loader slots 17,
3, 18 and 19. -/
def classRegs (reg : Fin 20 ↪ Fin r) : Fin 4 ↪ Fin r :=
  (⟨![17,3,18,19], by decide⟩ : Fin 4 ↪ Fin 20).trans reg

/-- Turn a selected side into the incoming or outgoing half-wire port, retaining an absent
selection at an endpoint. -/
def port (recv : Bool) (use : Option Bool) : Option LocalPort :=
  use.map fun side => if recv then .incoming side else .outgoing side

/-- The successor-loader row at a given stage, from testing whether an edge exists through
choosing the source field and moving its bits. -/
def instruction (pc : Stage → Fin p) (reg : Fin 20 ↪ Fin r) (done : Fin p) : Stage → Instr W p r k
  | .sendNext => .binary .add (reg 17) (reg 13) (reg 3) (pc .sendTest)
  | .sendTest => .jumpEq (reg 17) (reg 14) (pc (.zeroOffset false)) (pc (.sender false))
  | .recvTest => .jumpEq (reg 13) (reg 16) (pc (.zeroOffset true)) (pc (.sender true))
  | .sender false => .copy (reg 17) (reg 13) (pc (.classify false 0))
  | .sender true => .binary .sub (reg 17) (reg 13) (reg 3) (pc (.classify true 0))
  | .zeroOffset recv => .constant (reg 6) 0 (pc (.prepare recv none 0))
  | .classify recv i => LeafSuccessorClass.instruction (pc ∘ Stage.classify recv) (classRegs reg)
      (pc (.offset recv)) i
  | .offset recv => .binary .mul (reg 6) (reg 19) (reg 5) (pc (if recv then .side else .prepare false (some true) 0))
  | .side => .jumpEq (reg 19) (reg 12) (pc (.prepare true (some true) 0)) (pc (.prepare true (some false) 0))
  | .prepare recv use i => LeafIncidentLoad.prepare (port recv use) (pc ∘ Stage.prepare recv use)
      (subRegs reg) (pc (.move recv use 0)) i
  | .move recv use i => LeafFieldCopy.instruction (LeafIncidentLoad.mode (port recv use))
      (pc ∘ Stage.move recv use) (LeafIncidentLoad.copyRegs (subRegs reg)) (if recv then done else pc .recvTest) i

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 20 ↪ Fin r) (done : Fin p) (s : Stage) :
    (instruction (W := 1) (k := k) pc reg done s).resize W = instruction pc reg done s := by
  cases s <;> try rfl
  case sender recv => cases recv <;> rfl
  case classify => exact LeafSuccessorClass.resize_instruction ..
  case prepare => exact LeafIncidentLoad.resize_prepare ..
  case move => exact LeafFieldCopy.resize_instruction ..

/-- Each host instruction at a successor-loader stage implements its prescribed row using the
supplied register placement and exit. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 20 ↪ Fin r) (done : Fin p) :=
  ∀ s, M.code (pc s) = instruction pc reg done s

/-- The sending site index of an outgoing edge is the current index. For an incoming edge it is
the preceding index, with subtraction truncated at zero. -/
def sender (recv : Bool) (v : Fin (2^D)) := if recv then v.val-1 else v.val

/-- Whether the indicated edge exists without wrapping. An incoming edge requires a positive
site index and outgoing requires a successor below the site count. -/
def active (recv : Bool) (v : Fin (2^D)) : Bool :=
  if recv then decide (0 < v.val) else decide (v.val+1 < 2^D)

theorem sender_lt (recv : Bool) (v : Fin (2^D)) (h : active recv v = true) : sender recv v + 1 < 2^D := by
  cases recv <;> simp [active, sender] at h ⊢ <;> have := v.isLt <;> omega

/-- The low-bit successor class of the edge's sender, or no class at a missing nonwrapping
endpoint. -/
def selected (recv : Bool) (v : Fin (2^D)) : Option (Fin D) :=
  if h : active recv v then some (successorClass (sender_lt recv v h)) else none

/-- The outgoing field uses the true side. The incoming field uses that side exactly for the
final successor class. -/
def useSide (recv : Bool) (j : Fin D) : Bool := if recv then decide (j.val = D-1) else true

/-- Offset of the selected successor field in its half-wire buffer, measured in blocks of eight
machine words' worth of bits. -/
def sourceOffset (recv : Bool) (v : Fin (2^D)) (w : ℕ) := ((selected recv v).map Fin.val).getD 0 * (8*w)

theorem offsetFits [NeZero D] (recv : Bool) (v : Fin (2^D)) :
    sourceOffset recv v w + 8*w ≤ ramPayloadWidth D H w := by
  unfold sourceOffset ramPayloadWidth
  cases h : selected recv v with
  | none =>
    have hd : 1 ≤ D := Nat.pos_of_ne_zero (NeZero.ne D)
    have := Nat.mul_le_mul_right (8*w) hd
    simp only [Option.map_none, Option.getD_none, Nat.zero_mul, Nat.zero_add]
    omega
  | some j =>
    have := Nat.mul_le_mul_right (8*w) j.isLt
    rw [Nat.succ_mul] at this
    simp only [Option.map_some, Option.getD_some]
    omega

/-- The eight-word successor field selected from the incoming or outgoing half-wire buffer,
with an all-zero field at a missing endpoint. -/
def succBits [NeZero D] (recv : Bool) (v : Fin (2^D)) (buf : Buffers D H w) : List Bool :=
  LeafIncidentLoad.Field (port recv ((selected recv v).map (useSide recv))) (sourceOffset recv v w) (8*w)
    (offsetFits recv v) buf

@[simp] theorem length_succBits [NeZero D] (recv : Bool) (v : Fin (2^D)) (buf : Buffers D H w) :
    (succBits recv v buf).length = 8*w := List.length_ofFn

/-- The shared mover and geometry registers hold the constants, half-wire bases, field length,
dimension and site coordinates required for successor selection. -/
structure Fixed (reg : Fin 20 ↪ Fin r) (base : LocalPort → ℕ) (v : Fin (2^D)) (w : ℕ) (c : Config W p r) : Prop where
  one : c.reg (reg 3) = 1
  len : c.reg (reg 5) = word W (8*w)
  bases : ∀ a, c.reg (subRegs reg (LeafIncidentLoad.baseReg a)) = word W (base a)
  dims : c.reg (reg 11) = word W D
  last : c.reg (reg 12) = word W (D-1)
  site : c.reg (reg 13) = word W v.val
  sites : c.reg (reg 14) = word W (2^D)
  zero : c.reg (reg 16) = 0

/-- Indices of the eight local registers that the successor-field selection and copy may
overwrite. -/
def changed : List (Fin 20) := [0,1,2,4,6,17,18,19]

/-- Every host register outside the successor loader's eight writable slots agrees between the
input and output configurations. -/
def Frame (reg : Fin 20 ↪ Fin r) (c out : Config W p r) :=
  ∀ i, (∀ j ∈ changed, i ≠ reg j) → out.reg i = c.reg i

theorem Frame.trans {reg : Fin 20 ↪ Fin r} {a b c : Config W p r} (h : Frame reg a b) (h' : Frame reg b c) :
    Frame reg a c := fun i hi => (h' i hi).trans (h i hi)

theorem Fixed.of_frame {reg : Fin 20 ↪ Fin r} {base v w} {c out : Config W p r}
    (f : Fixed reg base (D := D) v w c) (h : Frame reg c out) : Fixed reg base v w out := by
  have keep (j : Fin 20) (hj : j ∉ changed) : out.reg (reg j) = c.reg (reg j) :=
    h _ (fun a ha => reg.injective.ne (fun eq => hj (eq ▸ ha)))
  refine ⟨(keep _ (by decide)).trans f.one, (keep _ (by decide)).trans f.len, ?_,
    (keep _ (by decide)).trans f.dims, (keep _ (by decide)).trans f.last, (keep _ (by decide)).trans f.site,
    (keep _ (by decide)).trans f.sites, (keep _ (by decide)).trans f.zero⟩
  intro a
  exact (keep (Fin.castAdd 9 (LeafIncidentLoad.baseReg a))
    (by cases a with | outgoing b | incoming b => cases b <;> decide)).trans (f.bases a)

theorem frame_put {reg : Fin 20 ↪ Fin r} (c : Config W p r) (next : Fin p) (j : Fin 20)
    (v : Word W) (hj : j ∈ changed) : Frame reg c (c.put next (reg j) v) :=
  fun _ hi => Function.update_of_ne (hi j hj) _ _

theorem step_at {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 20 ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (s : Stage) (c : Config W p r) (hc : c.pc = pc s) :
    M.program.step c = (instruction pc reg done s).run M.publicData c := by simp [Machine.program,hc,hl s]

end PairSimulation.LeafSuccessorFields

end VPVNP
end Computability
end OAI
