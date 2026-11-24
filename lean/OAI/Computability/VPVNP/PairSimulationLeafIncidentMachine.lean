import OAI.Computability.VPVNP.PairSimulationLeafIncidentCore
import OAI.Computability.VPVNP.PairSimulationLeafIncidentGeometry
import OAI.Computability.VPVNP.RAMApplications

/-!
# Fixed native table for preparing the virtual validator's incident stack

Six caller words designate the geometry, the current site and the two
private intervals. The table computes every address and fills the stack
directly from the four resident halves. Its destination top is the exclusive
end even though the working cursor retreats to the base.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafIncidentMachine

open BurstRAM PrivateRAM CursorRouting CursorNetwork RAMLayout PrimedCounter.GuessWord
open LeafFieldCopy (word)

variable {W D H w p r k : ℕ}

/-- Control labels of the geometry preparation and field-loading loops. -/
abbrev Stage := LeafIncidentGeometry.Stage ⊕ LeafIncidentCore.Stage

/-- The native row for preparing the field addresses or copying their bits. -/
def instruction (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) : Stage → Instr W p r k
  | .inl i => LeafIncidentGeometry.instruction (pc ∘ Sum.inl) reg (pc (.inr (.inl .sendNext))) i
  | .inr s => LeafIncidentCore.instruction (pc ∘ Sum.inr) reg done s

private theorem resize_twice (i : Instr 1 p r k) : (i.resize 5).resize W = i.resize W := by
  cases i <;> try rfl
  case constant dst v next => simp only [Instr.resize, resize_literal (show 1 ≤ 5 by decide)]

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) (s : Stage) :
    (instruction (W := 5) (k := k) pc reg done s).resize W = instruction pc reg done s := by
  cases s with
  | inl i => exact LeafIncidentGeometry.resize_instruction ..
  | inr s =>
    change (LeafIncidentCore.instruction _ _ _ _).resize _ = _
    rw [← LeafIncidentCore.resize_instruction (W := 5) (pc ∘ Sum.inr) reg done s, resize_twice,
      LeafIncidentCore.resize_instruction]
    rfl

/-- The complete incident machine is installed at the chosen host labels. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p) :=
  ∀ s, M.code (pc s) = instruction pc reg done s

/-- Starting address of each of the four resident half-wire arrays. -/
def base (node width : ℕ) : LocalPort → ℕ
  | .outgoing false => node
  | .outgoing true => node+width
  | .incoming false => node+2*width
  | .incoming true => node+3*width

/-- Register write footprint of the geometry and incident-loading stages together. -/
def changed : List (Fin 30) := (LeafIncidentGeometry.rows.map Prod.fst) ++ LeafIncidentCore.changed

/-- Total native instructions, including the 24 geometry-preparation rows. -/
def ticks (v : Site D) (H w : ℕ) := 24+LeafIncidentCore.ticks v H w

variable [NeZero D]

/-- Exact memory, register frame and continuation after incident materialization. -/
structure Result (reg : Fin 30 ↪ Fin r) (done : Fin p) (lo : ℕ) (v : Site D) (buf : Buffers D H w)
    (c out : Config W p r) : Prop where
  pc : out.pc = done
  top : out.reg (reg 24) = word W (lo+width D H w)
  cursor : out.reg (reg 2) = word W lo
  frame : ∀ i, (∀ j ∈ changed, i ≠ reg j) → out.reg i = c.reg i
  memory : out.privateMem = LeafFieldCopy.place lo (List.ofFn (incidentBuffer (0,v) buf)) c.privateMem
  persistent : out.persistent = c.persistent

/-- Full machine execution from raw word arguments, including the arithmetic
that prepares the source bases, both field lengths and the stack top. -/
theorem run (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 30 ↪ Fin r) (done : Fin p)
    (hl : Linked M pc reg done) (node lo : ℕ) (buf : Buffers D H w) (v : Site D)
    (c : Config W p r) (hc : c.pc = pc (.inl 0))
    (ready : LeafIncidentGeometry.Ready D H w v.val node lo (c.reg ∘ reg)) (hDW : D < W)
    (stored : LeafIncidentLoad.Stored (base node (ramPayloadWidth D H w)) buf c.privateMem)
    (destFits : lo+width D H w < 2^W) (srcFits : node+4*ramPayloadWidth D H w ≤ 2^W)
    (sep : node+4*ramPayloadWidth D H w ≤ lo ∨ lo+width D H w ≤ node) :
    (ticks v H w ≤ 80*w+6*D+53+layerCount D*(10*blockBits H w+14)) ∧
      ∃ out, Prefix M c (List.replicate (ticks v H w) .tick) out ∧ Result reg done lo v buf c out := by
  have linkG : LeafIncidentGeometry.Linked M (pc ∘ Sum.inl) reg (pc (.inr (.inl .sendNext))) :=
    fun s => hl (.inl s)
  obtain ⟨a,prep,ap,g,am,aper,af⟩ := LeafIncidentGeometry.run M _ _ _ linkG c hc ready
    (Nat.pos_of_ne_zero (NeZero.ne D)) hDW
  let origin := base node (ramPayloadWidth D H w)
  have dim : a.reg (reg 11) = c.reg (reg 11) := af _ fun l hl => reg.injective.ne (fun e =>
    (show (11 : Fin 30) ∉ LeafIncidentGeometry.rows.map Prod.fst by decide) (e ▸ List.mem_map_of_mem hl))
  have site : a.reg (reg 13) = c.reg (reg 13) := af _ fun l hl => reg.injective.ne (fun e =>
    (show (13 : Fin 30) ∉ LeafIncidentGeometry.rows.map Prod.fst by decide) (e ▸ List.mem_map_of_mem hl))
  have fixed : LeafSuccessorFields.Fixed (LeafIncidentCore.successorRegs reg) origin v w a := by
    refine ⟨g.one,g.successor,?_,dim.trans ready.dim,g.last,site.trans ready.site,g.count,g.zero⟩
    intro port
    cases port with
    | outgoing side => cases side with | false => exact g.base₀ | true => exact g.base₁
    | incoming side => cases side with | false => exact g.base₂ | true => exact g.base₃
  have bound (p : LocalPort) : node ≤ origin p ∧ origin p+ramPayloadWidth D H w ≤ node+4*ramPayloadWidth D H w := by
    cases p with | outgoing s | incoming s => cases s <;> simp only [origin,base] <;> omega
  obtain ⟨cost,out,body,res⟩ := LeafIncidentCore.run M (pc ∘ Sum.inr) reg done
    (fun s => hl (.inr s)) origin buf v lo a ap fixed g.block hDW g.cursor (am ▸ stored) destFits
    (fun p => (bound p).2.trans srcFits)
    (fun p => sep.imp ((bound p).2.trans) (fun h => h.trans (bound p).1))
  have top : out.reg (reg 24) = a.reg (reg 24) := res.frame _ fun j hj => reg.injective.ne (fun e =>
    (show (24 : Fin 30) ∉ LeafIncidentCore.changed by decide) (e ▸ hj))
  refine ⟨by unfold ticks; omega,out, ?_,res.pc,top.trans g.top,res.cursor, ?_, ?_,res.persistent.trans aper⟩
  · change Prefix M c (List.replicate 24 .tick) a at prep
    simpa only [ticks,List.replicate_add] using prep.append body
  · intro i hi
    rw [res.frame i (fun j hj => hi j (List.mem_append_right _ hj))]
    exact af i (fun l h => hi _ (List.mem_append_left _ (List.mem_map_of_mem h)))
  · rw [res.memory,am]

end PairSimulation.LeafIncidentMachine

end VPVNP
end Computability
end OAI
