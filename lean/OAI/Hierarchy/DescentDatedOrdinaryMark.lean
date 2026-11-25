import OAI.Hierarchy.DescentOrdinaryMarkPortHeader
import OAI.Hierarchy.DescentOrdinaryMarkNative
import OAI.Hierarchy.DescentDatedMaterialPhase
import OAI.Hierarchy.DescentDatedPriorHeaderProgram

namespace OAI
/-! The original wire-to-mark publisher between the venue roster and the signed ordinary program. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentOrdinaryMarkProject DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSharedCableNames
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ}
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
local notation "ms" => v.markShape
local notation "base₀" => v.peerTail floor
local notation "pre₀" => (ms).markStart (base₀)
def markVisited : Bank :=
  PriorHeader.visited v.area.H v.signed.groups v.signed.lanes v.signed.degree (v.donorEnd floor)
def markWire (input : Dated.Operands) (o : Fin (ms).slots) : Bank :=
  let seat : Fin ((ms).priorBlocks*(ms).cap) × Fin 11 := finProdFinEquiv.symm o
  let pair : Fin (ms).priorBlocks × Fin (ms).cap := finProdFinEquiv.symm seat.1
  input.wire pair.1.val (finProdFinEquiv ((0:Fin 2),pair.2)).val

def markBorn (o : Fin (ms).slots) : Bool :=
  decide ((finProdFinEquiv.symm o : Fin ((ms).priorBlocks*(ms).cap) × Fin 11).2.val≠0)

variable (input : Dated.Operands)
local notation "ports₀" => (ms).portChart (base₀) (v.markVisited floor)
local notation "core₀" => DescentOrdinaryMarkProject.program (ports₀) (v.markWire input) v.markBorn (pre₀)
  (ms).oldHosts (ms).hosts (ms).groups (ms).blocks (ms).degree (ms).cap (ms).oldLanes (ms).lanes v.materialPitch
/-- Only public dimensions, original wire pointers and the physical prior roster
address occur in either the program text or the clock. -/
def markNative (s : DescentOrdinaryMarkProject.Shape) (floor : ℕ) (visited : Bank) (i : Dated.Operands)
    (pitch w : ℕ) : NativePhase w :=
  let origin (o : Fin s.slots) :=
    let seat : Fin (s.priorBlocks*s.cap) × Fin 11 := finProdFinEquiv.symm o
    let pair : Fin s.priorBlocks × Fin s.cap := finProdFinEquiv.symm seat.1
    i.wire pair.1.val (finProdFinEquiv ((0:Fin 2),pair.2)).val
  let birth (o : Fin s.slots) :=decide ((finProdFinEquiv.symm o : Fin (s.priorBlocks*s.cap) × Fin 11).2.val≠0)
  let pre:=s.markStart floor
  let chart:=s.portChart floor visited
  (s.portPhase floor w).seq {
    program:=DescentOrdinaryMarkProject.program chart origin birth pre s.oldHosts s.hosts s.groups s.blocks s.degree s.cap s.oldLanes s.lanes pitch w
    ticks:=DescentOrdinaryMarkProject.ticks chart origin birth pre s.oldHosts s.hosts s.groups s.blocks s.degree s.cap s.oldLanes s.lanes
    image:=DescentOrdinaryMarkProject.memory chart origin birth pre s.oldHosts s.hosts s.groups s.blocks s.degree s.cap s.oldLanes s.lanes pitch
    cheap:=by
      unfold DescentOrdinaryMarkProject.program DescentResetStemProjectExpr.program
        DescentResetStemProject.postProgram Overlap.program Overlap.tables DescentVectorBookReshape.program
      exact @cheap_seq _ _ _ (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _) <|
        @cheap_seq _ _ _ (@cheap_seq _ _ _ (@ProtocolRAM.program_cheap _ _) <|
          @cheap_seq _ _ _ (@cheap_seq _ _ _
            (@cheap_seq _ _ _ (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _)
              (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _)) (@scan_cheap _ _ _ _))
            (@cheap_seq _ _ _ (@DescentStaticWordColumn.cheap _ _ _ _) (@scan_cheap _ _ _ _)))
          (@DescentStaticWordColumn.cheap _ _ _ _) }

def mark (w : ℕ) : NativePhase w :=markNative (ms) (base₀) (v.markVisited floor) input v.materialPitch w

theorem mark_eq {F' P' : Type} [Field F'] (v' : PhysicalOrdinary F' P') (floor' : ℕ)
    (shapes : v.markShape=v'.markShape) (floors : v.peerTail floor=v'.peerTail floor')
    (visited : v.markVisited floor=v'.markVisited floor') (pitch : v.materialPitch=v'.materialPitch) (w : ℕ) :
    v.mark floor input w=v'.mark floor' input w := by
  unfold mark
  rw [shapes,floors,visited,pitch]

structure MarkRoom (w : ℕ) : Prop where
  lanes : 0<(ms).lanes
  blocks : 0<(ms).blocks
  visited : (v.markVisited floor).Fits w (base₀)
  rosterSize : (ms).oldHosts*(ms).paths≤(v.markVisited floor).size
  wires : ∀o,(v.markWire input o).Fits w (base₀)
  sourceSize : ∀o,(ms).sourceRows≤(v.markWire input o).size
  room : v.markEnd floor<2^w

theorem mark_core_room (h : v.MarkRoom floor input w) :
    Safe (ports₀) (v.markWire input) (pre₀) (ms).oldHosts (ms).hosts (ms).groups (ms).blocks
      (ms).degree (ms).cap (ms).oldLanes (ms).lanes w := by
  have lower := DescentOrdinaryMarkProject.cut_le (pre₀) (ms).paths (ms).slots (ms).oldHosts (ms).groups
    (ms).blocks (ms).degree (ms).cap (ms).oldLanes (ms).lanes
  have sub : (pre₀)≤v.markEnd floor :=
    ((Nat.le_add_right ..).trans lower).trans (Nat.le_add_right ..)
  exact ⟨h.lanes,h.blocks,fun o=>(ms).port_access (base₀) _ _ h.visited h.rosterSize (h.wires o) (h.sourceSize o)
    (sub.trans_lt h.room),h.room⟩

theorem mark_any (h : v.MarkRoom floor input w) (m : Memory w) :
    (v.mark floor input w).Runs m ∧
      ∀u,u<(base₀) ∨ v.markEnd floor≤u→(v.mark floor input w).image m u=m u := by
  let s₀:=(ms).portPhase (base₀) w
  have core:=v.mark_core_room floor input h
  have lower := DescentOrdinaryMarkProject.cut_le (pre₀) (ms).paths (ms).slots (ms).oldHosts (ms).groups
    (ms).blocks (ms).degree (ms).cap (ms).oldLanes (ms).lanes
  have start : (base₀)≤(pre₀) := Nat.le_add_right ..
  have end₀ : (pre₀)≤v.markEnd floor := ((Nat.le_add_right ..).trans lower).trans (Nat.le_add_right ..)
  have p := (ms).port_any (base₀) m (end₀.trans_lt h.room)
  have q := DescentOrdinaryMarkProject.any (ports₀) (v.markWire input) v.markBorn (pre₀) v.materialPitch core (s₀.image m)
  refine ⟨?_,?_⟩
  · intro Pn R K machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then p.1 q.1 machine pc reg pub exit rom advice cfg raw enter same
  intro u outside
  rcases outside with lo|hi
  · exact (q.2.1 _ (.inl (lo.trans_le start))).trans (p.2 _ (.inl lo))
  · exact (q.2.1 _ (.inr hi)).trans (p.2 _ (.inr (end₀.trans hi)))

theorem mark_issued (h : v.MarkRoom floor input w) (old : 0<(ms).oldLanes)
    (R : Fin (ms).oldHosts→Fin (ms).paths→Option (Fin (ms).oldHosts))
    (panel : Fin (ms).slots→Fin (ms).oldHosts→Fin ((ms).groups*(ms).blocks)→
      Option (DescentSharedCableNames.Stage.Live (ms).degree (ms).cap)) (m : Memory w)
    (seen : ∀v₀ j,m ((v.markVisited floor).base+(v₀.val*(ms).paths+j.val))=(DescentPackedColony.target (R v₀ j):Word w))
    (read : ∀o,Reads (v.markWire input o) (fun j g=>DescentSignedCableCodec.encode (D:=(ms).degree) (cap:=(ms).cap) (panel o j g)) (ms).oldLanes m) :
    ∀x j,
      let term := DescentOrdinaryMarkProject.markExpr (pre₀) (ms).paths (ms).slots (ms).oldHosts (ms).hosts (ms).groups (ms).blocks
        (ms).degree (ms).cap (ms).oldLanes (ms).lanes x j
      term.Fits w (v.markEnd floor) ∧ DescentPackedZip.Source term (DescentOrdinaryMarkProject.bits (H:=(ms).hosts) R panel v.markBorn v.materialPitch x j)
        (ms).lanes ((v.mark floor input w).image m) := by
  let pre:=(ms).portPhase (base₀) w
  have core:=v.mark_core_room floor input h
  have mounted:=(ms).port_mounted (base₀) _ R m h.visited h.rosterSize seen
  have stored (o) : Reads (v.markWire input o) (fun j g=>DescentSignedCableCodec.encode (D:=(ms).degree) (cap:=(ms).cap) (panel o j g)) (ms).oldLanes (pre.image m) :=by
    intro p
    have lt : (row (ms).oldHosts ((ms).groups*(ms).blocks) (ms).oldLanes p).val<(v.markWire input o).size :=
      (row _ _ _ p).isLt.trans_le (h.sourceSize o)
    exact (DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left lt _).trans_le (h.wires o).2.2))).trans (read o p)
  have size : rows (ms).oldHosts (ms).groups (ms).lanes ≤ (v.markVisited floor).size :=
    (Nat.le_add_left _ _).trans (Nat.le_pow_clog (by decide) _)
  have narrow := (size.trans ((Nat.le_add_left ..).trans h.visited.2.2)).trans_lt
    (((ms).low (base₀)).trans_lt h.room)
  have actual:=run_fixed (ports₀) (v.markWire input) v.markBorn (pre₀) v.materialPitch R panel
    (pre.image m) old core.lanes core.blocks core.access mounted stored narrow core.room
  exact fun x j=>⟨actual.2.1 x j,actual.2.2.1 x j⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
