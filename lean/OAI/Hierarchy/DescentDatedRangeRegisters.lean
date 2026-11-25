import OAI.Hierarchy.DescentOriginalRangeRegister
import OAI.Hierarchy.DescentArchiveRegisterCoordinates
import OAI.Hierarchy.DescentRangeRegisterRAM
import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentReachedNodeCells

namespace OAI
/-! # The three carried range fields on an original dated register snapshot -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentSIMDLookup DescentColonies
open DescentRetainedRangeDigits DescentDatedPriorOperand DescentPackedColony DescentOperandStateBanks
open Computability.VPVNP.BurstRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist)
    (B : BitDescription W) (localOrder : ∀v,(B.recipe v).Node≃Fin (Fintype.card (B.recipe v).Node))
    (capacity : ∀v,Fintype.card (B.recipe v).Node≤ports.nodes)
    (hosts : ∀v,(Reached.NodeCells.coordinate r v).1.val<ports.operandHosts) (groups : S.groupCount age=ports.venue.groups)
    (radix : k=ports.venue.k) (pos : 0<ports.operandLanes) (m : Memory w)

local notation "coords" v => Reached.NodeCells.coordinate r v
local notation "blocksAt" => fun x : NodeOrder.All B=>(coords x.1).2.2.cast (congrArg (2^·) radix)
local notation "hostsAt" => fun x : NodeOrder.All B=>(⟨(coords x.1).1.val,hosts x.1⟩:Fin ports.operandHosts)
local notation "groupsAt" => fun x : NodeOrder.All B=>(coords x.1).2.1.cast groups
local notation "slots" => fun x : NodeOrder.All B=>(localOrder x.1 x.2).castLE (capacity x.1)
local notation "l" => ports.rangeLayout

local notation "reg" => rangeRegister ports r B localOrder capacity hosts groups radix pos m

theorem range_word (v : W.graph.Site) (u : (B.recipe v).Node) (j : Fin ports.argumentsPerNode)
    (f : Fin 3) (cells : Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.operandBits*ports.nodes))
    (seen : Reads (previousBank l ports.archive.arguments ((coords v).2.2.cast (congrArg (2^·) radix))
      (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)) cells ports.operandLanes m)
    (fits : ports.operandBits*ports.nodes*ports.operandLanes≤w) :
    (reg).word ⟨v,u⟩ j.val f=((encode ports.operandBits ports.nodes).symm
      (cells ⟨(coords v).1.val,hosts v⟩ ((coords v).2.1.cast groups)) ((localOrder v u).castLE (capacity v))).val :=
  word_read ports.archive l ports.operandBits m pos blocksAt hostsAt groupsAt slots ⟨v,u⟩ j f cells seen fits

/-- The cell addressed on the RAM side is occupied by the same typed node used by the
chronological induction, even when other SIMD lanes or node slots remain empty. -/
theorem range_occupant (x : NodeOrder.All B) :
    Reached.NodeCells.whereAt r B localOrder (coords x.1).2.2 ((localOrder x.1 x.2).castLE (capacity x.1))
      (coords x.1).1 (coords x.1).2.1=some x :=
  Reached.NodeCells.whereAt_at _ _ _ _ _ _ _ _ _ rfl rfl

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
