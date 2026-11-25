import OAI.Hierarchy.DescentRangePage
import OAI.Hierarchy.DescentArchiveRegisterCoordinates
import OAI.Hierarchy.DescentDatedNodeMetadataChart
import OAI.Hierarchy.DescentPreviousOperandLayout
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentArchiveWorldShape
import OAI.Hierarchy.DescentPrimitivePaletteToken
import OAI.Hierarchy.DescentInitialRolePages
import OAI.Hierarchy.DescentOriginalRangeSlots

namespace OAI
/-! # Positive reads of the archived operand, node and primitive pages -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- Both original primitive fields remain below the seven permanent operand pages. -/
def metadataChart (p : DatePorts) : DescentDatedNodeMetadata.Chart :=
  ⟨2^p.venue.k,p.nodes,p.operandHosts,p.venue.groups,p.operandBits,p.operandLanes⟩

def metadataPage (p : DatePorts) (f : Fin 2) (x : Fin (2^p.venue.k)) : Bank :=
  if p.archive.seed then p.metadataChart.seedBank p.archive.nodeBase f x
  else p.metadataChart.bank p.archive.nodeBase f x

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)

/-- The original node order supplies this physical row even when the physical
rectangle has extra actors, the group ends in a partial word, or the node is unfunded. -/
def slotAt (x : Fin (2^ports.venue.k)) (j : Fin ports.nodes) (h : Fin ports.operandHosts) (g : Fin ports.venue.groups) :
    Option (NodeOrder.All B) :=
  Reached.NodeCells.atPhysical r B number (x.cast (congrArg (2^·) room.radix.symm)) j h (g.cast room.groups.symm)

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B → Label G s Z op) (pointer : NodeOrder.All B → ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)

/-- All fields describe the *same* RAM state. The pointer function names the
actual shared grain, original exterior port, or first local alias at each live
argument. The first metadata page is occupancy at startup and the paid prefix
at subsequent dates. The count field remains meaningful beyond the last argument. -/
structure ArchiveRead (m : Memory w) : Prop where
  headers : ∀(x : Fin (2^ports.venue.k)) (j : Fin ports.argumentsPerNode) (f : Fin 4),
      ∃cells : (Fin ports.operandHosts → Fin ports.venue.groups → Cell (ports.operandBits*ports.nodes)),
        Reads (previousBank ports.rangeLayout ports.archive.arguments x
        (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) j)) cells ports.operandLanes m ∧
        ∀h g n (y : NodeOrder.All B),slotAt ports r B number room x n h g=some y → j.val<(occurrences (shape.sites y.1) y.2).length →
          ((encode ports.operandBits ports.nodes).symm (cells h g) n).val = (pointer y j.val).header f
  spans : ∀(x : Fin (2^ports.venue.k)) (j : Fin ports.argumentsPerNode) (f : Fin 3),
      ∃cells : (Fin ports.operandHosts → Fin ports.venue.groups → Cell (ports.operandBits*ports.nodes)),
        Reads (previousBank ports.rangeLayout ports.archive.arguments x
        (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)) cells ports.operandLanes m ∧
        ∀h g n (y : NodeOrder.All B),slotAt ports r B number room x n h g=some y → (j.val<(occurrences (shape.sites y.1) y.2).length ∨ f=2) →
          ((encode ports.operandBits ports.nodes).symm (cells h g) n).val = atSlot (shape.sites y.1) y.2 j.val f
  nodeFlags : ∀x,Reads (metadataPage ports 0 x) (fun h g=>encode ports.operandBits ports.nodes
    (fun j=>(flags x j h g:Cell ports.operandBits))) ports.operandLanes m
  arity : ∀x,Reads (metadataPage ports 1 x) (fun h g=>encode ports.operandBits ports.nodes
    (fun j=>((slotAt ports r B number room x j h g).elim 0 (fun y=>(occurrences (shape.sites y.1) y.2).length):Cell ports.operandBits))) ports.operandLanes m
  primitive : ∀x : Fin (2^ports.venue.k),Reads (ports.archive.roles.bank x.val)
    (fun h g=>encode (printedBits G s Z op) ports.nodes (fun j=>
      (slotAt ports r B number room x j h g).elim 0 (fun y=>token G s Z op (label y)))) ports.roleLanes m

/-- All seven pages of the actual previous archive are available to an ordinary gather,
including the packed words that contain unused lanes. -/
theorem ArchiveRead.operands {m : Memory w}
    (stored : Hierarchy.DescentSixParty.Chronology.DatePorts.ArchiveRead
      ports r B number room shape op label pointer flags m)
    (x : Fin (2^ports.venue.k)) (pg : Pages ports.argumentsPerNode) :
    ∃cells : (Fin ports.operandHosts → Fin ports.venue.groups → Cell (ports.operandBits*ports.nodes)),
        Reads (previousBank ports.rangeLayout ports.archive.arguments x pg) cells ports.operandLanes m :=by
  obtain ⟨⟨f,j⟩,rfl⟩:=((finProdFinEquiv : (Fin 7×Fin ports.argumentsPerNode)≃Pages ports.argumentsPerNode).surjective pg)
  by_cases header : f.val<4
  · let h : Fin 4:=⟨f.val,header⟩
    obtain ⟨cells,read,_⟩:=stored.headers x j h
    have id : h.castLE (by decide : 4≤7)=f:=Fin.ext rfl
    rw [id] at read
    exact ⟨cells,read⟩
  · let u : Fin 3:=⟨f.val-4,by have:=f.isLt;omega⟩
    have id : DescentRetainedRangeDigits.page u=f:=by
      apply Fin.ext
      change 4+(f.val-4)=f.val
      omega
    obtain ⟨cells,read,_⟩:=stored.spans x j u
    rw [id] at read
    exact ⟨cells,read⟩


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
