import OAI.Hierarchy.DescentDatedSampledOldSocketCore
import OAI.Hierarchy.DescentDatedBroadcastWalkNumber

namespace OAI
/-! # A retained raw socket read from the original W stamp and sorted-path broadcast -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentHaloWalkRAM
open DescentSortedRoster DescentRawCablePanel DescentSIMDLookup
open scoped Classical

/-- Each of the six emitted origin digits is read from the genuinely returned W
word. A fitting field survives the packed finite-width conversion. -/
theorem old_stamp_origin_values (chart : Return) (bits : ℕ) (ordinal : Fin (breadth chart.degree))
    (block : Fin (2^chart.depth)) (oldNode : Fin chart.oldNodes) (node : Fin chart.newNodes)
    (word : Cell (chart.ordinalBits*chart.newNodes))
    (stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=
      (candidate chart ordinal block (.inl oldNode)).val+1)
    (f : Fin 6) (fits : (![1,ordinal.val,block.val,oldNode.val,0,0] f)<2^bits) :
    (readLaw chart bits node f word).val=![1,ordinal.val,block.val,oldNode.val,0,0] f :=by
  rw [at_stamp chart bits node f word _ stamp,tuple_old]
  exact Nat.mod_eq_of_lt fits

theorem sampled_old_stamped_rows_socket (g : Geometry) (v : Data g)
    (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups)
    {H : ℕ} (pitch : ℕ) (reach : Fin H→Fin g.paths→Option (Fin H)) (recv actor : Fin H)
    (chart : Return) (ordinal : Fin (breadth chart.degree)) (block : Fin (2^chart.depth))
    (oldNode : Fin chart.oldNodes) (node : Fin chart.newNodes) (word : Cell (chart.ordinalBits*chart.newNodes))
    (stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=
      (candidate chart ordinal block (.inl oldNode)).val+1)
    (read : ∀f,v.origin j f h y=readLaw chart g.digitBits node f word)
    (s root p : Fin g.paths) (x : Fin g.blocks) (peer neighbor : Fin g.degree) (first old : Fin g.cap)
    (target : Bool) (z : Ticket.SocketSeat g.blocks g.cap) (chunk : ℕ)
    (ordinalId : ordinal.val=s.val) (blockId : block.val=x.val)
    (width : max 1 (max ordinal.val block.val)<2^g.digitBits)
    (atHost : DepotRAM.Material.Route.receiver H pitch h=some recv)
    (sorted : indexed reach recv s=some actor) (visited : Gather.select reach recv root=some actor)
    (room : root.val<2^g.digitBits)
    (header : ∀f,(v.prior j f h y).val=(DescentOperandStateBanks.Pointer.cable peer.val first.val chunk).header f)
    (rows : OldSocketRows g v j h y root p x peer neighbor first old target z) :
    SampledOldSocket g (SortedInput.values g v (SortedInput.Broadcast.value g pitch reach)) j h y p x old target z :=by
  have fields (f : Fin 6) (fits : (![1,ordinal.val,block.val,oldNode.val,0,0] f)<2^g.digitBits) :
      (v.origin j f h y).val=![1,ordinal.val,block.val,oldNode.val,0,0] f :=
    (congrArg Fin.val (read f)).trans
      (old_stamp_origin_values chart g.digitBits ordinal block oldNode node word stamp f fits)
  have cause : (v.origin j 0 h y).val=1:=fields 0 (by change 1<2^g.digitBits;omega)
  have dense : (v.origin j 1 h y).val=s.val:=(fields 1 (by change ordinal.val<2^g.digitBits;omega)).trans ordinalId
  have admitted : (v.origin j 2 h y).val=x.val:=(fields 2 (by change block.val<2^g.digitBits;omega)).trans blockId
  exact sampled_old_sorted_rows_socket g v j h y root p x peer neighbor first old target z reach recv actor s
    (SortedInput.Broadcast.value g pitch reach) chunk cause dense sorted visited
    (SortedInput.Broadcast.value_at_ordinal g pitch reach h y recv actor s root atHost sorted visited room)
    admitted header rows

end Hierarchy.DescentDatedOperandReadPipeline

end OAI
