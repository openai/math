import OAI.Hierarchy.DescentDatedMatcherPageIndex
import OAI.Hierarchy.DescentDatedBroadcastWalkNumber
import OAI.Hierarchy.DescentDatedTicketNativeOrigins

namespace OAI
/-! # The newborn ticket read from a sorted host slot and its original primitive mouth -/
namespace Hierarchy.DescentDatedOperandPages

theorem matcher_birth_index (fmt : DescentRawCablePanel.DepotRAM.Shape) {P : ℕ} (p : Fin P)
    (x : Fin fmt.blocks) (old : Fin fmt.cap) (second : Bool) (f : Fin 5) :
    matcherIndex fmt P (finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0 : Fin 3))))) f =
      (p,if second then sibling fmt x old f else anchor fmt x old 0 f) := by
  cases second <;> simp [matcherIndex]

end Hierarchy.DescentDatedOperandPages

namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open DescentHaloWalkRAM DescentSortedRoster DescentRawCablePanel DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry) (v : Data g) {H : ℕ}
variable (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups)

/-- The donor is resolved using the real inverse-ordinal broadcast. Both the
previous cable tag and the signed role come from the same original mouth. -/
theorem sampled_birth_sorted_rows_socket
    (pitch : ℕ) (reach : Fin H → Fin g.paths → Option (Fin H)) (recv donor : Fin H)
    (chart : Return) (ordinal : Fin (breadth chart.degree)) (x₁ : Fin (2^chart.depth))
    (seat : Fin chart.capacity) (party : Fin 6) (node : Fin chart.newNodes)
    (word : Cell (chart.ordinalBits*chart.newNodes))
    (stamp : ((encode chart.ordinalBits chart.newNodes).symm word node).val=
      (candidate chart ordinal x₁ (.inr (seat,party))).val+1)
    (origin : ∀f,v.origin j f h y=readLaw chart g.digitBits node f word)
    (s p : Fin g.paths) (x : Fin g.blocks) (old : Fin g.cap)
    (ordinalId : ordinal.val=s.val) (blockId : x₁.val=x.val) (seatId : seat.val=old.val)
    (width : max 2 (max ordinal.val (max x₁.val seat.val)) < 2^g.digitBits)
    (atHost : DepotRAM.Material.Route.receiver H pitch h=some recv)
    (sorted : indexed reach recv s=some donor) (livePath : Gather.select reach recv p=some donor)
    (walkRoom : p.val<2^g.digitBits)
    (B : DescentOrdinaryBorn.Spec) (arg scale prof : ℕ) (m : DescentOrdinaryBorn.Mouth)
    (live : DescentOrdinaryBorn.mouth B scale prof party arg=some m)
    (priorBits mouthBits : ℕ) (priorRoom : 1<2^priorBits) (mouthRoom : 11≤2^mouthBits)
    (header : (v.prior j 0 h y).val=(DescentOrdinaryBorn.field B priorBits 0 arg scale prof party).val)
    (ports : ∀f,(v.mouth j f h y).val=(DescentOrdinaryBorn.RolePorts.value mouthBits (some m) f).val)
    (second : Bool) (side : m.anchor.val=second.toNat)
    (z : Ticket.SocketSeat g.blocks g.cap) (mouthRole : m.rawRole=z.2.2.val)
    (issued : let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))
      (v.anchor j 4 a h y).val=Ticket.anchor true z 4) :
    let fixed:=SortedInput.values g v (SortedInput.Broadcast.value g pitch reach)
    let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))
    let raw:=finProdFinEquiv (p,Ticket.seatNo z)
    (rawKey g fixed j h y).val=Ticket.socket p true z ∧ (fixed.origin j 0 h y).val=2 ∧
      (fixed.prior j 0 h y).val=1 ∧ (fixed.mouth j 1 h y).val=z.2.2.val ∧
      (anchorChoice g fixed j h y).val=a.val+1 ∧ (fixed.origin j 1 h y).val+1=p.val+1 ∧
      ∀f,rawV g fixed j f h y=fixed.raw j f raw h y :=by
  intro fixed a raw
  have fromW:=origin_at_birth g v j h y chart ordinal x₁ seat party node word stamp origin
  have actor : (v.origin j 0 h y).val=2 := fromW 0 (by change 2<2^g.digitBits; omega)
  have dense : (v.origin j 1 h y).val=s.val :=
    (fromW 1 (by change ordinal.val<2^g.digitBits; omega)).trans ordinalId
  have block_ : (v.origin j 2 h y).val=x.val :=
    (fromW 2 (by change x₁.val<2^g.digitBits; omega)).trans blockId
  have seat_ : (v.origin j 4 h y).val=old.val :=
    (fromW 4 (by change seat.val<2^g.digitBits; omega)).trans seatId
  have path : (fixed.origin j 1 h y).val=p.val := SortedInput.Broadcast.selected_at_ordinal
    g v pitch reach j h y recv donor s p (Or.inr actor) dense atHost sorted livePath walkRoom
  have cause : (fixed.origin j 0 h y).val=2 := actor
  have kind : (fixed.prior j 0 h y).val=1 := by
    change (v.prior j 0 h y).val=1
    rw [header,DescentOrdinaryBorn.field_read B priorBits 0 arg scale prof party m live priorRoom]
    rfl
  have mouth (f : Fin 3) : (fixed.mouth j f h y).val=DescentOrdinaryBorn.RolePorts.numeral m f :=
    (ports f).trans (DescentOrdinaryBorn.RolePorts.value_live _ mouthRoom m f)
  have recorded:=DescentOrdinaryBorn.RolePorts.coordinates m
  have chosen : (anchorChoice g fixed j h y).val=a.val+1 :=
    anchor_choice_birth g fixed j h y p x old second cause kind path block_ seat_ ((mouth 0).trans (recorded.1.trans side))
  have head : (anchorV g fixed j 4 h y).val=Ticket.anchor true z 4 :=
    (congrArg Fin.val (anchorV_at g fixed j h y a chosen 4)).trans issued
  have role := (mouth 1).trans (recorded.2.1.trans mouthRole)
  have address := rawKey_at_socket g fixed j h y rfl rfl p true z cause (congrArg (·+1) path) head (fun _=>role)
  exact ⟨address,cause,kind,role,chosen,congrArg (·+1) path,fun f=>rawV_at g fixed j h y raw
    (address.trans (Ticket.socket_at p true z)) f⟩

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
