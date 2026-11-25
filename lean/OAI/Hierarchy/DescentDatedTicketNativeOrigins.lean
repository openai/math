import OAI.Hierarchy.DescentDatedTicketOriginRows
import OAI.Hierarchy.DescentOrdinaryBornRoleNumerals

namespace OAI
/-! # The native socket of a live newborn operand -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentSIMDLookup DescentDatedOperandCoordinates DescentPacking.PackedMatch.Local.Stage
open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open scoped Classical
noncomputable section

variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups)

/-- The two serializations of a newborn primitive occurrence give its previous cable
tag and the original eleven-way raw role, from the very same mouth. -/
theorem birth_port_fields (B : DescentOrdinaryBorn.Spec) (bits : ℕ) (arg z prof : ℕ) (party : Fin 6)
    (m : DescentOrdinaryBorn.Mouth) (live : DescentOrdinaryBorn.mouth B z prof party arg=some m)
    (space : 11≤2^bits)
    (prior : (v.prior j 0 h k).val=(DescentOrdinaryBorn.field B bits 0 arg z prof party).val)
    (mouth : ∀f,(v.mouth j f h k).val=(DescentOrdinaryBorn.RolePorts.value bits
      (DescentOrdinaryBorn.mouth B z prof party arg) f).val) :
    (v.prior j 0 h k).val=1 ∧ (v.mouth j 0 h k).val=m.anchor.val ∧ (v.mouth j 1 h k).val=m.rawRole := by
  constructor
  · rw [prior,DescentOrdinaryBorn.field_read B bits 0 arg z prof party m live (by change 1<2^bits; omega)]
    rfl
  · constructor
    · rw [mouth,live,DescentOrdinaryBorn.RolePorts.value_live bits space]
      exact (DescentOrdinaryBorn.RolePorts.coordinates m).1
    · rw [mouth,live,DescentOrdinaryBorn.RolePorts.value_live bits space]
      exact (DescentOrdinaryBorn.RolePorts.coordinates m).2.1

/-- The same live first seat and party supply the previous cable pointer and the
three measured mouth words. A unique native predecessor ordinal determines the donor. -/
theorem born_origin_rows (R : Return) (walk : Fin (DescentHaloWalkRAM.breadth R.degree))
    (block : Fin (2^R.depth)) (seat : Fin R.capacity) (party : Fin 6) (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes))
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R walk block (.inr (seat,party))).val+1)
    (origin : ∀f,v.origin j f h k=readLaw R g.digitBits node f word)
    (p q : Fin g.paths) (x : Fin g.blocks) (old : Fin g.cap)
    (rootId : walk.val=q.val) (blockId : block.val=x.val) (seatId : seat.val=old.val)
    (wide : max 2 (max walk.val (max block.val seat.val))<2^g.digitBits)
    (donor : Fin g.hosts)
    (reaching : Fin g.paths→Option (Fin g.hosts)) (reached : reaching q=some donor)
    (unique : ∀i,reaching i=some donor→i=p)
    (B : DescentOrdinaryBorn.Spec) (bits arg scale prof : ℕ) (m : DescentOrdinaryBorn.Mouth)
    (live : DescentOrdinaryBorn.mouth B scale prof party arg=some m) (space : 11≤2^bits)
    (prior : (v.prior j 0 h k).val=(DescentOrdinaryBorn.field B bits 0 arg scale prof party).val)
    (mouth : ∀f,(v.mouth j f h k).val=(DescentOrdinaryBorn.RolePorts.value bits
      (DescentOrdinaryBorn.mouth B scale prof party arg) f).val)
    (second : Bool) (sideId : m.anchor.val=second.toNat)
    (z : Ticket.SocketSeat g.blocks g.cap) (role : m.rawRole=z.2.2.val)
    (issued : let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))
      (v.anchor j 4 a h k).val=Ticket.anchor true z 4) :
    (rawKey g v j h k).val=Ticket.socket p true z ∧ (v.origin j 0 h k).val=2 ∧
      (v.prior j 0 h k).val=1 ∧ (v.mouth j 1 h k).val=z.2.2.val ∧
      (anchorChoice g v j h k).val=(finProdFinEquiv (p,finProdFinEquiv (x,
        finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))).val+1 ∧
      (v.origin j 1 h k).val+1=p.val+1 := by
  have origin_:=origin_at_birth g v j h k R walk block seat party node word stamp origin
  have cause : (v.origin j 0 h k).val=2:=origin_ 0 (by change 2<2^g.digitBits; omega)
  have root_ : (v.origin j 1 h k).val=p.val:=(origin_ 1 (by change walk.val<2^g.digitBits; omega)).trans
    (rootId.trans (congrArg Fin.val (unique q reached)))
  have block_ : (v.origin j 2 h k).val=x.val:=(origin_ 2 (by change block.val<2^g.digitBits; omega)).trans blockId
  have seat_ : (v.origin j 4 h k).val=old.val:=(origin_ 4 (by change seat.val<2^g.digitBits; omega)).trans seatId
  obtain ⟨kind,side,role_⟩:=birth_port_fields g v j h k B bits arg scale prof party m live space prior mouth
  have row:=anchor_choice_birth g v j h k p x old second cause kind root_ block_ seat_ (side.trans sideId)
  have head: (anchorV g v j 4 h k).val=Ticket.anchor true z 4 :=
    (congrArg Fin.val (anchorV_at g v j h k _ row 4)).trans issued
  have mouth_:=role_.trans role
  exact ⟨rawKey_at_socket g v j h k rfl rfl p true z cause (congrArg (·+1) root_) head
    (fun _=>mouth_),cause,kind,mouth_,row,congrArg (·+1) root_⟩

theorem born_origin_socket (R : Return) (walk : Fin (DescentHaloWalkRAM.breadth R.degree))
    (block : Fin (2^R.depth)) (seat : Fin R.capacity) (party : Fin 6) (node : Fin R.newNodes)
    (word : Cell (R.ordinalBits*R.newNodes))
    (stamp : ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R walk block (.inr (seat,party))).val+1)
    (origin : ∀f,v.origin j f h k=readLaw R g.digitBits node f word)
    (p q : Fin g.paths) (x : Fin g.blocks) (old : Fin g.cap)
    (rootId : walk.val=q.val) (blockId : block.val=x.val) (seatId : seat.val=old.val)
    (wide : max 2 (max walk.val (max block.val seat.val))<2^g.digitBits)
    (donor : Fin g.hosts)
    (reaching : Fin g.paths→Option (Fin g.hosts)) (reached : reaching q=some donor)
    (unique : ∀i,reaching i=some donor→i=p)
    (B : DescentOrdinaryBorn.Spec) (bits arg scale prof : ℕ) (m : DescentOrdinaryBorn.Mouth)
    (live : DescentOrdinaryBorn.mouth B scale prof party arg=some m) (space : 11≤2^bits)
    (prior : (v.prior j 0 h k).val=(DescentOrdinaryBorn.field B bits 0 arg scale prof party).val)
    (mouth : ∀f,(v.mouth j f h k).val=(DescentOrdinaryBorn.RolePorts.value bits
      (DescentOrdinaryBorn.mouth B scale prof party arg) f).val)
    (second : Bool) (sideId : m.anchor.val=second.toNat)
    (z : Ticket.SocketSeat g.blocks g.cap) (role : m.rawRole=z.2.2.val)
    (issued : let a:=finProdFinEquiv (p,finProdFinEquiv (x,finProdFinEquiv (old,(if second then 2 else 0:Fin 3))))
      (v.anchor j 4 a h k).val=Ticket.anchor true z 4) :
    (rawKey g v j h k).val=Ticket.socket p true z ∧ (v.origin j 0 h k).val=2 ∧
      (v.prior j 0 h k).val=1 ∧ (v.mouth j 1 h k).val=z.2.2.val := by
  obtain ⟨word_,cause,kind,mouth_,_,_⟩:=born_origin_rows g v j h k R walk block seat party node word stamp origin p q x old
    rootId blockId seatId wide donor reaching reached unique B bits arg scale prof m live space prior mouth second sideId z role issued
  exact ⟨word_,cause,kind,mouth_⟩


end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
