import OAI.Hierarchy.DescentDatedNativeTicketRead

namespace OAI
/-! # The old private, external pin, and empty arms of the native ticket program -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip

variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups)

theorem private_rank (p : Fin g.paths) (actor : (v.origin j 0 h y).val=1)
    (kind : (v.prior j 0 h y).val=0) (path : (v.origin j 1 h y).val=p.val) :
    rankV g v j 0 h y=v.rank p h y :=by
  apply DescentResetStemMux.pick_actor
    (localLaw g.paths g.digitBits 0 (fun i => rankInputs g v j i h y)) (fun t => v.rank t h y) p
  simpa [localLaw,rankInputs,actor,kind,path] using (digit_at (C:=g.paths) (n:=p.val+1) p.isLt)

theorem private_ticket (p : Fin g.paths) (rank block : ℕ)
    (actor : (v.origin j 0 h y).val=1) (kind : (v.prior j 0 h y).val=0)
    (path : (v.origin j 1 h y).val=p.val) (old : (v.origin j 2 h y).val=block)
    (read : (v.rank p h y).val=rank+1) :
    ticketAt g v j h y=![rank*g.blocks+block,0,0,0,0,0,0,0] :=by
  unfold ticketAt
  rw [actor,kind,private_rank g v j h y p actor kind path,read,old]
  apply Ticket.private_word

theorem missing_private (p : Fin g.paths) (actor : (v.origin j 0 h y).val=1)
    (kind : (v.prior j 0 h y).val=0) (path : (v.origin j 1 h y).val=p.val)
    (read : (v.rank p h y).val=0) : ticketAt g v j h y=fun _=>0 :=by
  unfold ticketAt
  rw [actor,kind,private_rank g v j h y p actor kind path,read]
  simp [Ticket.fields]

theorem pin_ticket (kind : (v.prior j 0 h y).val=2) : ticketAt g v j h y=fun _=>0 :=by
  unfold ticketAt
  rw [kind]
  apply Ticket.pin

theorem empty_ticket (actor : (v.origin j 0 h y).val=0) : ticketAt g v j h y=fun _=>0 :=by
  unfold ticketAt
  rw [actor]
  apply Ticket.no_actor

end Hierarchy.DescentDatedOperandReadPipeline

end OAI
