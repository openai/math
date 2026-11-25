import OAI.Hierarchy.DescentDatedTicketWords
import OAI.Hierarchy.DescentDatedNativeTicketRead
import OAI.Hierarchy.DescentDatedTicketResolve

namespace OAI
/-! # Resolving all eight values returned by the native ticket expressions -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks
open DescentPriorOperandColumns DescentOrdinaryLocalFragment ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable (g : Geometry) (v : Data g) (s : Sources g) {w floor : ℕ} (m : Memory w)
  (stored : Recorded g s v floor m) (space : endAddress g floor < 2^w)
  (lanes : 0 < g.lanes) (width : g.resultBits*g.lanes ≤ w)
  (j : Fin g.jobs) (h : Fin g.hosts) (y : Fin g.groups)
local notation "out" => readTicket g s (floor:=floor) m j h y

include stored space lanes width in
theorem posted_read (word : Fin 8→ℕ) (equal : ticketAt g v j h y=word) (fits : ∀f,word f < 2^g.resultBits) :
    out=word :=by
  funext f
  exact (ticket_read_of_lt g v s m stored space lanes width j h y f (by rw [equal];exact fits f)).trans (congrFun equal f)

variable {size : ℕ} (priorPeer priorSerial piece : ℕ)
  (earlier : ∀f,(Pointer.cable priorPeer priorSerial piece).header f<2^(size+2))
  (grain : Cell (size+2))
local notation "key" => resolve (Ticket.compiled out grain (Pointer.cable priorPeer priorSerial piece) earlier)

include stored space lanes width in
theorem captured_key (donor ordinal role start peer : ℕ) (second marked : Bool)
    (visible : ticketAt g v j h y=postedVector donor (!second) second marked start peer ordinal role)
    (fits : ∀f,postedVector donor (!second) second marked start peer ordinal role f < 2^g.resultBits)
    (donorFit : donor<2^(size+2)) (nameFit : 11*ordinal+role<2^(size+2)) :
    key=(if second then Key.second else Key.first) donor 0 (11*ordinal+role) piece :=by
  rw [posted_read g v s m stored space lanes width j h y _ visible fits]
  have pieceFit : piece<2^(size+2):=earlier 3
  have nameValue : (11*(ordinal:Cell (size+2))+(role:Cell (size+2))).val=11*ordinal+role := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using (Fin.val_cast_of_lt nameFit)
  cases second <;> simp [postedVector,Ticket.compiled,Ticket.side,Side.withHeader,Pointer.header,route,resolve,
    Fin.val_cast_of_lt donorFit,nameValue]

include stored space lanes width in
theorem survivor_key (donor ordinal role start peer : ℕ) (marked : Bool)
    (visible : ticketAt g v j h y=postedVector donor false false marked start peer ordinal role)
    (fits : ∀f,postedVector donor false false marked start peer ordinal role f < 2^g.resultBits) :
    key=resolve (Public.fragment marked (peer:Cell (size+2)) (start:Cell (size+2))
      (⟨piece,show piece<2^(size+2) from earlier 3⟩:Cell (size+2)) grain) :=by
  rw [posted_read g v s m stored space lanes width j h y _ visible fits]
  cases marked <;> simp [postedVector,Ticket.compiled,Ticket.side,Side.withHeader,Pointer.header,route,resolve,Public.fragment]

include stored space lanes width in
theorem captured_physical (sameWidth : g.resultBits=size+2) (donor ordinal role start peer : ℕ) (second marked : Bool)
    (visible : ticketAt g v j h y=postedVector donor (!second) second marked start peer ordinal role)
    (donorFit : donor<2^(size+2)) (nameFit : 11*ordinal+role<2^(size+2)) :
    key=(if second then Key.second else Key.first) donor 0 (11*ordinal+role) piece :=by
  apply captured_key g v s m stored space lanes width j h y priorPeer priorSerial piece earlier grain donor ordinal role
    start peer second marked visible _ donorFit nameFit
  intro f
  rw [sameWidth]
  have unit : 1 < 2^(size+2):=Nat.one_lt_pow (by omega) (by decide : 1 < 2)
  cases second <;> cases marked <;> fin_cases f <;> simp [postedVector] <;> omega

include stored space lanes width in
theorem survivor_physical (sameWidth : g.resultBits=size+2) (donor ordinal role start peer : ℕ) (marked : Bool)
    (visible : ticketAt g v j h y=postedVector donor false false marked start peer ordinal role) :
    key=resolve (Public.fragment marked (peer:Cell (size+2)) (start:Cell (size+2))
      (⟨piece,show piece<2^(size+2) from earlier 3⟩:Cell (size+2)) grain) :=by
  have field (f : Fin 8) : out f =
      ((postedVector donor false false marked start peer ordinal role f:ℕ):Cell (size+2)).val:=by
    rw [ticket_read g v s m stored space lanes width j h y f,visible,sameWidth]
  cases marked <;> simp [Ticket.compiled,Ticket.side,Side.withHeader,Pointer.header,route,resolve,Public.fragment,
    field,postedVector]

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
