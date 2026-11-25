import OAI.Hierarchy.DescentRetainedHubFlag
import OAI.Hierarchy.DescentPhysicalTrunkSibling
import OAI.Hierarchy.DescentPhysicalResetRankProgram
import OAI.Hierarchy.DescentResetTrunkOperandPrefix

namespace OAI
/-! # Retained operands use the chronological arrival shelf at the actual relay -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentResetTrunkCompactPointer DescentDyadicSpan
open scoped Fin.CommRing
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput)
local notation "front" => v.front
local notation "C" => v.setup
local notation "A" => v.receiver

def incomingTicketBank (base x d : ℕ) :=DescentResetSourceTicketBank.column (v.pairEnd base)
  v.ticketBits (A).lanes (A).hosts (A).groups (A).candidates x ((front).signedQueries/2+d)

def incomingTicketRow (base x d : ℕ) : Expr :=
  let floor:=v.actorEnd base
  let n:=(front).newHosts*chunks (front).peer.groups (front).peer.lanes
  DescentResetTrunkGather.issue n (DescentResetTrunkCompactGather.rows ((front).mixed floor)
    (front).newHosts (front).peer.groups (front).peer.lanes) (v.incomingTicketBank base x d)

def ticketColumn (d : Fin (C).strip) : Fin (C).inputs:=⟨6+(C).strip+d.val,by
  have ht:=d.isLt
  change _<6+2*(C).strip
  omega⟩

@[simp] theorem ticket_width (d : Fin (C).strip) : (C).width (v.ticketColumn d)=(C).ticketBits:=by
  have h₁ : ¬ 6 + (C).strip + d.val < 5 := by omega
  have h₂ : 6 + (C).strip + d.val ≠ 5 := by omega
  have h₃ : ¬ 6 + (C).strip + d.val < 6 + (C).strip := by omega
  simp only [DescentResetOperandSetup.Chart.width,ticketColumn,h₁,h₂,h₃,ite_false]

/-- The bank read at the matched sibling uses precisely one existing lane-wise
width cast. The ticket starts at zero in the original incoming order. -/
def retainedTicket (base : ℕ) (x : Fin (C).placement.blocks) (d : Fin (C).strip) : Expr:=
  DescentOperandInputCast.expr (C).width (C).fieldBits (C).sourceWidth (C).lanes
    ((C).publicEnd (v.operandFloor base)) (v.ticketColumn d) (v.incomingTicketRow base x.val d.val)

/-- Previous terminal hub status is the complement of the scalar trunk mark.
Both receiver hosts share the marker. Empty or truncated last rows retain the
canonical packed padding. -/
def retainedHub (base : ℕ) (_ : Fin (C).placement.blocks) : Expr:=
  let f:=v.actorEnd base
  DescentRetainedHubFlag.hub (front).newHosts (front).peer.groups (front).peer.lanes (front).metaBits (C).fieldBits
    ((front).peer.endAddress ((front).peers f)) ((front).trunkHeader f)

theorem hub_work (base : ℕ) (x : Fin (C).placement.blocks) : (v.retainedHub base x).work=26:=rfl

theorem ticket_work (base : ℕ) (x : Fin (C).placement.blocks) (d : Fin (C).strip) :
    (v.retainedTicket base x d).work≤40:=by
  change 34≤40
  decide

theorem same_ticket_bank (u : v.RankInputs) (base : ℕ) (x : Fin (A).blocks) (d : Fin (C).strip)
    (room : (front).signedQueries/2+d.val<(A).candidates) :
    v.incomingTicketBank base x.val d.val=(v.rankBook u base).oldBank x ⟨_,room⟩:=rfl

/-- The previously printed sibling address works at the later chronology bank.
No packed search or global name is required to look up the other endpoint. -/
theorem incoming_ticket_rows (base : ℕ) (s : (front).Scene) {w N : ℕ}
    (safe : (front).SceneRoom (v.actorEnd base) s w) (m now : Memory w)
    (name : Fin N→Fin (front).peer.hosts) (other : Fin N→Option (Fin N))
    (live : N≤(front).newHosts) (active : N≤ s.inverse.size)
    (census : Measured ((front).trunkBanks (v.actorEnd base) s) name other
      (((front).received (v.actorEnd base) s safe).image m))
    (trunk : v.trunkEnd base<2^w) (limit : ℕ) (bound : limit<2^w) (space : (front).gathered (v.actorEnd base)≤limit)
    (x d : ℕ) (fit : (v.incomingTicketBank base x d).Fits w limit)
    (wide : (front).newHosts*chunks (front).peer.groups (front).peer.lanes≤(v.incomingTicketBank base x d).size)
    {b : ℕ} (value : Fin (front).newHosts→Fin (front).peer.groups→Cell b)
    (read : Reads (v.incomingTicketBank base x d) value (front).peer.lanes now)
    (kept : ∀p : Row (front).newHosts (front).peer.groups (front).peer.lanes,
      let i:=DescentResetTrunkCompactGather.rows ((front).mixed (v.actorEnd base)) (front).newHosts
        (front).peer.groups (front).peer.lanes+(row _ _ _ p).val
      now i=(((front).trunkScene (v.actorEnd base) s safe).image m) i) :
    (v.incomingTicketRow base x d).Fits w limit ∧ Source (v.incomingTicketRow base x d)
      (fun h g=>(pointer live other h).elim 0 (fun t=>value t g)) (front).peer.lanes now :=
  (front).trunk_sibling_read (v.actorEnd base) s safe m now rfl name other live active census trunk limit
    bound space (v.incomingTicketBank base x d) value fit wide read kept

private theorem source_cast {a b w H G M : ℕ} (e : a=b) (src : Expr)
    (value : Fin H→Fin G→Cell a) (m : Memory w) (read : Source src value M m) :
    Source src (fun h g=>Fin.cast (congrArg (fun z=>2^z) e) (value h g)) M m:=by
  subst b
  exact read

theorem retained_ticket_source (base : ℕ) (x : Fin (C).placement.blocks) (d : Fin (C).strip) {w H G : ℕ}
    (m : Memory w) (value : Fin H→Fin G→Cell (C).ticketBits)
    (safe : (v.incomingTicketRow base x.val d.val).Fits w ((C).publicEnd (v.operandFloor base)))
    (source : Source (v.incomingTicketRow base x.val d.val) value (C).lanes m)
    (room : (C).casts (v.operandFloor base)<2^w) :
    (v.retainedTicket base x d).Fits w ((C).casts (v.operandFloor base)) ∧
      Source (v.retainedTicket base x d) (fun h g=>((value h g).val:Cell (C).fieldBits)) (C).lanes
        (((C).castBook ((C).publicEnd (v.operandFloor base)) w).image m):=by
  let c:=v.ticketColumn d
  let casted (h : Fin H) (g : Fin G) : Cell ((C).width c):=Fin.cast (congrArg (fun z=>2^z) (v.ticket_width d).symm) (value h g)
  have same : Source (v.incomingTicketRow base x.val d.val) casted (C).lanes m:=by
    exact source_cast (v.ticket_width d).symm _ _ m source
  exact DescentOperandInputCast.issued (C).width (C).fieldBits (C).sourceWidth (C).lanes
    ((C).publicEnd (v.operandFloor base)) c _ m casted (C).width_le safe same room

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
