import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentFundedRoleTimeRate

namespace OAI
/-! # Exact operand charges of the final measured reset books -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentContacts DescentCommonHost DescentSIMDLookup
open DescentFundedCensus DescentVenueQuantityPlanes
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "F₀" => (v).funded
local notation "V₀" => (v).venue
local notation "Q" => (V₀).census
local notation "T" => (V₀).dense
local notation "V₁" => (V₀).next
local notation "M₀" => (v).metadata
local notation "M₁" => (M₀).chart
local notation "stop₀" => (v).finalEnd b
local notation "fund" => (v).fundedEnd b
local notation "dense" => (V₀).denseStart fund
local notation "venue" => (V₀).venueStart fund
local notation "meta" => (v).fullEnd b
local notation "actors" => (v).actor.directory ((v).middle.stop b)
local notation "P" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "key" => (⟨(P).saved,0⟩ : Bank)


variable {u} (z:u.FinalInputs)
namespace FinalInputs
open DescentHostDirectory DescentCommonPalette DescentRelativeContacts DescentColonies.SplitRAM
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
private theorem job_work_offset {n d r : ℕ} (board : NonlinearExpanders.Graph n d)
    (Ht C packet batch bits oldCap f D cap field header inputBits L M base : ℕ)
    (old stencil : Bank) (present : Expr) (work : present.work≤9) (signed : Fin (2*cap)→Bank) (root : Bool→DescentResetHostSize.Code r×Option (Fin (2^n))→Bank)
    (actor : Node Unit (Unit×Endpoint (2^n)) (rotor board).Site) :
    let io : Ports r n:=⟨.lookup old .row,Arrivals.expr base D cap inputBits L M (fun j=>.lookup (signed j) .row),
      .lookup stencil .row,fun side label=>.lookup (root side label) .row⟩
    let j:=compile (Ht:=Ht) board C packet batch bits oldCap f D cap field header io present actor
    j.first.work≤roleWork cap+2 ∧ j.second.work≤roleWork cap+2 ∧ j.present.work≤roleWork cap+2 :=by
  intro io j
  let K:=roleWork cap+2
  have read (B : Bank) : (Expr.lookup B .row).work≤K:=by change 7≤7+(2*cap)*13+2;omega
  have one : (Expr.lit 0).work≤K:=by change 1≤7+(2*cap)*13+2;omega
  have has:present.work≤K:=by change present.work≤7+(2*cap)*13+2;omega
  have relay : io.relay.work≤K :=by
    dsimp only [io]
    rw [Arrivals.work]
    dsimp [K,roleWork]
    omega
  rcases actor with ⟨side,⟨_,label⟩⟩|⟨side,t,role⟩|⟨side,⟨_,label⟩,path⟩
  · cases side <;> exact ⟨read _,by first | exact read _ | exact relay,has⟩
  · exact ⟨has,one,has⟩
  · dsimp only [j,compile]
    split
    · exact ⟨has,read _,has⟩
    · exact ⟨one,one,has⟩

local notation "rotorBits" => (v).middle.rotorBits
local notation "rootDepth" => (v).middle.rootDepth

theorem funded_work (j : Fin (Q).jobs) :
    let op:=z.jobs j
    op.first.work≤roleWork (F₀).capacity+2 ∧ op.second.work≤roleWork (F₀).capacity+2 ∧ op.present.work≤roleWork (F₀).capacity+2 :=by
  let rc:=a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
  let cols:=fun j : Fin (2*(F₀).capacity)=>rc.tapped (j.cast (congrArg (2*·) z.signedCount))
  let panel:Bank:=⟨(P).output,Nat.clog 2 ((v).actor.hosts*(v).actor.chunksPerHost)⟩
  let pages:=fun (side : Bool) (label : DescentResetHostSize.Code rootDepth×Option (Fin (2^rotorBits)))=>
    u.book.target rc.projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c) (v).middle.signedLanes (side,.inr label)
  exact job_work_offset u.atlas.board u.roots.Ht u.atlas.C u.atlas.packet u.atlas.groupDigits (Q).bits (F₀).capacity
    a.depthCut (F₀).degree (F₀).capacity u.roots.field (P).S.t (F₀).precision (F₀).donors (F₀).outputLanes
    ((F₀).signedEnd stop₀) ((F₀).primary stop₀) panel (presence (a:=a) (floor:=floor) j) (by change 9 ≤ 9; exact le_rfl) cols pages
    (ActorSetup.shapeAt u.atlas.board rootDepth u.roots.Ht (j.cast z.roleCount))

end FinalInputs
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
