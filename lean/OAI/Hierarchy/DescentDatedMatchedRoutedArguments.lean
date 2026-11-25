import OAI.Hierarchy.DescentDatedMatchedTicketFlags
import OAI.Hierarchy.DescentDatedTicketPreparationTotal

namespace OAI
/-! # Eight native ticket outputs feed the actual scalar operand key and its public grain -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedZip DescentSIMDLookup DescentPackedColony
open DescentRawCablePanel DescentHaloWalkRAM DescentOperandStateBanks DescentOperandVectorArena
open DescentSharedCableNames DescentPriorOperandColumns DescentDatedOperandReadPipeline DescentDatedOperandCoordinates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor w : ℕ) (cs : v.SignedChart)
    (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "l₀" => v.resolver
local notation "g₀" => v.ticketReadGeometry
local notation "end₀" => v.preparedUntil floor
local notation "vec₀" => v.vectorStart floor
local notation "route₀" => v.routedStart floor
local notation "C₀" => (A.directory v floor mat).refs
variable (blocks : v.resolver.blocks=v.material.blocks) (pg : Fin (7*v.vector.operands))
local notation "src₀" => v.nativeTicketExpr floor cs A mat shape blocks
local notation "prep₀" => v.nativeTicketPreparation floor w cs A mat shape blocks pg

theorem routed_native_ticket (m : Memory w) (books : Books (l₀)) (typed : BookPointers books)
    (words : Fin (l₀).jobs → Fin (l₀).hosts → Fin (l₀).groups → Fin 8 → ℕ)
    (purchased : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize)
    (admit : v.TicketAdmission floor w cs A mat pg)
    (space : v.endAddress floor<2^w) (wide : (l₀).lanes*DescentPackedOperand.unit (l₀).size≤w/2)
    (pages : ∀x p,Reads ((v.nativeArgs floor).previous x p) (books x p) (l₀).lanes (((C₀).phase w vec₀).image m))
    (held : ∀j f,Held (g₀) end₀ ((prep₀).image (((C₀).phase w vec₀).image m)) (src₀ j f)
      (fun h k=>(words j h k f:Cell ((l₀).size+2))))
    (flags : ∀j h k,Ticket.Flags (words j h k))
    (digits : ∀j h k,11*(v.ticketRoles words j 1 h k).val+(v.ticketRoles words j 2 h k).val<2^((l₀).size+2)) :
    let raw:=ofBooks books typed (fun j h k=>DescentDatedPublicGrain.withGrain v.chosenGrain (v.ticketSides words j h k))
      (v.ticketRoles words) digits
    ∀j : Fin (l₀).jobs, Reads (Banks.wordBank (l₀) (v.normalizedEnd floor) j)
      (fun h k=>DescentPackedOperand.word ((raw j).compiled h k)) (l₀).lanes
      ((v.routedArguments floor (C₀) (src₀) (prep₀) shape space wide).image m) :=by
  obtain ⟨_,_,toOut,toKeys,last⟩:=v.routed_order floor
  have paid:=v.grain_after_sources floor purchased
  have cap : end₀<2^w:=by rw [←paid]; exact toOut.trans_lt (toKeys.trans_lt (last.trans_lt space))
  let input:=((C₀).phase w vec₀).image m
  have run:=v.ticket_preparation_any floor w cs A mat shape blocks pg admit cap input
  have lane : 0<(l₀).lanes:=by rw [shape.lanes]; exact admit.lanes
  exact v.routed_keys_of_sources floor (C₀) (src₀) (prep₀) shape space wide m books typed
    (v.ticketSides words) (v.ticketRoles words) digits lane pages
    (fun i hi=>run.1.frame i (.inl hi)) (fun j f=>by rw [paid]; exact run.2 j f)
    (v.ticket_target_sources words ((prep₀).image input) (src₀) end₀ held flags)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
