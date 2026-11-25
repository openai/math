import OAI.Hierarchy.DescentOriginalSourcePaid
import OAI.Hierarchy.DescentArgumentRowVolume
import OAI.Hierarchy.DescentSourceRectangleCosts

namespace OAI
/-! # All native prior operand-page preparation and selection at the common date volume -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentDatedOperandReadPipeline
open DescentDatedSourcePathDirectory DescentDatedOperandPages DescentHaloWalkRAM DescentArgumentWordRectangle
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor : ℕ)
local notation "W_" => v.registeredFrom prior floor
local notation "A_" => v.registeredEntry prior floor
local notation "e_" => (W_).material
local notation "fmt_" => (W_).ticket.depotShape (W_).short
local notation "d_" => (fmt_).degree
local notation "r_" => 2^v.area.k
local notation "short_" => r_*v.fundedWorkingUnit (v.argumentUnitFrom prior floor)

def originalControlRate (K : ℕ) :=depotRate K+pathRate K+columnRate K+
  (327+115*(2*K+4))+7*K*(3+K)+16384

theorem original_control_volume {S : AtomSchedule} {i : ℕ}
    (geometry : SectionPopulation W_ A_ S i)
    (rad : (W_).vector.radix=S.radix) (nonempty : 0<(W_).vector.radix)
    (J rate ratio K : ℕ)
    («fields» : count fmt_≤ K) (panel : (W_).fundedPanelUnit≤ K) (signedUnit : (W_).signedLayout.unit≤ K)
    (branch : breadth d_≤ K) (ports : breadth d_*(d_+1)≤ K)
    (loop : (breadth d_+1)*(30+4*breadth d_+4*(breadth d_*breadth d_))≤ K)
    (nodes : (W_).resolver.nodes≤ K)
    (unit : short_≤ K) (selection : scale J (22*rate)≤ K) :
    v.originalReadCharge prior floor ratio J rate≤ originalControlRate K*ratio*((W_).rowVolume v.payload) :=by
  let Z:=(W_).rowVolume v.payload
  let h:=v.payload
  obtain ⟨root,host,_,oldGrid,_,compactHost,compactGrid,_,afterGrid,rom,shared,rounding⟩:=
    geometry.native_rows h rad nonempty
  have base : (W_).operandDepotCharge ratio≤ depotRate K*ratio*Z:=
    depot «fields» panel signedUnit root host oldGrid rom shared
  have grid : (e_).oldHosts*(e_).groups≤ Z:=by
    rw [←geometry.vector.1,←geometry.vector.2];exact afterGrid
  have path := physical_path (ratio:=ratio) root host grid rounding signedUnit branch ports loop
  have rank_ : rankCost (e_).oldHosts d_ h ratio≤ columnRate K*ratio*Z:=
    path_column _ _ _ _ _ _ _ branch loop root host
  have t : ratio*(327*h+115*(2*(W_).resolver.nodes+4)*2^(h/2)*h)≤
      (327+115*(2*K+4))*ratio*Z:=by
    rw [Nat.mul_assoc _ (2^(h/2)) h]
    calc _≤ ratio*(327*Z+115*(2*K+4)*Z):=by gcongr
         _=_:=by ring
  let g:=(W_).ticketReadGeometry
  have volume : h+g.hosts*h+g.hosts*g.groups*short_≤(2+K)*Z:=
    (rows root compactHost compactGrid short_).trans (Nat.mul_le_mul_right Z (Nat.add_le_add_left unit 2))
  have reads : 7*(scale J (22*rate)*ratio*(h+g.hosts*h+g.hosts*g.groups*short_)+
      scale J (22*rate)*ratio*(2^(h/2)*h))≤7*K*(3+K)*ratio*Z:=by
    calc _≤7*(K*ratio*((2+K)*Z)+K*ratio*Z):=by gcongr
         _=_:=by ring
  have last : finalCharge h ratio≤16384*ratio*Z:=by
    unfold finalCharge
    calc _=8192*ratio*(h+2^(h/2)*h):=by ring
         _≤8192*ratio*(Z+Z):=by gcongr
         _=_:=by ring
  unfold originalReadCharge originalControlRate
  dsimp only
  calc _≤ depotRate K*ratio*Z+pathRate K*ratio*Z+columnRate K*ratio*Z+
      (327+115*(2*K+4))*ratio*Z+(7*K*(3+K)*ratio*Z+16384*ratio*Z):=by gcongr
       _=_:=by ring

/-- Both width-converting head transfers share the same current signed grid. -/
theorem original_head_volume {S : AtomSchedule} {i : ℕ} (geometry : SectionPopulation W_ A_ S i)
    (rad : (W_).vector.radix=S.radix) (nonempty : 0<(W_).vector.radix)
    (K ratio : ℕ) (work : (W_).headUnit≤ K) (signedUnit : (W_).signedLayout.unit≤ K)
    (unit : short_≤ K) :
    v.originalSourceRows prior floor v.payload ratio≤(1+5*K)*K*ratio*((W_).rowVolume v.payload) :=by
  let Z:=(W_).rowVolume v.payload
  obtain ⟨_,_,hh,_,hg,_,_,_,_,_,_,_⟩:=geometry.native_rows v.payload rad nonempty
  unfold originalSourceRows
  dsimp only
  rw [geometry.signed.2.1,geometry.signed.2.2]
  calc _≤ ratio*K*(Z+Z*(4*K+K)):=by gcongr
       _=_:=by ring

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
