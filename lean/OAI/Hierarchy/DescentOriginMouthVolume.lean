import OAI.Hierarchy.DescentRegisteredEntryPaid
import OAI.Hierarchy.DescentArgumentRowVolume

namespace OAI
/-! # Shared row and half-word budget for the original returning occurrence and newborn mouth -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler.TerminalScale DescentDatedAddressBook
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor : ℕ)

def originRate (K : ℕ) :=
  2600*(K+1)+(160+300*K)*(1+K)+115*(4+K)+(109+230*(1+K*6))+K*(3+K)

theorem origin_mouth_volume {S : DescentCompiler.AtomSchedule} {i : ℕ}
    (geometry : SectionPopulation (v.registeredFrom prior floor) (v.registeredEntry prior floor) S i)
    (rad : (v.registeredFrom prior floor).vector.radix=S.radix)
    (nonempty : 0<(v.registeredFrom prior floor).vector.radix)
    (J a K ratio : ℕ) (rCap : 2^v.area.k≤K) (lows : v.vector.lows≤K) (nodes : v.resolver.nodes≤K)
    (room : 2^v.area.k*v.fundedWorkingUnit (v.argumentUnitFrom prior floor)≤K)
    (factors : scale J (20*a)≤K) :
    v.originMouthCharge prior floor ratio J a≤originRate K*ratio*((v.registeredFrom prior floor).rowVolume v.payload) :=by
  let W:=v.registeredFrom prior floor
  let h:=v.payload
  let Z:=W.rowVolume h
  let H:=v.vector.hosts*v.vector.lows
  let G:=v.vector.groups
  let r:=2^v.area.k
  let u:=r*v.fundedWorkingUnit (v.argumentUnitFrom prior floor)
  obtain ⟨start,old,_,_,_,host,items,_,groups,table,_,_⟩:=geometry.native_rows h rad nonempty
  have hcap : H*h≤Z:=by change W.vector.hosts*W.vector.lows*h≤Z;rw [←geometry.resolver.1];exact host
  have count : H*G≤Z:=by
    change W.vector.hosts*W.vector.lows*W.vector.groups≤Z
    rw [←geometry.resolver.1,←geometry.resolver.2];exact items
  have bornH : W.bornBook.hosts*h≤Z:=by rw [geometry.born.1];exact old
  have bornG : W.bornBook.hosts*G≤Z:=by
    change W.bornBook.hosts*W.vector.groups≤Z
    rw [geometry.born.1,←geometry.vector.1];exact groups
  have cleanup : (109+115*((1+v.resolver.nodes*6)*(2*2^(h/2))))*h=
      109*h+230*(1+v.resolver.nodes*6)*(2^(h/2)*h):=by ring
  unfold originMouthCharge
  change ratio*(2600*(v.vector.lows+1)*h+(160+300*r)*(H*h+H*G*u)+115*((4+r)*2^(h/2))*h+
    (109+115*((1+v.resolver.nodes*6)*(2*2^(h/2))))*h)+
    (ratio*scale J (20*a))*(h+(W.bornBook.hosts*h+W.bornBook.hosts*G*u)+2^(h/2)*h)≤_
  rw [cleanup, ← Nat.mul_assoc 115 (4+r), Nat.mul_assoc (115*(4+r))]
  calc _≤ratio*(2600*(K+1)*Z+(160+300*K)*(Z+Z*K)+115*(4+K)*Z+
          (109*Z+230*(1+K*6)*Z))+(ratio*K)*(Z+(Z+Z*K)+Z):=by gcongr
       _=_:=by unfold originRate;ring

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
