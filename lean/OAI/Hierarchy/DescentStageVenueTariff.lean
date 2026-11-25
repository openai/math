import OAI.Hierarchy.DescentVenueSlabTariff
import OAI.Hierarchy.DescentStageVenueTail
import OAI.Hierarchy.DescentVenueSlabs
import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentColumnHardware

namespace OAI
/-! # Clock and machine-size invoices for the successor inputs -/
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentPackedColony DescentSIMDLookup DescentActorRaster ProtocolRAM
open DescentStaticWordColumn (names names_seq names_mount names_scan)
noncomputable section

def tariff (k H G M D:ℕ) :=
  let r:=2^k
  let n:=H*chunks G M
  let table:=r*2^M
  let lookup:=1+13*r
  let dirs:=DescentScalarHaloPortROM.length H G M D
  (4+10*table+(4+n*(2*lookup+4))+(4+10*dirs))+
    7*(15*(table+1)+(11+4*lookup)+15*(dirs+1))

theorem price (B:Sources) (base k H G M D w:ℕ) :
    ticks B base k H G M D+7*names (program B base k H G M D w)≤tariff k H G M D :=by
  let e:=DescentPackedColumnSum.reads base 1 M (fun _ : Fin (2^k)=>1) (input B k)
  have bound:e.work≤1+13*2^k:=by
    simpa [e,Nat.mul_comm] using DescentPackedColumnSum.work_le base 1 M (fun _ : Fin (2^k)=>1) (input B k) 7
      (fun _=>show 7≤7 from le_rfl)
  have cost:=Nat.mul_le_mul_left (H*chunks G M) (show 2*e.work+4≤2*(1+13*2^k)+4 by omega)
  simp only [ticks,program,Venue.ticks,Venue.program,DescentPackedColumnSum.ticks,DescentPackedColumnSum.program,
    DescentScalarHaloPortROM.program,names_seq,names_scan,names_mount,tariff,Nat.one_mul]
  dsimp only [e] at *
  omega

end
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
