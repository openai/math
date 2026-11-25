import OAI.Hierarchy.DescentDonorGatherRAM
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Actual clocks and physical controller size for the six-field donor gather -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM

def fieldWork (f : Fields) := f.raw.work+f.signed.work+f.owners.work+f.ranks.work+f.hub.work+f.fresh.work

/-- The final 44 steps in each batch expand the packed ROM entry into the true
old/arm/supply cells read by the path accumulator. -/
theorem clock_eq (t : Tables6) (f : Fields) (H J M : ℕ) :
    clocks t f H J M=8+(H*chunks J M)*(2*fieldWork f+158) := by
  unfold clocks clock fieldWork
  rw [work]
  ring

theorem clock_cost (t : Tables6) (f : Fields) (H J payload amount w factor : ℕ)
    (positive : 0<amount) (wide : 2*amount≤payload) (word : w≤factor*payload) :
    clocks t f H J (lanes payload amount)*w ≤
      factor*(8*payload+(H*payload+4*H*J*amount)*(2*fieldWork f+158)) := by
  have measure:=volume H J payload amount positive wide
  calc
    _ ≤ clocks t f H J (lanes payload amount)*(factor*payload) := Nat.mul_le_mul_left _ word
    _ ≤ _ := by
      rw [clock_eq]
      have bill:=Nat.mul_le_mul_left factor (Nat.mul_le_mul_right (2*fieldWork f+158) measure)
      nlinarith only [bill]

theorem controller (t : Tables6) (f : Fields) (rom : Banks) (out H J M w : ℕ) :
    names (program t f rom out H J M w)=322+4*fieldWork f := by
  simp only [program,DescentSIMDLookup.program,names_seq,names_scan,lookup_work,work,fieldWork]
  omega

end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
