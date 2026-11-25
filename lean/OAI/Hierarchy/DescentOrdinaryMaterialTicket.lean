import OAI.Hierarchy.DescentOrdinaryRawRankFields
import OAI.Hierarchy.DescentOrdinaryDonorMaterial
import OAI.Hierarchy.DescentOrdinaryDonorRankDirectory
import OAI.Hierarchy.DescentDonorChartTables
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! The source-ticket high digit comes from the reverse-path rank table in the original donor rack. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSIMDLookup DescentPackedZip DescentHaloWalkRAM DescentSharedCableNames DescentHaloPackedRebase
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) (u : Setup) {H G M w : ℕ}
local notation "P" => breadth s.degree

/-- The existing replication directory can be pointed at the earlier reverse-rank array.
Only the chart base changes; its public row and spreading instructions are reused. -/
theorem reverse_source (R : Fin H→Fin s.degree→Option (Fin H)) (banks : DescentOrdinaryDonorRankDirectory.Banks)
    (base out : ℕ) (m : Memory w) (actual : DescentOrdinaryDonorRankDirectory.Reads R banks m)
    (static : DonorChartBook.Static H G M P base m)
    (room : DescentHaloPackedRebase.Fits (DonorChartBook.tables H G M P base banks.reverseRank) H G M w out) :
    Source (context (DonorChartBook.tables H G M P base banks.reverseRank))
      (fun h (_:Fin G)=>digest (reverseEntries s R h)) M m :=by
  apply DescentHaloPackedRebase.source _ out room
  apply DonorChartBook.ready H G M P base _ _ m static
  exact actual.reverse

def ticketLaw (seat : Seat s) (chart : Cell (chartBits s)) (sourcePath : Cell u.fieldBits) : Cell u.fieldBits :=
  let i:=sourcePath.val
  if good : 0< i ∧ i≤P then
    let p : Fin P:=⟨i-1,by omega⟩
    let v:=((encode (Packed.bits P) P).symm chart p).val
    (v*roles s+(seat.1.val*s.cap+seat.2.1.val)*11+seat.2.2.val:ℕ)
  else 0

@[simp] theorem ticket_blank (seat : Seat s) (chart : Cell (chartBits s)) : ticketLaw s u seat chart 0=0:=by
  simp [ticketLaw]

theorem ticket_hit (R : Fin H→Fin s.degree→Option (Fin H)) (host : Fin H) (p : Fin P)
    (seat : Seat s) (path : Cell u.fieldBits) (hit : path.val=p.val+1) :
    ticketLaw s u seat (digest (reverseEntries s R host)) path=
      ((Rebase.value R .rank host p*roles s+(seat.1.val*s.cap+seat.2.1.val)*11+seat.2.2.val:ℕ):Cell u.fieldBits) :=by
  have live : 0<path.val ∧ path.val≤P :=by have:=p.isLt;omega
  have back : (⟨path.val-1,by omega⟩:Fin P)=p:=by apply Fin.ext; change path.val-1=p.val;omega
  simp only [ticketLaw,dite_eq_left live,back,digest,Equiv.symm_apply_apply,field,reverseEntries]

theorem ticket_source (R : Fin H→Fin s.degree→Option (Fin H)) (host : DescentHaloPackedRebase.Headers P)
    (src : Bank) (zip : Tables) (out : ℕ) (m : Memory w)
    (seat : Seat s) (v : Fin H→Fin G→Parts s)
    (fit : DescentPackedZip.Fits zip (context host) (.lookup src .row) (chartBits s) u.fieldBits M out w)
    (enough : H*chunks G M≤ src.size)
    (rev : Source (context host) (fun h (_:Fin G)=>digest (reverseEntries s R h)) M m)
    (raw : DescentPackedColony.Reads src (fun h g=>(observations s u (v h g) seat 0:Cell u.fieldBits)) M m)
    (rom : Static zip (ticketLaw s u seat) M m) :
    Source (zip.read (context host) (.lookup src .row))
      (fun h g=>ticketLaw s u seat (digest (reverseEntries s R h)) (observations s u (v h g) seat 0:Cell u.fieldBits)) M m :=by
  exact read_data zip _ _ out fit _ (ticket_blank s u seat _) m rom _ _ rev
    (source_column src out fit.right.1 m _ enough raw)

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
