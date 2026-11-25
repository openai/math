import OAI.Hierarchy.DescentArgumentPageWordTariff
import OAI.Hierarchy.DescentOrdinaryBirthChip
import OAI.Hierarchy.DescentOrdinaryBornTariff
import OAI.Hierarchy.DescentOrdinaryRoleControlPrice

namespace OAI
/-! # The chosen donor chip, original finite birth book, and two physical receiver controls -/
namespace Hierarchy
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM DescentSixParty DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local DescentPackedColony DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM

namespace DescentOrdinaryBirthChip.Layout
theorem word_bill (L : Layout) (base w h ratio unit : ℕ) (src : Bank)
    (table : DescentRawCablePanel.DepotRAM.totalBits L.format*L.lanes≤h/2) (fill : h≤L.lanes*unit) (bus : w≤ratio*h) :
    ((L.phase base src w).ticks+7*names (L.phase base src w).program)*w≤
      1024*ratio*(0+1)*(h+L.hosts*h+L.hosts*L.groups*unit)+1024*ratio*(0+1)*2^(h/2)*h :=by
  apply DescentDatedSeedStartup.page_scan_words L.hosts L.groups L.lanes unit h w ratio 0 1024 _ fill bus
  have original:=L.charged h w base src table
  change L.ticks+7*names (L.program w base src)≤_
  change L.ticks+7*names (L.program w base src)≤750+115*2^(h/2)+159*(L.hosts*chunks L.groups L.lanes) at original
  omega
end DescentOrdinaryBirthChip.Layout

namespace DescentOrdinaryBorn.Chart
theorem word_bill (B : Chart) (base w h ratio unit : ℕ) (src : Bank)
    (table : (B.chipBits*1+B.chipBits)*B.lanes≤h/2) (fill : h≤B.lanes*unit) (bus : w≤ratio*h) :
    (B.ticks src base+7*DescentStaticWordColumn.names (B.program src base w))*w≤
      2048*ratio*(B.fields+1)*(h+B.hosts*h+B.hosts*B.groups*unit)+
        2048*ratio*(B.fields+1)*2^(h/2)*h :=by
  apply DescentDatedSeedStartup.page_scan_words B.hosts B.groups B.lanes unit h w ratio B.fields 2048 _ fill bus
  obtain ⟨time,text⟩:=B.tariff src base w
  have static :=Nat.pow_le_pow_right (n:=2) (by decide) table
  have bound : B.bookWords≤(B.fields+1)*(2*2^(h/2)) :=by
    unfold bookWords
    rw [Nat.add_comm 1 B.fields]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ static)
  change _≤2048*((B.fields+1)*(1+B.rows)+(B.fields+1)*2^(h/2))
  unfold cpu at time
  unfold textCost at text
  nlinarith only [time,text,bound,Nat.zero_le B.fields,Nat.zero_le B.rows,
    Nat.zero_le (B.fields*B.rows),Nat.zero_le (2^(h/2)),Nat.zero_le (B.fields*2^(h/2))]

end DescentOrdinaryBorn.Chart

namespace DescentOrdinaryAtomFieldRAM.RoleControl.Layout
theorem word_bill (L : RoleControl.Layout) (P : Ports L.walks) (old : Fin L.blocks→Bank)
    (w h ratio unit : ℕ) (fill : h≤L.lanes*unit) (bus : w≤ratio*h)
    (lookup : (L.roleBits*L.nodes)*L.lanes≤h/4)
    (assembly : (L.countBits*L.donors+L.countBits)*L.lanes≤h/4)
    (small : L.chunkBits≤h/4) (pages : L.count≤2^(h/4)) :
    (L.ticks P old+7*names (L.program w P old))*w≤
      4096*ratio*(L.donors+1)*(h+L.hosts*h+L.hosts*L.groups*unit)+
        4096*ratio*(L.donors+1)*2^(h/2)*h :=by
  apply DescentDatedSeedStartup.page_scan_words L.hosts L.groups L.lanes unit h w ratio L.donors 4096 _ fill bus
  have original:=L.syntax_clock P old w
  have tables:=L.immutable_size lookup assembly small pages
  change _≤4096*((L.donors+1)*(1+L.rows)+(L.donors+1)*2^(h/2))
  nlinarith only [original,tables,Nat.zero_le L.rows,Nat.zero_le L.donors,Nat.zero_le (L.rows*L.donors),
    Nat.zero_le (L.donors*2^(h/2)),Nat.zero_le (2^(h/2))]
end DescentOrdinaryAtomFieldRAM.RoleControl.Layout
end Hierarchy

end OAI
