import OAI.Hierarchy.DescentOrdinaryRasterReturn
import OAI.Hierarchy.DescentVenueQuantityAny

namespace OAI
/-! # Padded ordinary successor census after the original old-actor and six-role records -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentVenueQuantityPlanes DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
structure Sources where
  paid : Bank
  alive : Bank
  count : Bank
variable (d:Dims)(B:Sources)(base:ℕ)
def fund:=State.layout d (first d base) B.paid B.count (inverse d base)
def seen:=State.layout (actor d) (second d base) B.alive B.count (inverse d base)
def identityColumn (w:ℕ):NativePhase w:=
  ⟨DescentStaticWordColumn.program w base id d.hosts,4+10*d.hosts,
    fun m=>DescentStaticWordColumn.image base id m d.hosts,@DescentStaticWordColumn.cheap _ _ _ _⟩
def phase (w:ℕ):NativePhase w:=
  ((identityColumn d base w).seq (DescentVenueQuantityPlanes.phase d (fund d B base) w)).seq
    (DescentVenueQuantityPlanes.phase (actor d) (seen d B base) w)

structure Room (used w:ℕ):Prop where
  firstFit:DescentVenueQuantityPlanes.Room d (fund d B base) used w
  secondFit:DescentVenueQuantityPlanes.Room (actor d) (seen d B base) used w
  column:base+d.hosts<2^w

variable {used w:ℕ}
theorem Room.observed (space:Room d B base used w){actual:ℕ}(within:actual≤d.hosts):
    Room d B base actual w:=by
  have size:actual≤(inverse d base).size:=within.trans (Nat.le_pow_clog (by decide) _)
  have word:actual<2^w:=within.trans_lt ((Nat.le_add_left d.hosts base).trans_lt space.column)
  exact ⟨{space.firstFit with inverseSize:=size,usedFit:=word},
    {space.secondFit with inverseSize:=size,usedFit:=word},space.column⟩

theorem any (m:Memory w)(space:Room d B base used w):
    (phase d B base w).Runs m ∧ ∀a,a<base ∨ roof d base≤a→(phase d B base w).image m a=m a:=by
  let ids:=identityColumn d base w
  let load:=DescentVenueQuantityPlanes.phase d (fund d B base) w
  let bits:=DescentVenueQuantityPlanes.phase (actor d) (seen d B base) w
  have ir:ids.Runs m:=DescentStaticWordColumn.mount base d.hosts id m space.column
  obtain ⟨lr,lf⟩:=DescentVenueQuantityPlanes.any d (fund d B base) (ids.image m) space.firstFit
  obtain ⟨br,bf⟩:=DescentVenueQuantityPlanes.any (actor d) (seen d B base) (load.image (ids.image m)) space.secondFit
  have low:base+d.hosts≤first d base:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have mid:first d base ≤ second d base:=by rw [second,State.shift];omega
  have last:second d base≤roof d base:=by rw [roof,State.shift];omega
  have paidEnd:(fund d B base).out+State.newRows d ≤ second d base:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have seenEnd:(seen d B base).out+State.newRows (actor d)≤roof d base:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  refine ⟨(ids.seq load).seq_runs bits m (ids.seq_runs load m ir lr) br,?_⟩
  intro a outside
  have firstBound : base ≤ first d base := (Nat.le_add_right base d.hosts).trans low
  have idEnd : base+d.hosts ≤ roof d base := low.trans (mid.trans last)
  apply (bf a (outside.imp (fun below => below.trans_le (firstBound.trans mid))
    (fun above => seenEnd.trans above))).trans
  apply (lf a (outside.imp (fun below => below.trans_le firstBound)
    (fun above => paidEnd.trans (last.trans above)))).trans
  exact DescentStaticWordColumn.frame base d.hosts id m a
    (outside.imp_right (fun above => idEnd.trans above))

end
end Hierarchy.DescentOrdinaryRasterReturn

end OAI
