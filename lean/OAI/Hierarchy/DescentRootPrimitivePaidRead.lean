import OAI.Hierarchy.DescentPostedPaidActors

namespace OAI
/-! # Reading the reset's funded column in the primitive birth chart -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentCompiler DescentPackedZip DescentPackedColony DescentColonies DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F X:Type} [Field F] {n:ℕ} {bits:X→ℕ} {W:MarkedWorld F n X bits}
    {G:PoweredGadget F} {S:AtomSchedule} {k age t D wire hist:ℕ} {q ε:ℝ}
    {a:PhysicalReset} {floor w:ℕ} {u:a.DateInputs floor w} (z:u.FinalInputs)
local notation "v" => a.successor
local notation "B" => (v).birth
local notation "L" => (B).placement
local notation "chart" => (v).primitive.chart
local notation "fund" => (v).fundedEnd (a.rebased floor)
local notation "banks" => (v).venue.sources (predecessor u) fund

private theorem source_axes {H H' G G' b M:ℕ} (host:H=H') (groupId:G=G') (e:Expr)
    (quantity:Fin H'→Fin G'→Cell b) (m:Memory w) (read:Source e quantity M m):
    Source e (fun h g=>quantity (Fin.cast host h) (Fin.cast groupId g)) M m:=by
  subst H';subst G';exact read

/-- The block, host, and group casts are those in the physical primitive reader.
They keep the row address and the group's packed lane unchanged. -/
theorem root_funded_acquired (r:Reached W G q ε S k age t D wire hist)
    (blocks:(chart).blocks=2^k)(hosts:(chart).hosts=S.hostSize age)(groups:(chart).groups=S.groupCount age)
    (fullHost:(chart).hosts=(L).newHosts)(fullGroup:(chart).groups=(L).groups)(mid:Memory w)
    (raw:∀x:Block k,Source (.lookup ((banks).paid x.val) .row) (fun h g=>Census.count r.placement
      (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb r.valid.host)) (B).paidBits h g x) (L).lanes (z.venueImage mid)):
    ∀x:Fin (chart).blocks,Source (paid u (x.cast z.censusBlocks))
      (fun h g=>Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb r.valid.host)) (B).paidBits
        (Fin.cast (fullHost.symm.trans hosts) h) (Fin.cast (fullGroup.symm.trans groups) g) (Fin.cast blocks x))
      (L).lanes (z.venueImage mid):=by
  intro x
  exact source_axes (w:=w) (b:=(B).paidBits) (M:=(L).lanes)
    (fullHost.symm.trans hosts) (fullGroup.symm.trans groups) (.lookup ((banks).paid x.val) .row)
    (fun h g => Census.count r.placement (Equiv.refl _)
      (r.vertex.trans (Fin.castLEEmb r.valid.host)) (B).paidBits h g (Fin.cast blocks x))
    (z.venueImage mid) (raw (Fin.cast blocks x))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
