import OAI.Hierarchy.DescentSeedCompleteHostCount

namespace OAI
/-! # Exact natural shared host count at the physical first date -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentInitialHost DescentCompiler DescentSixParty DescentColonies
open DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open Computability.VPVNP.BurstRAM PrivateRAM Catalyst ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H w : ℕ} (X : Approximation F cp p)
  (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
  (publicWide : Fintype.card (Vertex X)≤H) (l : Layout) (header payload Z : ℕ)
local notation "G₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "db" => directoryBase X l H G₀ k
local notation "top" => endAddress X l H G₀ k
local notation "ct" => sharedHostCountBank db H G₀ l.packedLanes
local notation "chart" => nodeChart l k H G₀
local notation "finish" => (chart).seedEnd top
local notation "Q" => nodeArities X publicWide l
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "last" => Primitive.initialEnd X S.copies l.seedWidth payload k H G₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload

theorem complete_host_number (m : Memory w) (early : header<l.base)
    (before : publicWords X+DescentDyadicSpan.span jobs≤finish) (live : 0<lanes)
    (machine : payload≤w) (space : last<2^w) :
    (completeImage D op X digits publicWide l header payload Z m (ct).base).val=Fintype.card (Vertex X) := by
  rw [complete_host_count D op X digits publicWide l header payload Z m early before live machine space]
  apply Fin.val_cast_of_lt
  obtain ⟨start_,end_⟩:=Primitive.fences X S.copies l.seedWidth payload k H G₀ lanes finish
  have nodeBound : top ≤ finish := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have topFit := (nodeBound.trans (start_.trans end_)).trans_lt space
  have bankFit:=shared_host_fits db H G₀ l.packedLanes w topFit
  have capBound : (bank db H G₀ l.packedLanes 3 4).base+H+1 ≤ top := bankFit.2.2
  have hostsFit : H ≤ top := (Nat.le_add_left H _).trans ((Nat.le_add_right _ 1).trans capBound)
  exact (publicWide.trans hostsFit).trans_lt topFit

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
