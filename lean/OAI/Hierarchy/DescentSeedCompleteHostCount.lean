import OAI.Hierarchy.DescentSeedCompleteImage
import OAI.Hierarchy.DescentSeedTokenRun
import OAI.Hierarchy.DescentSeedNodeHostCount

namespace OAI
/-! # The public host count survives the complete seed loader -/
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

theorem complete_host_count (m : Memory w) (early : header<l.base)
    (before : publicWords X+DescentDyadicSpan.span jobs≤finish) (live : 0<lanes)
    (machine : payload≤w) (space : last<2^w) :
    completeImage D op X digits publicWide l header payload Z m (ct).base=(Fintype.card (Vertex X):Word w) :=by
  obtain ⟨begin_,last_⟩:=Primitive.fences X S.copies l.seedWidth payload k H G₀ lanes finish
  have first:=(begin_.trans last_).trans_lt space
  have leq : top≤finish:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have fits:=shared_host_fits db H G₀ l.packedLanes w (leq.trans_lt first)
  have below : (ct).base<finish:=by have b:=fits.2.2;change (ct).base+1≤top at b;omega
  exact ((Primitive.any X D op S.copies l.seedWidth Z payload k H G₀ lanes finish hs
    (afterCountImage X digits publicWide l header m) before space machine live).2.2 (ct).base (.inl below)).trans
    (roster_host_count X digits publicWide l header m early first)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
