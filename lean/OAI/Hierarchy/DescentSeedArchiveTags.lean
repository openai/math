import OAI.Hierarchy.DescentDatePortTaggedRead
import OAI.Hierarchy.DescentSeedAllPointerRows

namespace OAI
/-! # The tag digits returned by the initial physical operand writer -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentPriorOperandColumns DescentOrdinaryAtomFieldRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z

theorem seed_archive_tags {w : ℕ} (counted : Memory w)
    (fields : l.operandBits*l.operandLanes≤w) (early : header<l.base)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w) (bits : 2≤l.operandBits) :
    ArchiveTags (ports) ((final) counted) :=by
  let data:=seedOperandBooks G op X digits publicWide l payload Z
  have printed:=seed_typed_rows G op X digits publicWide l header payload Z counted fields early
    sourceSpace live machine space bits
  exact ⟨data,printed.1.tags,printed.2⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
