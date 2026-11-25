import OAI.Hierarchy.DescentSeedArchiveTags
import OAI.Hierarchy.DescentDatedSeedActualTokens

namespace OAI
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentLocalArchiveOrder DescentPrimitivePalette
open DescentInitialHost DescentCompiler DescentSixParty DescentSixParty.SeedNamed DescentColonies
open Chronology DescentRotor DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open DescentExterior DescentGL DescentTerminalEpochChart DescentPackedEpochShelves DescentExteriorShelf
open DescentPackedProfileInstall Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H e j r t w : ℕ} (X : Approximation F cp p) (radix : S.radix=2^k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
  (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
  (ex : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool) (back : Memory w)
local notation "G" => S.groupCount 0
local notation "digits" => S.initialDigits radix
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H G k
local notation "chart" => nodeChart l k H G
local notation "finish" => (chart).seedEnd top
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "raw" => Root.appended front extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) raw
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H G lanes finish
local notation "done" => completeImage D op X digits publicWide l header payload Z counted

local notation "seedPorts" => DatePorts.initial D op X S.copies l k H G payload Z

/-- The first registered position observes the actual client bits after the wide selector prelude,
including the seventeen saved exterior arrays. -/
theorem issued_startup_tags (fields : l.operandBits*l.operandLanes≤w) (early : header<l.base)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish) (live : 0<lanes)
    (machine : payload≤w) (space : cap<2^w) (wordRoom : 3<2^l.operandBits) :
    DatePorts.ArchiveTags (seedPorts) done :=by
  have two : 2≤l.operandBits:=by
    by_contra! h
    have limit_:=Nat.pow_le_pow_right (by decide : 0<2) (show l.operandBits≤1 by omega)
    omega
  exact DatePorts.seed_archive_tags D op X digits publicWide l header payload Z counted
    fields early sourceSpace live machine space two

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
