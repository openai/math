import OAI.Hierarchy.DescentSeedProposalExecution
import OAI.Hierarchy.DescentSeedTokenReads
import OAI.Hierarchy.DescentExteriorAppendedWords
import OAI.Hierarchy.DescentSeedCountedRoleSource
import OAI.Hierarchy.DescentSeedInitialBlockKeys

namespace OAI
/-! # Original global primitive receipts in the complete initialized memory -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentInitialHost DescentCompiler DescentSixParty DescentColonies
open DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
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
variable {c : (initialGroup X S.copies l.seedWidth).Choice}

theorem ballot_tokens {cw : ℕ} (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w) (bits : DescentPrimitivePalette.printedBits D l.seedWidth Z op*lanes ≤ w)
    (fit : l.seedWidth < 2^cw) (seen : (z∘Sum.inl)∘seed=selectBit X cw c)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fields : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w)
    (x : Block k) :
    Reads (Primitive.page X S.copies l.seedWidth payload k H G lanes finish x)
      (Primitive.value X D op S.copies l.seedWidth Z k H G hs c digits x) lanes done :=by
  let old:=afterCountImage X digits publicWide l header counted
  obtain ⟨source,rawRead⟩:=Root.counted_role_source X S.copies l.seedWidth payload w seed lo C grain ss origin ex z raw
    (fun _ h=>Root.append_low _ _ _ _ h) width seedFits seedBefore shelves
  obtain ⟨sourceStart,sourceEnd⟩:=Primitive.fences X S.copies l.seedWidth payload k H G lanes finish
  have lowLo : lo ≤ lowEnd := profile_start_le_end lo C grain ss
  have lowHeader : flag ≤ header:=by omega
  have corners:=fences X l H G k
  have baseBelow : l.base ≤ top:=corners.1.trans (corners.2.1.trans corners.2.2)
  have finalFloor : top ≤ finish:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have retained:=(after_count_any X digits publicWide l header counted signed fields early
    ((sourceStart.trans sourceEnd).trans_lt space)).2.2
  have sourceSpace :=source.trans (lowHeader.trans (early.le.trans (baseBelow.trans finalFloor)))
  apply Primitive.reads X D op S.copies l.seedWidth Z payload k H G lanes finish hs old c
    (S.seed_population_eq radix) digits (S.seed_block_index radix)
    (occupancy payload (8*digitsNeeded l.seedWidth) (by unfold digitsNeeded;positivity) (by omega)).1
    live machine bits fit sourceSpace space ?_ x
  intro rr
  have limit:=Nat.add_lt_add_left ((row _ _ _ rr).isLt.trans_le (DescentDyadicSpan.span_ge jobs)) (publicWords X)
  have below:=limit.trans_le (source.trans lowHeader)
  have atRow:=(retained _ below.ne (.inl (below.trans early))).trans (rawRead rr)
  simpa only [seen] using atRow

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
