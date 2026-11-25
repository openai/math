import OAI.Hierarchy.DescentDatedSeedActualTokens
import OAI.Hierarchy.DescentSeedProposalCount

namespace OAI
/-! # The original source population in the complete initialized tape -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentInitialHost DescentCompiler DescentSixParty DescentSixParty.SeedNamed DescentColonies
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
local notation "g₀" => S.groupCount 0
local notation "digits" => S.initialDigits radix
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "raw" => Root.appended front extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) raw
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "done" => completeImage D op X digits publicWide l header payload Z counted
variable {q ε : ℝ} {wire z₀ : ℕ} {c : (initialGroup X S.copies l.seedWidth).Choice}
  (o : Origin X (s:=l.seedWidth) (G:=D) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c (S.initialDigits radix))
  (wide : @Fintype.card o.raw.V o.raw.finite ≤ H)

include o wide in
omit wide o in
theorem complete_source_count (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fields : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w) :
    done 0=((S.copies*Fintype.card (Vertex X):ℕ):Word w) :=
  proposal_count D op X radix publicWide l header payload Z seed lo C grain ss origin extra ex z back
    width live machine signed fields seedFits seedBefore shelves privateAfter early space

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
