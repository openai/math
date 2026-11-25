import OAI.Hierarchy.DescentSeedProposalExecution
import OAI.Hierarchy.DescentWideSeedHeader
import OAI.Hierarchy.DescentExteriorAppendedWords

namespace OAI
/-! # The original source population in the complete initialized tape -/
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
theorem proposal_count (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fields : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w) :
    done 0=((S.copies*Fintype.card (Vertex X):ℕ):Word w) := by
  have stop : 0 < DescentTerminalPackedSeedFlags.start X S.copies l.seedWidth payload := by
    unfold DescentTerminalPackedSeedFlags.start
    exact Nat.add_pos_right _ (Nat.two_pow_pos _)
  have table : 0 < (DescentWideSeedFlags.dictionary X S.copies l.seedWidth payload).base := by
    change 0 < DescentTerminalPackedSeedFlags.start X S.copies l.seedWidth payload + _
    omega
  have beforeFlag : 0 < flag := table.trans_le (Nat.le_add_right ..)
  have loFits := profile_start_le_end lo C grain ss
  have beforeLo : 0 < lo := by omega
  have beforeFront : 0 < front := (beforeLo.trans_le (loFits.trans shelves)).trans_le (Nat.le_add_right ..)
  have beforeHeader : 0 < header := beforeFront.trans_le ((Nat.le_add_right ..).trans privateAfter)
  have keep := (execute_proposal D op X radix publicWide l header payload Z seed lo C grain ss origin extra ex z back
    width live machine signed fields seedFits seedBefore shelves privateAfter early space).2.2.2.2.2
  calc
    done 0 = raw 0 := keep 0 beforeHeader.ne (.inl beforeFlag) (.inl (beforeHeader.trans early))
    _ = Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z 0 :=
      Root.append_low _ _ _ _ beforeFront
    _ = Root.wideOriginal X S.copies l.seedWidth payload w seed lo C grain ss (z∘Sum.inl) 0 :=
      Root.widePacked_original X S.copies l.seedWidth payload w seed lo C grain ss origin ex z shelves
        (beforeLo.trans_le loFits)
    _ = DescentWideSeedFlags.initial X S.copies l.seedWidth payload w seed (z∘Sum.inl) 0 :=
      DescentPackedEpochShelves.frame lo C grain ss (z∘Sum.inl) _ (a:=0) beforeLo
    _ = _ := (DescentWideSeedFlags.lower X S.copies l.seedWidth payload w seed (z∘Sum.inl) table).trans
      (DescentPackedSeed.wide_site_count X payload w _)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
