import OAI.Hierarchy.DescentResetStemObservedInputs
import OAI.Hierarchy.DescentResetTrunkOriginalHeaders
import OAI.Hierarchy.DescentDateStemRegisterRead
import OAI.Hierarchy.DescentCalendarStemCoordinates

namespace OAI
/-! # Transport of old signed chips and the newly built stem headers together -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentPackedZip DescentDatedAddressBook DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "ng" => S.groupCount (i+1)
local notation "J" => stemsCount B

structure StemPublished (H lanes signedBits metaBits lo hi : ℕ) (old head : ℕ→ℕ→Expr) {w : ℕ} (m : Memory w) : Prop where
  signed : ∃val : Block k→Fin J→Fin H→Fin ng→Cell signedBits,
    (∀x j,(old x.val j.val).Fits w lo ∧ Source (old x.val j.val) (val x j) lanes m) ∧
    ∀x j h g v,originalTrunkRack B h=some v→val x j h g=(stemObservedChip B (originalTrunkRack B) x j h g:Cell signedBits)
  head : ∀(x : Block k) (j : Fin J),(head x.val j.val).Fits w hi ∧
    Source (head x.val j.val) (fun (h : Fin H) g=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x (stemShelf B j) h g)) lanes m

theorem original_signed_coordinates {a b : CandidateFront} {start : ℕ}
    (same : a=b) (x : a.Originals start) (y : b.Originals start) (inputs : HEq x y)
    (flags count inverse : Bank) :
    a.mixed start=b.mixed start ∧
    (∀i j,(a.job (a.fromOriginals start x flags count inverse).stems).signedTerm
      (a.parentEnd start) (a.parent start).base i j=
      (b.job (b.fromOriginals start y flags count inverse).stems).signedTerm
      (b.parentEnd start) (b.parent start).base i j) :=by
  subst b
  cases eq_of_heq inputs
  exact ⟨rfl,fun _ _=>rfl⟩


section
variable {date : PhysicalReset} {floor w : ℕ} (I : date.DateInputs floor w)
local notation "V" => date.successor
local notation "bb" => date.rebased floor
local notation "A₀" => (V).front
local notation "start" => (V).actorEnd bb
local notation "rows" => (V).actor.directory ((V).middle.stop bb)
local notation "sh" => (V).sheets
local notation "actual" => (V).issuedScene bb I.earlier

theorem named_stem_dimensions (M cap : ℕ)
    (layout : (sh)=CandidateSheets.fromBoard S ctl.board k tail i D f g cap M) :
    S.hostSize (i+1)=(sh).hosts ∧ M=(sh).lanes ∧
    ResetMiddle.fieldWidth D cap n k (GroupStage.depthBound D n f g)=(sh).stemSignedBits ∧
    (CandidateSheets.fromBoard S ctl.board k tail i D f g cap M).metaBits=(sh).metaBits :=by
  rw [layout]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Relabel the one real calendar publication at the named date and the same input. -/
theorem named_stem_published {b : CandidateFront} (same : (A₀)=b) (old : b.Originals start)
    (sameOld : HEq I.earlier old) (access : b.SceneRoom start
      (b.fromOriginals start old (rows).flags (rows).count (rows).inverse) w)
    {H lanes signedBits metaBits : ℕ}
    (hosts : H=(sh).hosts) (batch : lanes=(sh).lanes)
    (degree : signedBits=(sh).stemSignedBits) (width : metaBits=(sh).metaBits)
    (m : Memory w)
    (published : StemPublished B H lanes signedBits metaBits (b.mixed start) (b.trunkEnd start)
      ((b.job (b.fromOriginals start old (rows).flags (rows).count (rows).inverse).stems).signedTerm
        (b.parentEnd start) (b.parent start).base)
      (b.stemOperand start)
      ((b.trunkScene start (b.fromOriginals start old (rows).flags (rows).count (rows).inverse) access).image m)) :
    StemPublished B (sh).hosts (sh).lanes (sh).stemSignedBits (sh).metaBits ((A₀).mixed start)
      ((V).trunkEnd bb) I.previousSigned ((A₀).stemOperand start)
      (((A₀).trunkScene start actual I.sceneFits).image m) :=by
  subst b
  cases eq_of_heq sameOld
  subst H lanes signedBits metaBits
  exact published

theorem named_stem_at_directory (layout : DescentResetNewActorDirectory.Layout)
    (atLayout : (rows)=layout) {b : CandidateFront} (same : (A₀)=b) (old : b.Originals layout.endAddress)
    (sameOld : HEq I.earlier old) (access : b.SceneRoom layout.endAddress
      (b.fromOriginals layout.endAddress old layout.flags layout.count layout.inverse) w)
    {H lanes signedBits metaBits : ℕ}
    (hosts : H=(sh).hosts) (batch : lanes=(sh).lanes)
    (degree : signedBits=(sh).stemSignedBits) (width : metaBits=(sh).metaBits)
    (m : Memory w)
    (published : StemPublished B H lanes signedBits metaBits (b.mixed layout.endAddress) (b.trunkEnd layout.endAddress)
      ((b.job (b.fromOriginals layout.endAddress old layout.flags layout.count layout.inverse).stems).signedTerm
        (b.parentEnd layout.endAddress) (b.parent layout.endAddress).base)
      (b.stemOperand layout.endAddress)
      ((b.trunkScene layout.endAddress (b.fromOriginals layout.endAddress old layout.flags layout.count layout.inverse) access).image m)) :
    StemPublished B (sh).hosts (sh).lanes (sh).stemSignedBits (sh).metaBits ((A₀).mixed start)
      ((V).trunkEnd bb) I.previousSigned ((A₀).stemOperand start)
      (((A₀).trunkScene start actual I.sceneFits).image m) :=by
  subst layout
  exact named_stem_published B I same old sameOld access hosts batch degree width m published


end
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
