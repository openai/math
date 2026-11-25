import OAI.Hierarchy.DescentNamedCountReads
import OAI.Hierarchy.DescentNamedExteriorPublication
import OAI.Hierarchy.DescentPackedEpochIssuedFlag
import OAI.Hierarchy.DescentExteriorPackedSeedRun
import OAI.Hierarchy.DescentExteriorReelLayout

namespace OAI
/-! # One universal native prefix admits the true packed choice and installs its physical exterior -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentPackedEpochShelves DescentPackedEpochFold DescentPackedProfileTape DescentPackedProfileInstall
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentExterior DescentExteriorShelf DescentExteriorMatrixUpdate CorrectionBatch CatalystSubstitution
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode Origin.source Branch.publicLayout
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ow" => inputOrder X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→ Bool)
local notation "choice_" => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z
local notation "path_" => (SeedNamed.issued X G S ordinary reset branch positive room shorten choice_).path.selections

local notation "empty" => ([]:List (Source (ch).Pin))
local notation "seedBase" => DescentTerminalPackedSeedFlags.endInput X S.copies q w empty
local notation "seedRows" => DescentPackedSeed.rows X S.copies q w
local notation "seedAt" => seedBase+seedRows
local notation "initial" => DescentTerminalPackedSeedFlags.initial X S.copies q w empty (ch).seed z
local notation "seedCode" => DescentTerminalPackedSeedFlags.check X S.copies q w empty
local notation "first" => seededState X S.copies q w (ch).seed z

local notation "chosen" => SeedNamed.issued X G S ordinary reset branch positive room shorten choice_
local notation "E" => Fintype.card (Port nP X.width)
variable {j rest t : ℕ} (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (x : Fin (Fintype.card (Port nP X.width))→Plane j rest→Fin t→Bool)
  (guesses : Hidden (Fintype.card (Port nP X.width)) j rest t→Bool)
local notation "packed" => Sum.elim z guesses
local notation "B" => S.groupWidth k tail 0+k
local notation "survives" => (∃c,(ch).read z=some c)

private abbrev observedCounts (count : ℕ → ℕ) (m : Memory w) : Prop :=
  ∀ i, i < ((ch).rows z).length → ∀ v, (path_)[i]? = some v → (m (count i)).val = selectionCount G v

private abbrev savedOnAcceptance (plan : Reel) (fence : ℕ) (m : Memory w) : Prop :=
  survives → (chosen).path.savedRotations plan fence tail m

attribute [local irreducible] Loaded in
theorem loaded_for (origin : ℕ) (m : Memory w)
    (held : survives→Loaded origin (Branch.publicLayout X G S chosen positive reset.base width) x guesses m) :
    ∀c,(ch).read z=some c→Loaded origin (Branch.publicLayout X G S
      (SeedNamed.issued X G S ordinary reset branch positive room shorten c) positive reset.base width) x guesses m := by
  intro c ok
  have same := ((ch).read_iff z c).mp ok
  have selected : choice_ = c :=
    (congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow same).trans
      ((normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored c)
  exact selected ▸ (held ⟨c,ok⟩)

set_option maxHeartbeats 600000 in
/-- A single native run, from the jointly wired original seed, epoch, external and proposal bits.
The chronological prefix publishes the selected rotation codes only on surviving selectors. -/
theorem issue_exterior_from (lo grain rawOrigin origin fence : ℕ) (count : ℕ→ℕ) (plan : Reel)
    (middle : Procedure w) (m : Memory w) (cost : ℕ)
    (wideSeed : 2*digitsNeeded q ≤ w) (wide : 0 < w) (fitsSeed : seedBase+(seedRows+1) < 2^w)
    (topSeed : seedBase+(seedRows+1) ≤ lo) (positiveGrain : 0 < grain)
    (below : end_ (lo+extent grain (ch).layout) G.C grain ≤ fence)
    (before : final lo G.C grain (ch).layout < origin)
    (low : ∀p∈shelves grain lo 0 (ch).layout,count p.ordinal < lo)
    (words : ∀s∈(ch).layout,slots s.seats grain*grain < 2^w)
    (fits : final lo G.C grain (ch).layout+1 < 2^w)
    (geometry : plan.Room w B S.length fence origin)
    (top : origin+span j rest t E+E < 2^w)
    (rawRoom : end_ (lo+extent grain (ch).layout) G.C grain ≤ rawOrigin)
    (stage : middle.Exec (Root.counted X S.copies q w (ch).seed lo G.C grain (ch).layout rawOrigin x packed) m cost)
    (cheap : CheapCode middle)
    (measured : m seedAt=Root.counted X S.copies q w (ch).seed lo G.C grain (ch).layout rawOrigin x packed seedAt)
    (archive : ∀a,lo ≤ a→a < end_ (lo+extent grain (ch).layout) G.C grain→
      m a=Root.counted X S.copies q w (ch).seed lo G.C grain (ch).layout rawOrigin x packed a)
    (exterior : ∀(col : Fin 17) (u : ℕ),u < span j rest t E→
      m ((bank j rest t E origin col.val).base+u)=Root.counted X S.copies q w (ch).seed lo G.C grain
        (ch).layout rawOrigin x packed ((bank j rest t E rawOrigin col.val).base+u))
    (physical : observedCounts X G S ordinary reset branch positive room shorten w fit z count m)
    (issued : savedOnAcceptance X G S ordinary reset branch positive room shorten w fit z plan fence m) :
    let keep:=plan.result j rest t E B S.length origin m
    let start:=Root.packedImage X S.copies q w (ch).seed lo G.C grain (ch).layout rawOrigin x packed
    let dst:=final lo G.C grain (ch).layout
    let ss:=controls lo G.C grain (ch).layout count (fun _=>seedAt)
    let program:=(((seedCode).seq middle).seq (plan.program j rest t E w B S.length origin)).seq (fold w seedAt dst ss)
    let o:=oldState lo G.C grain seedAt (ch).layout count z keep
    program.Exec start o (((4+(seedRows+1)*66+cost)+(10+((4+58*S.length)+(4+16*E))))+bill seedAt dst ss) ∧
    CheapCode program ∧ (o dst=0 ↔ survives) ∧
    (survives→Loaded origin (Branch.publicLayout X G S chosen positive reset.base width) x guesses o) ∧
    ∀a < end_ (lo+extent grain (ch).layout) G.C grain,o a=m a := by
  intro keep start dst ss program o
  have ordered : end_ (lo+extent grain (ch).layout) G.C grain ≤ final lo G.C grain (ch).layout := Nat.le_add_right ..
  have loFit : lo ≤ end_ (lo+extent grain (ch).layout) G.C grain:=by dsimp only [end_,dict];omega
  have start_:=Root.counted_run X S.copies q w (ch).seed lo G.C grain (ch).layout rawOrigin x packed
    wideSeed fitsSeed topSeed rawRoom
  have reel:=plan.run (j:=j) (r:=rest) (t:=t) (e:=E) B S.length fence origin m geometry wide top
  have active : Loaded origin (fun _=>LinearEquiv.refl _ _) x guesses m:=by
    intro col u hu
    exact (exterior col u hu).trans (start_.2.2.2.1 col u hu)
  have same:=SeedNamed.uniform G _ _ X S.copies q w fit (S.initialDigits ordinary.radix) rs ow
  have store : ∀a,lo ≤ a→a < end_ (lo+extent grain (ch).layout) G.C grain→
      keep a=header lo G.C grain (ch).layout z initial a:=by
    intro a ha hb
    exact (reel.2.2 _ (hb.trans_le below)).trans ((archive _ ha hb).trans
      ((start_.2.2.2.2 a (.inr (by omega))).trans
      (Root.packed_original X S.copies q w (ch).seed lo G.C grain (ch).layout rawOrigin x packed rawRoom hb)))
  have passes : keep seedAt=0 ↔ valid X (z∘(ch).seed) := by
    rw [show keep seedAt=m seedAt from reel.2.2 _ (by omega),measured]
    exact start_.2.2.1
  have recorded:=issued_count_words X G S ordinary reset branch positive room shorten w fit z lo grain count
    (fun _=>seedAt) m physical
  have retained : (controls lo G.C grain (ch).layout count (fun _=>seedAt)).map (fun s=>(keep s.banks.count.base).val)=
      (controls lo G.C grain (ch).layout count (fun _=>seedAt)).map (fun s=>(m s.banks.count.base).val) := by
    rw [counter_words,counter_words]
    apply List.map_congr_left
    intro i hi
    rw [←ordinals grain lo 0 (ch).layout,List.mem_map] at hi
    obtain ⟨p,hp,rfl⟩:=hi
    rw [show keep (count p.ordinal)=m (count p.ordinal) from reel.2.2 _ ((low p hp).trans_le (loFit.trans below))]
  rw [←retained] at recorded
  have finalCheck:=oldAdmit ch z initial keep lo G.C grain seedAt count same positiveGrain (by omega)
    low words fits store passes recorded
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then start_.1 stage) reel.1) finalCheck.1,
    cheap_seq (cheap_seq (cheap_seq start_.2.1 cheap) reel.2.1) finalCheck.2.1,finalCheck.2.2.1,?_,?_⟩
  · intro ok
    have branch_:=Branch.reel_layout X G S chosen positive reset.base width origin fence plan m x guesses
      active (issued ok) geometry
    intro col u live
    have hi : dst < (bank j rest t E origin col.val).base+u:=by
      change final lo G.C grain (ch).layout < origin+col.val*span j rest t E+u
      omega
    exact (oldState_frame ch z initial keep lo G.C grain seedAt count same positiveGrain (by omega) low words fits store _
      (.inr hi)).trans (branch_ col u live)
  · exact fun a ha=>(finalCheck.2.2.2 a ha).trans (reel.2.2 a (ha.trans_le below))

end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

-- Keep the physical and chart predicates opaque while Lean indexes these theorem signatures.
open OAI.Hierarchy.DescentSixParty.SeedNamed OAI.Hierarchy.DescentExteriorShelf
attribute [local irreducible] Origin.source Branch.publicLayout Loaded OAI.Hierarchy.DescentSixParty.SeedNamed.issued normalizedRoute normalizedPackedChart
attribute [local irreducible] OAI.Hierarchy.ProtocolRAM.CheapCode
  OAI.ThreeFlat.RAM.PhysicalProcedure.Procedure.Exec
