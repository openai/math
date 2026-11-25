import OAI.Hierarchy.DescentPackedEpochCountReads
import OAI.Hierarchy.DescentPackedEpochOldAdmit
import OAI.Hierarchy.DescentPackedEpochSeedImage
import OAI.Hierarchy.DescentTerminalSharedProfileROM

namespace OAI
/-! # Publish the genuine packed seed and profile verdict after the measured native stage trace -/
namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentPackedEpochShelves DescentPackedEpochFold DescentPackedProfileTape DescentPackedProfileInstall
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ow" => normalizedIssuedInputOrders X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→ Bool)
local notation "choice_" => (actualRoute G _ _ X S.copies q w fit rs ow).follow z
local notation "path_" => (normalizedIssuedRows X G S ordinary reset branch positive room shorten choice_).path.selections

local notation "empty" => ([]:List (Source (ch).Pin))
local notation "seedBase" => DescentTerminalPackedSeedFlags.endInput X S.copies q w empty
local notation "seedRows" => DescentPackedSeed.rows X S.copies q w
local notation "seedAt" => seedBase+seedRows
local notation "initial" => DescentTerminalPackedSeedFlags.initial X S.copies q w empty (ch).seed z
local notation "seedCode" => DescentTerminalPackedSeedFlags.check X S.copies q w empty
local notation "first" => seededState X S.copies q w (ch).seed z

/-- The native middle procedure executes the ordinary stages and deposits the
measured pair counters. Its frame protects the one seed verdict, packed source
words, and the original low bits. This holds for an arbitrary raw selector. -/
theorem issued_old_admit (lo R : ℕ) (count : ℕ→ℕ) (middle : Procedure w) (m : Memory w) (cost : ℕ)
    (wideSeed : 2*digitsNeeded q ≤ w) (fitsSeed : seedBase+(seedRows+1) < 2^w)
    (topSeed : seedBase+(seedRows+1) ≤ lo) (pos : 0 < R)
    (low : ∀p∈shelves R lo 0 (ch).layout,count p.ordinal < lo)
    (wide : ∀s∈(ch).layout,slots s.seats R*R < 2^w)
    (space : final lo G.C R (ch).layout+1 < 2^w)
    (stage : middle.Exec (first lo G.C R (ch).layout) m cost) (cheap : CheapCode middle)
    (measured : m (seedAt)=first lo G.C R (ch).layout (seedAt))
    (archive : ∀a,lo ≤ a→ a < end_ (lo+extent R (ch).layout) G.C R→ m a=first lo G.C R (ch).layout a)
    (physical : ∀i,i < ((ch).rows z).length→∀v,(path_)[i]?=some v→(m (count i)).val=selectionCount G v) :
    let dst:=final lo G.C R (ch).layout
    let ss:=controls lo G.C R (ch).layout count (fun _=>seedAt)
    let tape:=((seedCode).seq middle).seq (fold w seedAt dst ss)
    let o:=oldState lo G.C R seedAt (ch).layout count z m
    tape.Exec (original X S.copies q w (ch).seed z lo G.C R (ch).layout) o
      ((4+(seedRows+1)*66+cost)+bill seedAt dst ss) ∧ CheapCode tape ∧
    (o dst=0 ↔ ∃c,(ch).read z=some c) ∧ ∀a < end_ (lo+extent R (ch).layout) G.C R,o a=m a := by
  have seed_:=seed_exact X S.copies q w (ch).seed z lo G.C R (ch).layout wideSeed fitsSeed topSeed
  have same:=actual_uniform G _ _ X S.copies q w fit rs ow
  have resident : ∀a,lo ≤ a→ a < end_ (lo+extent R (ch).layout) G.C R→ m a=header lo G.C R (ch).layout z initial a :=
    fun a ha h=>(archive a ha h).trans (seed_.2.2.2 a (Or.inr (by omega)))
  have valid : m seedAt=0 ↔ valid X (z∘(ch).seed) := by rw [measured];exact seed_.2.2.1
  have checked:=oldAdmit ch z initial m lo G.C R seedAt count same pos (by omega) low wide space resident valid
    (issued_count_words X G S ordinary reset branch positive room shorten w fit z lo R count _ m physical)
  exact ⟨Procedure.Exec.then (Procedure.Exec.then seed_.1 stage) checked.1,cheap_seq (cheap_seq seed_.2.1 cheap) checked.2.1,checked.2.2⟩

end
end Hierarchy.DescentBundleHistory

end OAI
