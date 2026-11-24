import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorSelectedTermWorker

/-!
# The selector input at the actual shrinking branch

The AB and CD reads of the paired gather establish the exact demand
rows in its output memory. These rows and the packed term addresses
instantiate the physical worker input used by the reverse selector proof.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkCurrentBranch

open BurstRAM Compression SelectedTerms PairSimulation.LocalHistory
open scoped Classical Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
variable {g w : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (T : IncidenceDirectory w) (start fuel : ℕ) {m : Memory w} (p : ShrinkBranch.Prefix X T start fuel m)
local notation "o" => (PassOrigin.shrink i rfl X : PassOrigin B f hf (B.shrinkPassAt f hf i rfl X))
local notation "dense" => ShrinkInput.demandHead (w := w) X start
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "thick" => ShrinkInput.thickBank X T start
local notation "cd" => ShrinkInput.cdBank X T start
local notation "ab" => ShrinkInput.piecesBank X T start

theorem pairs (space : ShrinkInput.termEnd X start 10 < 2^w) (cost : ShrinkDemandGather.cost < fuel) :
    ShrinkTermInputs.statePairs X dense p.beforeTerm := by
  let ref := after p.input.post (eventLog p.absolute)
  have fit : ShrinkInput.stop X start < 2^w := by unfold ShrinkInput.termEnd at space; omega
  have rows := (p.input.keepAbsoluteFrame fit p.absoluteRun.frame).stored
  obtain ⟨r,scan,data⟩ := ShrinkTermInputs.gather X.packingData (Shrink.packedIndex X.baseIndex) X.packingWidth
    X.shrinkNumber X.shrinkOrder thick cd ab dense ref rows (ShrinkInput.termLayout X T start 10 space).1 cost
  have eqn := Option.some.inj (scan.run.symm.trans p.gatherRun.run)
  subst r; exact data

set_option maxHeartbeats 1000000 in
/-- Build the motif term worker's input at the end of the actual gather prefix, with the stored
demand pairs, ten-word descriptor addresses and private-fuel bound. -/
def workerInput (fit : ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel) : WorkerInput o w := by
  have ten : (10 : Word w).val = 10 := Nat.mod_eq_of_lt (fit.wide.trans_lt (10 : Word w).isLt)
  have space := fit.termRoom
  rw [ten] at space
  let bounds := ShrinkInput.termLayout X T start 10 space
  let sep := bounds.2.2.1
  let room := bounds.2.2.2
  let L := ShrinkTermInputs.termRows X dense term 10 le_rfl sep room
  have data := ShrinkTermInputs.inputs X dense term 10 le_rfl sep room p.beforeTerm (pairs i X T start fuel p space fit.gatherClock)
  exact ⟨L,ShrinkTermSelection.addr dense term 10,
    TermWorker.addresses_strided (dense).val (term).val 2 10 le_rfl le_rfl sep room,
    p.beforeTerm,data,fit.termWords,fuel,fit.termClock⟩

theorem workerInput_fields (fit : ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel) :
    let I := workerInput B f hf i X T start fuel p fit
    I.addr = ShrinkTermSelection.addr dense term 10 ∧ I.fuel = fuel ∧ I.memory = p.beforeTerm :=
  ⟨rfl,rfl,rfl⟩

theorem workerInput_run (fit : ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel)
    (bs : Fin (ShrinkTermInputs.motifCount X) → List Bool) :
    (workerInput B f hf i X T start fuel p fit).run bs =
      runSegment (ShrinkTermSelection.termProgram B.shrink dense term 10) fuel (some 0) p.beforeTerm (List.ofFn bs) := rfl

end CompressorRecords.ShrinkCurrentBranch

end

end VPVNP
end Computability
end OAI
