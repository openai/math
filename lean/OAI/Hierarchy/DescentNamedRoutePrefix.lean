import OAI.Hierarchy.DescentEpochRoutePrefix
import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentPackedEpochReader
import OAI.Hierarchy.DescentPackedProfileArchive
import OAI.Hierarchy.DescentPackedSeedHeader

namespace OAI
/-! # The preselection counts run on an honest completion even if a later profile is malformed -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing DescentPackedProfileWide
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "rs" => (cert).choose
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "s" => S.firstWidth G.b p
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "rr" => normalizedRoute X G S ordinary reset branch positive room shorten w fit
local notation "b" => issued X G S ordinary reset branch positive room shorten

theorem reached_past : (rr).Past := by
  apply epochs_past G _ _ rs order (seedChart X S.copies s w fit) (seedRoute X S.copies s w fit)
  intro z
  constructor
  · intro h
    change 0 < 0 at h
    omega
  · intro i h
    change i+1 < 0 at h
    omega

variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→Bool)
local notation "c₀" => (rr).follow z
local notation "other" => (ch).store c₀

/-- The actual seed fields and complete preceding physical source words agree with the
single valid completed choice of this same tape, up to every observed count. -/
theorem prefix_completion (i : ℕ) (hit : i < ((ch).rows z).length) :
    (ch).read other=some c₀ ∧ z∘(ch).seed=other∘(ch).seed ∧
    ∀j < i,∀a,(ch).layout[j]?=some a → z∘a.pin=other∘a.pin := by
  have past:=reached_past X G S ordinary reset branch positive room shorten w fit z
  exact ⟨((ch).read_iff _ _).2 rfl,funext (past.1 ((Nat.zero_le i).trans_lt hit)),
    fun j hj a at_=>funext (past.2 j ((Nat.succ_le_of_lt hj).trans_lt hit) a at_)⟩

/-- Native wide-cell lanes of every past ordinary step hold the profile of the
exact mathematical matched pair, in the issuer's own rank order. -/
theorem previous_profile (i : ℕ) (hit : i < ((ch).rows z).length) {j : ℕ} (earlier : j < i)
    (src : Source (ch).Pin) (fromTape : (ch).layout[j]?=some src)
    (v : _) (fromPath : (b c₀).path.inputRanked[j]?=some v)
    (digit : ℕ) (extend : DescentTerminalEpochBits.width src.C ≤ digit) :
    ∀q,(wideCell src.pin z digit extend q).val=issuedProfile G v q := by
  have eqn:=prefix_completion X G S ordinary reset branch positive room shorten w fit z i hit
  have original:=eqn.2.2 j earlier src fromTape
  have profileRows:=packedChart_fields X G S ordinary reset branch positive room shorten w fit other c₀ eqn.1
  have at_:=congrArg (fun xs : List (ℕ→ℕ)=>xs[j]?) profileRows
  simp only [List.getElem?_map,fromTape,fromPath,Option.map_some,Option.some.injEq] at at_
  intro q
  rw [cell_eq,cell_read]
  change (if h : q < src.seats then raw (z∘src.pin) ⟨q,h⟩ else 0)=_
  rw [original]
  exact congrFun at_ q

theorem preceding_seed (i : ℕ) (hit : i < ((ch).rows z).length) (a : CountKey X S.copies) :
    (rawCount X (z∘(ch).seed) a).val=selected X (Epochs.seedChoice G _ _
      (H:=initial X S.copies s (S.groupCount 0) k (S.initialDigits ordinary.radix)) (J:=S.height)
      (t:=S.rounds) (h:=h) (C:=C) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g) rs c₀) a := by
  have pre:=prefix_completion X G S ordinary reset branch positive room shorten w fit z i hit
  rw [pre.2.1]
  exact packedChart_seed X G S ordinary reset branch positive room shorten w fit other c₀ pre.1 a

/-- The compact physical startup words are exactly the honest reference's original
public and short-count words whenever an ordinary count is reached. -/
theorem preceding_header (i : ℕ) (hit : i < ((ch).rows z).length) :
    DescentPackedSeed.base X w (z∘(ch).seed)=DescentPackedSeed.base X w (other∘(ch).seed) :=
  congrArg (DescentPackedSeed.base X w)
    (prefix_completion X G S ordinary reset branch positive room shorten w fit z i hit).2.1

/-- This is the identical RAM image, including trailing window words. Altering a
future profile never changes which datum was read in this prior physical shelf. -/
theorem preceding_bank (i : ℕ) (hit : i < ((ch).rows z).length) {j : ℕ} (earlier : j < i)
    (src : Source (ch).Pin) (onTape : (ch).layout[j]?=some src)
    (digit grain : ℕ) (extend : DescentTerminalEpochBits.width src.C ≤ digit) (bank : ProtocolRAM.Bank) {bw : ℕ}
    (m : Computability.VPVNP.BurstRAM.Memory bw) :
    DescentPackedProfileArchive.Stored src digit grain extend bank z m ↔
      DescentPackedProfileArchive.Stored src digit grain extend bank other m := by
  have same:=((prefix_completion X G S ordinary reset branch positive room shorten w fit z i hit).2.2 j earlier src onTape)
  have bits (c : _) : z (src.pin c)=other (src.pin c):=congrFun same c
  have cells : wideCell src.pin z digit extend=wideCell src.pin other digit extend := by
    funext n
    simp only [wideCell,DescentPackedProfileTape.cell,bits]
  simp only [DescentPackedProfileArchive.Stored,cells]

/-- A malformed packed startup count reaches no ordinary pair counter. -/
theorem bad_seed_has_no_rows (bad : ¬ valid X (z∘(ch).seed)) : (ch).rows z=[] := by
  cases eqn:(ch).rows z with
  | nil=>rfl
  | cons a tail=>
    have reached : 0 < ((ch).rows z).length:=by simp [eqn]
    obtain ⟨good,seed,_⟩:=prefix_completion X G S ordinary reset branch positive room shorten w fit z 0 reached
    have checked:=((ch).accepted other).1 ⟨c₀,good⟩
    exact (bad (seed.symm ▸ checked.1)).elim

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
