import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentStemCalendarRegister
import OAI.Hierarchy.DescentStemRegisterNumbers
import OAI.Hierarchy.DescentNamedResetSheets

namespace OAI
/-! # The real numbered register fields of the date, using the original signed controls -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty DescentResetStemDateSignature DescentStemNumberOperands DescentSIMDLookup
open DescentResetStemPackedIssue DescentResetStemPackedIssue.Mixed
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {start w : ℕ} (u : a.DateInputs start w)
local notation "v" => a.successor
local notation "f" => (v).front
local notation "b" => a.rebased start
local notation "s" => (v).sheets
local notation "cut" => (v).actorEnd b
local notation "base" => (s).metaEnd (((v).remap b).endAddress)

def previousSigned (x j : ℕ) :=((f).job (((v).issuedScene b u.earlier).stems)).signedTerm
  ((f).parentEnd cut) ((f).parent cut).base x j

def originalBasis : Bank:=⟨(a.stencilPhase u.shape start u.count u.hub u.g u.Y).saved,0⟩

theorem stem_at (x j : ℕ) (hx : x<(f).blocks) (jx : x<2^(s).stemSources.coord.fine)
    (hj : j<(f).signedQueries) (jq : j<DescentResetStemPackedIssue.count (2^(s).stemSources.coord.residual) (a.c/2)) :
    u.stemRegisters x j=(s).stemSources.stem base u.originalBasis ⟨x,jx⟩
      (((ordinal (2^(s).stemSources.coord.residual) (a.c/2)).symm ⟨j,jq⟩).2.1)
      (u.previousSigned x j) ((v).peerAux b 3) ((f).stemOperand cut x j) :=by
  unfold stemRegisters
  rw [dite_eq_left (And.intro hx jx), dite_eq_left (And.intro hj jq)]
  unfold previousSigned StemJob.signedTerm
  rw [dite_eq_left (show x<((f).job ((v).issuedScene b u.earlier).stems).blocks from hx),
    dite_eq_left (show j<((f).job ((v).issuedScene b u.earlier).stems).Q from hj)]
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentPackedZip DescentDatedAddressBook
open DescentResetFieldAssembler DescentStemNumberOperands DescentResetStemFlagInputs
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {a : PhysicalReset} {start Wd : ℕ} (u : a.DateInputs start Wd)
local notation "v" => a.successor
local notation "fr" => (v).front
local notation "s" => (v).sheets
local notation "b₀" => a.rebased start
local notation "cut₀" => (v).actorEnd b₀
local notation "base" => (s).metaEnd (((v).remap b₀).endAddress)
local notation "N" => (s).hosts
local notation "M" => (s).lanes
local notation "field" => (s).stemBits
local notation "sg" => (s).stemSignedBits
local notation "bw" => (s).metaBits
local notation "ng" => S.groupCount (i+1)
local notation "J" => stemsCount B
local notation "receivers" => originalTrunkRack (H:=N) B
local notation "bias" => (v).peerAux b₀ 3
local notation "headerAt" => (fr).stemOperand cut₀
local notation "P₀" => numberPlan B N M field sg bw bw

theorem scheduled_stem_plan (board : NonlinearExpanders.Graph n h) (cap lanes : ℕ) :
    let sh:=CandidateSheets.fromBoard S board k tail i D f g cap lanes
    sh.stemSources=numberPlan B sh.hosts sh.lanes sh.stemBits sh.stemSignedBits sh.metaBits sh.metaBits :=by
  simp only [CandidateSheets.fromBoard,CandidateSheets.stemSources,CandidateSheets.coordinate,
    numberPlan,coords,B.commonDepth,Nat.add_sub_cancel_left]

theorem observed_chip_bound (x : Block k) (j : Fin J) (r : Fin N) (a₀ : Fin ng)
    (fits : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤ sg) :
    stemObservedChip B (receivers) x j r a₀<2^sg :=by
  unfold stemObservedChip
  cases rec : receivers r with
  | none=>exact Nat.two_pow_pos _
  | some v'=>
    apply Nat.lt_of_lt_of_le (Fin.isLt _)
    exact Nat.pow_le_pow_right (by decide) fits

theorem real_stem_inputs (mem : Memory Wd)
    (schedule : (s).stemSources=P₀)
    (xRoom : 2^k≤(fr).blocks) (jRoom : J≤(fr).signedQueries)
    (cap : a.c/2=input.placement.cap)
    (chosen : mem u.originalBasis.base=((DescentExterior.matrixCode B.frame.basis).val:Word Wd))
    (saved : u.originalBasis.Fits Wd base) (space : (s).coordinateEnd (((v).remap b₀).endAddress)<2^Wd)
    (chip : Fin (2^k)→Fin J→Fin N→Fin ng→Cell sg)
    (sign : ∀x j,Source (u.previousSigned x.val j.val) (chip x j) M mem)
    (signAt : ∀x j r h v',receivers r=some v'→(chip x j r h).val=stemObservedChip B (receivers) x j r h)
    (cs : ∀(x : Block k) (j : Fin J),(u.previousSigned x.val j.val).Fits Wd base)
    (self : Fin N→Cell bw)
    (sels : Source (bias) (fun r (_:Fin ng)=>self r) M mem)
    (selfAt : ∀r v',receivers r=some v'→(self r).val=stemSelfDigit B (receivers) r)
    (bf : (bias).Fits Wd base)
    (head : ∀(x : Block k) (j : Fin J),Source (headerAt x.val j.val)
      (fun r h=>DescentResetFieldAssembler.raw bw (actualMeta B (receivers) x (stemShelf B j) r h)) M mem)
    (hd : ∀(x : Block k) (j : Fin J),(headerAt x.val j.val).Fits Wd base) (metaPos : 0<bw) :
    let dst:=(s).stemSources.image base mem
    let top:=(s).coordinateEnd (((v).remap b₀).endAddress)
    (∀(x : Block k) (j : Fin J) t,(u.stemRegisters x.val j.val t).Fits Wd top) ∧
    (∀(x : Block k) (j : Fin J),Source (u.stemRegisters x.val j.val 0) (fun r h=>((chip x j r h).val:Cell field)) M dst) ∧
    (∀(x : Block k) (j : Fin J),Source (u.stemRegisters x.val j.val 1)
      (fun (_:Fin N) h=>(stemGroupDigit B x (stemTag B j).2.1 h:Cell field)) M dst) ∧
    (∀(x : Block k) (j : Fin J),Source (u.stemRegisters x.val j.val 2) (fun r (_:Fin ng)=>((self r).val:Cell field)) M dst) ∧
    (∀(x : Block k) (j : Fin J),Source (u.stemRegisters x.val j.val 3)
      (fun (_:Fin N) h=>(stemFineDigit B x (stemTag B j).2.1 h:Cell field)) M dst) ∧
    (∀(x : Block k) (j : Fin J),Source (u.stemRegisters x.val j.val 4)
      (fun r h=>((actualMeta B (receivers) x (stemShelf B j) r h).live.toNat:Cell field)) M dst) ∧
    (∀(x : Block k) (j : Fin J),Source (u.stemRegisters x.val j.val 5) (fun (_:Fin N) (h : Fin ng)=>firstDigit field x.val h) M dst) ∧
    (∀x j r h v',receivers r=some v'→((chip x j r h).val:Cell field)=(stemObservedChip B (receivers) x j r h:Cell field)) ∧
    (∀r v',receivers r=some v'→((self r).val:Cell field)=(stemSelfDigit B (receivers) r:Cell field)) :=by
  let orig:=fun (x : Block k) (j : Fin J)=>u.previousSigned x.val j.val
  let header:=fun (x : Block k) (j : Fin J)=>(headerAt x.val j.val)
  have reduced (x : Block k) (j : Fin J) : u.stemRegisters x.val j.val=
      originalRegisters («N»:=N) («M»:=M) («field»:=field) (signed:=sg) (self:=bw) («meta»:=bw)
        B base u.originalBasis orig (bias) header x j:=by
    have hx : x.val<2^(s).stemSources.coord.fine:=by rw [schedule];exact x.isLt
    have hj : j.val<DescentResetStemPackedIssue.count (2^(s).stemSources.coord.residual) (a.c/2):=by
      rw [schedule,cap];exact j.isLt
    rw [u.stem_at x.val j.val (x.isLt.trans_le xRoom) hx (j.isLt.trans_le jRoom) hj]
    revert hx hj
    rw [schedule,cap]
    intros
    rfl
  have limit : (P₀).endAddress base<2^Wd:=by
    change (s).stemSources.endAddress base<2^Wd at space
    rwa [schedule] at space
  have regs:=registers_issued B (receivers) base u.originalBasis mem orig (bias) header chip self chosen saved limit
    cs bf hd sign sels head metaPos
  simp only [CandidateSheets.coordinateEnd,schedule,reduced]
  exact ⟨regs.1,regs.2.1,regs.2.2.1,regs.2.2.2.1,regs.2.2.2.2.1,regs.2.2.2.2.2.1,
    regs.2.2.2.2.2.2,fun x j r h vv hh=>congrArg _ (signAt x j r h vv hh),
    fun r vv hh=>congrArg _ (selfAt r vv hh)⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
