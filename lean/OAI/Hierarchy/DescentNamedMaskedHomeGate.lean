import OAI.Hierarchy.DescentNamedPrivateArchive
import OAI.Hierarchy.DescentTerminalMaskCounter
import OAI.Hierarchy.DescentTerminalPrivateRowsVolume
import OAI.Hierarchy.DescentTerminalPrivateReferences
import OAI.Hierarchy.DescentTerminalPrivateArguments
import OAI.Hierarchy.DescentPrivateNativeReplay

namespace OAI
/-! # The mounted terminal mask and the authentic named branch's scalar -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentKernelHistory DescentBundleHistory DescentHistoryOrder DescentCompiler DescentHostDegree DescentInitialHost Catalyst
open Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalObservedExponent Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "epochGraph" => ((Epochs.finish G hu he r).state c).graph
variable (sh : WorldShape p R (Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).bit)
local notation "row" => fun v=>(sh.sites v).recipe hp


open DescentTerminalRecipeRows DescentTerminalVertexFields DescentTerminalGraphPositions DescentTerminalSiteShelves DescentTerminalChronologicalBooks
open ThreeFlat.RAM PhysicalProcedure
variable {t₀ q₀ HN NN AN wb K : ℕ}
local notation "homes" => S.hostSize S.length
local notation "terminalGroups" => S.groupCount S.length
variable (L : Order ((Epochs.finish G hu he r).state c).graph (S.hostSize S.length) p) (byHome : L.home=b.target.home)
local notation "birth" => fun v=>((Branch.localNodes X G S b hp) v).toEmbedding.trans Fin.valEmbedding
local notation "real" => fun v=>(row v).restricted
variable (label : ((Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).bit.Tag×List (List SliceCode))→Fin t₀)
local notation "recipes" => DescentTerminalBundleRows.recipes L real hp birth label
variable {V B : ℕ} (banks : MaskAllocation.Channels (2^k)) (base header : ℕ)
local notation "cap" => cohortSize (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (w:=p) (groups:=terminalGroups) (blocks:=2^k)
local notation "size" => channelSize (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (w:=p) (groups:=terminalGroups) (blocks:=2^k)
local notation "cells" => MaskAllocation.marks size+cap
local notation "C₀" => MaskAllocation.counter (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (p:=p) (groups:=terminalGroups) banks base
local notation "O" => PrivateCounter.registers C₀ header homes cap
local notation "values" => measured (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (w:=p) (groups:=terminalGroups) (C₀).layout

variable (fit : V * DescentTerminalVertexFields.span q₀ t₀ HN NN AN p ≤ B)
local notation "stamp" => MaskAllocation.program (groups:=terminalGroups) (blocks:=(2^k)) fit wb base
local notation "printed" => MaskAllocation.image (groups:=terminalGroups) (blocks:=(2^k)) fit base
local notation "machine" => PrivateCounter.machine (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (p:=p) (groups:=terminalGroups) («homes»:=homes) (bw:=wb) C₀ O
local notation "emit" => PrivateCounter.rawFinal (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (p:=p) (groups:=terminalGroups) («homes»:=homes) C₀ O
variable (calendar : Chronology.MeterCalendar b.origin.source header wb b.path)
    (publish : Chronology.NativePhase wb) (input : Memory wb)
local notation "reached" => calendar.memory input
local notation "source" => publish.image reached

attribute [local irreducible] PrivateCounter.machine PrivateCounter.rawFinal MaskAllocation.literal Origin.archivePackage Origin.source
set_option cleanup.letToHave false

private theorem chain_execution {w : ℕ} {first second : Procedure w} {m₀ m₁ m₂ : Memory w}
    {a b : ℕ} (left : first.Exec m₀ m₁ a) (right : second.Exec m₁ m₂ b) :
    (first.seq second).Exec m₀ m₂ (a+b) :=
  @Procedure.Exec.then w first second m₀ m₁ m₂ a b (@left) (@right)

private theorem count_parts {a b c : ℕ} (parts : a + b = c) : a ≤ c ∧ c - a = b ∧ b ≤ c := by omega

set_option maxHeartbeats 800000 in
theorem masked_private_gate_arguments (ready : calendar.Ready K input) (issued : publish.Runs reached)
    (keep : source header=reached header)
    (rank : ∀i,Birth (recipes i))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden≤HN)
    (hN : ∀i v,Fintype.card (recipes i v).Node≤NN)
    (hA : ∀i v u,(recipes i v).arity u≤AN)
    (hw : ∀i v u,(recipes i v).width u≤p)
    (short : ∀i v,(L.site i).arity v≤q₀)
    (occupied : ∀(i : Fin homes) c,blankAt (values source i) c≠0 ↔ ∃u,b.target.chart L byHome i u=c)
    (previous : ∀i v,let book:=record (L.site i) (recipes i) (rank i) (hH i) (hN i) (hA i) (hw i) (short i) v
      ArgumentReads (venueField (cellAt (values source i) (b.target.rawResident L byHome i v))) (fun j=>(value book j).val))
    (prior : ∀f,(banks.bank f).base+(banks.bank f).size≤base) (safe : header<base)
    (endAt : base+cells+cap+homes+homes+3<2^wb)
    (widthFit : Nat.log 2 (NativeBranch.privateMax G S p)+1≤wb) :
    let out:=emit (printed source)
    ((calendar.program.seq publish.program).seq ((stamp).seq machine)).Exec input out
       ((calendar.ticks+publish.ticks)+TerminalScale.privateMaskedClock cells cap homes (2^k) p) ∧
    ProtocolRAM.CheapCode ((calendar.program.seq publish.program).seq ((stamp).seq machine)) ∧
    out (O).deadBits=((deadCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites:ℕ):Computability.VPVNP.BurstRAM.Word wb) ∧
    MountedMask (groups:=terminalGroups) (C₀).layout out fit ∧
    (∀f z,(banks.bank f).read out z=(banks.bank f).read source z) ∧
    ∀(assign : (epochGraph).Assignment) (x : Ports _), (∏v,(epochGraph).read ((Epochs.finish G hu he r).state c).tables assign x v)=
      (∏j:Fin wb,if (out (O).deadBits).val.testBit j.val then (2:F)^(2^j.val) else 1)*
      ∏v,(row v).restricted.value (bundleScalar p (Branch.archive X G S b hp).bit.scalar)
        (fun arg=>wordList (fun j=>bitInput epochGraph assign x v (arg.atBit j))) := by
  obtain ⟨past,held,_⟩:=calendar.run K input ready
  have total :
      (∑i:Fin homes,privateHome (values source i))=liveCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites := calc
    _ = ∑i,∑v,Fintype.card (recipes i v).UsedWord := by
      apply Finset.sum_congr rfl
      intro i _
      exact b.target.private_home_arguments L byHome i _ (recipes i) (rank i) (hH i) (hN i) (hA i)
        (hw i) (short i) (occupied i) (previous i)
    _ = _ := DescentTerminalBundleRows.private_rows_volume epochGraph L hp row birth label
  have partition:=DescentTerminalObservedExponent.partition hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites
  obtain ⟨liveFits, leftOver, deadFits⟩ := count_parts partition
  have lower : (∑i:Fin homes,privateHome (values source i))*p≤volume epochGraph (Branch.archive X G S b hp).bit.recipe := by
    rw [total]
    exact liveFits
  obtain ⟨last,cheap,read,rom,preserved⟩:=MaskAllocation.terminal (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (p:=p)
    (groups:=terminalGroups) (blocks:=2^k) (sites:=homes) (V:=V) (B:=B) (bw:=wb) banks base header fit source
    (volume epochGraph (Branch.archive X G S b hp).bit.recipe) prior safe endAt (keep.trans (Branch.held_volume X G S b hp held)) lower
  rw [total, leftOver] at read
  have executed := @chain_execution wb (calendar.program.seq publish.program) ((stamp).seq machine)
      input source (emit (printed source)) (calendar.ticks+publish.ticks)
      (TerminalScale.privateMaskedClock cells cap homes (2^k) p)
      (@chain_execution wb calendar.program publish.program input reached source calendar.ticks publish.ticks (@past) (@issued)) (@last)
  have evaluates : ∀(assign : (epochGraph).Assignment) (x : Ports _), (∏v,(epochGraph).read ((Epochs.finish G hu he r).state c).tables assign x v)=
      (∏j:Fin wb,if ((emit (printed source)) (O).deadBits).val.testBit j.val then (2:F)^(2^j.val) else 1)*
      ∏v,(row v).restricted.value (bundleScalar p (Branch.archive X G S b hp).bit.scalar)
        (fun arg=>wordList (fun j=>bitInput epochGraph assign x v (arg.atBit j))) := by
    intro assignment x
    have bound:=Branch.private_max X G S b hp
    have capBound:NativeBranch.privateMax G S p<2^wb:=(Nat.lt_pow_succ_log_self (by decide) _).trans_le
      (Nat.pow_le_pow_right (by decide) widthFit)
    have lim : deadCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites < 2^wb :=
      (deadFits.trans bound).trans_lt capBound
    dsimp only
    rw [read,Fin.val_cast_of_lt lim]
    exact fixed_powers hp epochGraph (Branch.archive X G S b hp).bit.scalar (Branch.archive X G S b hp).bit.recipe ((Epochs.finish G hu he r).state c).tables (Branch.archive X G S b hp).bit.correct sh.sites assignment x wb lim
  exact ⟨@executed, @ProtocolRAM.cheap_seq wb _ _ (@ProtocolRAM.cheap_seq wb _ _ (@calendar.cheap) (@publish.cheap)) (@cheap),read,rom,preserved,evaluates⟩

set_option maxHeartbeats 800000 in
theorem masked_private_gate (ready : calendar.Ready K input) (issued : publish.Runs reached)
    (keep : source header=reached header)
    (rank : ∀i,Birth (recipes i))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden≤HN)
    (hN : ∀i v,Fintype.card (recipes i v).Node≤NN)
    (hA : ∀i v u,(recipes i v).arity u≤AN)
    (hw : ∀i v u,(recipes i v).width u≤p)
    (short : ∀i v,(L.site i).arity v≤q₀)
    (occupied : ∀(i : Fin homes) c,blankAt (values source i) c≠0 ↔ ∃u,b.target.chart L byHome i u=c)
    (previous : ∀i v j,let record:=record (L.site i) (recipes i) (rank i) (hH i) (hN i) (hA i) (hw i) (short i) v
      allows (fun f=>(value record f).val) j → venueField
        (cellAt (values source i) (b.target.rawResident L byHome i v)) j=(value record j).val)
    (prior : ∀f,(banks.bank f).base+(banks.bank f).size≤base) (safe : header<base)
    (endAt : base+cells+cap+homes+homes+3<2^wb)
    (widthFit : Nat.log 2 (NativeBranch.privateMax G S p)+1≤wb) :
    let out:=emit (printed source)
    ((calendar.program.seq publish.program).seq ((stamp).seq machine)).Exec input out
       ((calendar.ticks+publish.ticks)+TerminalScale.privateMaskedClock cells cap homes (2^k) p) ∧
    ProtocolRAM.CheapCode ((calendar.program.seq publish.program).seq ((stamp).seq machine)) ∧
    out (O).deadBits=((deadCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites:ℕ):Computability.VPVNP.BurstRAM.Word wb) ∧
    MountedMask (groups:=terminalGroups) (C₀).layout out fit ∧
    (∀f z,(banks.bank f).read out z=(banks.bank f).read source z) ∧
    ∀(assign : (epochGraph).Assignment) (x : Ports _), (∏v,(epochGraph).read ((Epochs.finish G hu he r).state c).tables assign x v)=
      (∏j:Fin wb,if (out (O).deadBits).val.testBit j.val then (2:F)^(2^j.val) else 1)*
      ∏v,(row v).restricted.value (bundleScalar p (Branch.archive X G S b hp).bit.scalar)
        (fun arg=>wordList (fun j=>bitInput epochGraph assign x v (arg.atBit j))) :=
  masked_private_gate_arguments X G S b hp sh L byHome label banks base header fit calendar publish input
    ready issued keep rank hH hN hA hw short occupied
    (fun i v=>ArgumentReads.of_allowed (previous i v)) prior safe endAt widthFit

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
