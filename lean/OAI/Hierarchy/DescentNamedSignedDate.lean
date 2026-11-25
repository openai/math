import OAI.Hierarchy.DescentNamedDonorCode
import OAI.Hierarchy.DescentSignedStageFormat
import OAI.Hierarchy.DescentIncomingHosts
import OAI.Hierarchy.DescentCapCalendarPositive

namespace OAI
/-! # The signed plane is chosen before any of the date's profiles are read -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage.Dated

def atDate {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (gain k i newHosts : ℕ) : SignedStage :=
  let a:=forAge S G.b gain k i (Nat.clog 2 (S.hostSize i)) 1 0 0 0 0
  ⟨k,a.D,a.cap,ordinaryDegree a.D,2^DescentHostDegree.gainExponent 20 a.D*G.b*a.cap,
    hostRows (S.hostSize i),newHosts,S.groupCount (i+1),G.b,G.C,G.k⟩

/-- The very same host bound consumed by the following ordinary/reset event or
the final frozen roster; it depends only on the original calendar. -/
def signedAt {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (gain k i payload : ℕ) : DescentDatedAddressBook.SignedExtent :=
  (atDate G S gain k i (NativePitch.incomingHosts S (i+1))).format payload

end Hierarchy.DescentDatedAddressBook.SignedStage

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height


include ticket before tail cut in
theorem signed_source_capacity : 256≤prior.placement.cap := by
  have shape:=ordinary_geometry X G S br ticket before tail cut 0 1 0 0 0 0
  have physical:=congrArg Ordinary.cap shape
  dsimp only [forAge, Ordinary.cap] at physical
  have paid:=G.paid
  have live : 0<G.b:=by omega
  have prefixLive:=DonorDate.prefix_cap_pos G.b S.rounds g S.height i live
  rw [physical]
  exact Nat.le_mul_of_pos_left 256 prefixLive

include ticket before tail cut in
theorem signed_stage_eq (newHosts : ℕ) :
    (⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      hostRows (S.hostSize i),newHosts,S.groupCount (i+1),G.b,G.C,G.k⟩ : SignedStage)=
      SignedStage.atDate G S g k i newHosts := by
  let ℓ:=Nat.clog 2 (S.hostSize i)
  let a:=forAge S G.b g k i ℓ 1 0 0 0 0
  have metrics:=ordinary_geometry X G S br ticket before tail cut ℓ 1 0 0 0 0
  have degree : prior.placement.degree=a.D:=congrArg Ordinary.D metrics
  have cap : prior.placement.cap=a.cap:=congrArg Ordinary.cap metrics
  have oldD : D=a.D:=prior.branch.symm.trans degree
  have newD : next.placement.degree=ordinaryDegree a.D :=
    next.branch.trans (ticket.nextDegree.trans (congrArg ordinaryDegree oldD))
  have newCap : next.placement.cap=2^DescentHostDegree.gainExponent 20 a.D*G.b*a.cap := by
    exact ticket.capacity.trans (congrArg₂
      (fun d c => 2^DescentHostDegree.gainExponent 20 d*G.b*c) oldD cap)
  change SignedStage.mk _ _ _ _ _ _ _ _ _ _ _=SignedStage.mk _ a.D a.cap _ _ _ _ _ _ _ _
  rw [degree,cap,newD,newCap]

include ticket before tail cut in
theorem signed_format_eq (newHosts payload : ℕ) :
    let actual : SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      hostRows (S.hostSize i),newHosts,S.groupCount (i+1),G.b,G.C,G.k⟩
    actual.format payload=(SignedStage.atDate G S g k i newHosts).format payload :=
  congrArg (fun a : SignedStage=>a.format payload) (signed_stage_eq X G S br ticket before tail cut newHosts)

include ticket before tail cut in
theorem signed_at (payload : ℕ) :
    let H':=NativePitch.incomingHosts S (i+1)
    let actual : SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      hostRows (S.hostSize i),H',S.groupCount (i+1),G.b,G.C,G.k⟩
    actual.format payload=SignedStage.signedAt G S g k i payload :=
  signed_format_eq X G S br ticket before tail cut _ payload

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
