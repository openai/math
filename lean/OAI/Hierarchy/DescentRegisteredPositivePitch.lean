import OAI.Hierarchy.DescentNamedFundedBaseWidth
import OAI.Hierarchy.DescentNamedRegisteredSuffix
import OAI.Hierarchy.DescentRegisteredGeometry

namespace OAI
/-! # The resolver pitch of the actual ordinary date on a registered branch -/
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
local notation "feeMultiplier" => price*(wire:ℝ)
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
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
variable (op : RotorSpec) (frozen drift degree payload root : ℕ) (ports : DatePorts)
  (ordinary : ℕ → Ordinary) {bn bd : ℕ} (board : NonlinearExpanders.Graph bn bd)
  (atSeats prices : ℕ → ℕ) (header : ℕ)
local notation "b" => (⟨board,op,g,frozen,p,f,drift,degree,payload,atSeats,ordinary,prices,header⟩ : RegisterTimeline.Menu bn bd)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload (atSeats i) ports
local notation "model" => (books).onTicket ticket g frozen p f payload (atSeats i) ports.venue.lanes ports.io.roster ordinary
local notation "actual" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary

variable {t reset τ β copies driftR degreeMax ratio : ℕ}
local notation "J" => Nat.log 2 payload/(2*β)
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "funds" => 44*argumentDigitRate G t f g reset driftR baseRate

include before tail cut in
/-- Both native lane bounds follow from the actual public calendar rates and the
preceding archive, including on a prefix that terminates at the current date. -/
theorem registered_geometry_pitch {w : ℕ}
    (cells : RegisterTimeline.Geometry G S b k w i ⟨ports,root⟩)
    (purchase : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g reset driftR funds τ β ratio payload)
    (schedule : S=stageNumbers G t J f g reset copies frozen)
    (depth : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (cutoff : frozen=TerminalScale.tail τ J) (dr : drift+1 ≤ scale J driftR)
    (reach : degree≤degreeMax) (digits : p≤payload) (original : S.firstWidth G.b p≤payload)
    (live : 0<p) :
    0<(actual).resolver.lanes ∧ (actual).resolver.lanes≤payload/2 :=by
  have base:=registered_base_width X G S br ticket before tail cut op frozen drift degree payload
    (atSeats i) ports.venue.lanes ports ports.io.roster ordinary purchase schedule depth digits
  have rows:=registered_row_room X G S br ticket before tail cut op frozen drift degree payload
    (atSeats i) ports.venue.lanes ports ports.io.roster ordinary ((model).stageStart root) purchase returns
    schedule depth cutoff dr base reach digits original cells.room.archive cells.room.args live
  exact ⟨rows.1,rows.2.1⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
