import OAI.Hierarchy.DescentNamedPurchasedOrdinaryBooks
import OAI.Hierarchy.DescentOrdinaryBarePlan

namespace OAI
/-! # The input operand plan of an issued ordinary date -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option hygiene false
set_option quotPrecheck false
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height



variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "start" => PhysicalOrdinary.StaticCore.profileStart G S g k i p payload seats root

local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster
local notation "paid" => (StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i ports.venue.lanes).paidBits


local notation "clip" => OrdinaryBooks.purchaseClip G books core ports paid
local notation "purchased" => OrdinaryBooks.purchased G books core ports paid
local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "argData" => PhysicalOrdinary.bareData G S i payload seats start (S.censusBits p)
  ports core purchased clip
local notation "cap₀" => Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift)
local notation "m₀" => (base).registered_match ports ((base).stageStart root) cap₀
local notation "actual" => (v).bareArguments ((base).stageStart root) entry m₀

include before tail cut in
theorem registered_bare_at : ∃h:(argData).Valid,actual=(argData).plan h :=by
  have fixed:=registered_static_core X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  obtain ⟨bought,clipped⟩:=registered_purchased_books X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  let floor:=(base).stageStart root
  let a:=PhysicalOrdinary.bareData G S i payload seats floor (S.censusBits p)
    ports ((base).staticCore floor) (v).books (entry).clip
  have same : a=argData:=by
    dsimp only [a]
    change PhysicalOrdinary.bareData G S i payload seats start (S.censusBits p) ports ((v).staticCore start)
        (v).books (entry).clip=_
    have fixed' : (v).staticCore start = core := fixed
    rw [fixed',bought,clipped]
  let ok:a.Valid:=(base).registered_bare_valid ports floor cap₀
  exact ⟨same ▸ ok, ((base).registered_bare_plan ports floor cap₀).trans (a.plan_eq ok _ same)⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
