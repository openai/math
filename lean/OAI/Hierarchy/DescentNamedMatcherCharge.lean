import OAI.Hierarchy.DescentNamedMatcherInvoice
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! # Paid word tariff for the original dated rotation matcher -/
namespace Hierarchy.DescentSixParty.Chronology
variable {F : Type} [Field F]

noncomputable def matcherChargeRate (G : PoweredGadget F) (t f g reset : ℕ) :=
  let rates:=donorRates G t f g reset
  (rates.work+3)*5+rates.amount+41

end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {run : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he run).Choice}
  (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port pins X.width)))
    (fun _ => S.firstWidth G.b p * 1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    {T : StageInput W G rate (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k (i+1) z' D'
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement

variable (payload seats ratio w floor : ℕ) (input : Operands) (hk : 0<k)
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "board" => S.censusBits p
local notation "a₀" => (d₀).schedule payload seats board
local notation "vals" => measuresAt S G.b p i
local notation "r" => 2^k
local notation "K" => 2^(k+1)
local notation "H" => hostRows (S.hostSize i)
local notation "u₀" => (d₀).amount
local notation "b₀" => (a₀).shapeAt.outputBits*(a₀).lanesAt
local notation "N₀" => (K*H)*chunks (S.groupCount i) (a₀).lanesAt

include ticket before tail cut in
theorem matcher_charge {t J reset M frozen : ℕ}
    (schedule : S=stageNumbers G t J f g reset M frozen)
    (depth : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (room : MatcherRoom G S k p payload)
    (fits : (a₀).Space input w floor) (word : w≤ratio*payload)
    (column : ∀x : Fin r,∃b : Bank,input.atoms x.val=ProtocolRAM.Expr.lookup b .row) :
    DateBill.bitTariff ((a₀).program G hk input vals w floor) ((a₀).ticks G hk input vals w floor) ≤
      (S.hostSize i*payload+S.hostSize i*(S.groupCount i*S.radix))*
        (ratio*scale J (matcherChargeRate G t f g reset)) :=by
  let zero : Bank:=⟨0,0⟩
  have paired:=matched_count_paid X G S br ticket before tail cut payload seats ratio w floor input hk
    fits word zero (fun _=>0) 0 schedule depth room column
  exact DateBill.matcher_tariff_factor _ _ _ _ _ _ ratio J _ _ paired

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
