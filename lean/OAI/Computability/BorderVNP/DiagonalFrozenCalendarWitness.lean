import OAI.Computability.BorderVNP.DiagonalChosenSignedCalendar
import OAI.Computability.BorderVNP.DiagonalFixedSignedWitness
import OAI.Computability.BorderVNP.PackedLocatedFrozenTable

/-! # The original verifier and terminal source selected before all live pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 7000
set_option maxHeartbeats 1900000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "n₁" => l+1
local notation "r₁" => stretch b.ρ (l+1)
local notation "size₁" => stretch b.σ (l+1)
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "ξ₁" => (scales.τ:ℝ)/5
local notation "ℓ₁" => TeamScales.link (ξ₁) (R₁+1) (l+1)
local notation "ec₁" => Wires.sortExponent (block (ξ₁) (l+1))
local notation "budget₁" => adv (adviceScale b.σ b.ρ (l+1))
local notation "pins₁" => (pairedTableParameters (l+1) (size₁)+2)*(budget₁+6)
local notation "d₁" => CoverScale.initialDepth (Cube D) (r₁) (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

/-- The chosen physical scale and original named query are fixed even before
the finite field chart is supplied. Its slot count already uses the true
coefficient-reader input length of this batch. -/
noncomputable def SignedCalendarAt.frozenWitness :
    WiredWitness (tape₁) (Fin.last l) D axes (d₁) (order₁)
      (0 : ParseTable.State (Fin (l+1) × Bool) (size₁)) :=
  (cal.length.fixed_signed_query cube b axes (d₁) (pins₁) (order₁) (geo₁)).choose

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

local notation3 (prettyPrint := false) "blank₀" => (cal.blank chart reader chargeFit).choose

private theorem signed_link_length : b.physical.link (l+1) = ℓ₁ := by
  have sizes := b.sizes (Nat.succ_pos l)
  rw [sizes.1]
  exact sizes.2.1

/-- One header-only wire layout on the actual processor link serves all
original histories of this reader. -/
noncomputable def SignedCalendarAt.frozenLayout : Routing.WireLayout (R₁+1) (r₁) (ℓ₁) :=
  (signed_link_length (b:=b) (l:=l)) ▸ (blank₀)

/-- Transporting the header to the exact processor link preserves its
length and zero initial traffic. -/
theorem SignedCalendarAt.frozenLayout_fields :
    let L := cal.frozenLayout chart reader chargeFit
    let symbols := _root_.OAI.Computability.BorderVNP.Cube.alphabet scales.α (l+1)
    let traffic := (R₁+1)*TeamScales.exterior (ξ₁) (r₁) (l+1)
    let blocks := _root_.OAI.Computability.BorderVNP.Cube.Physical.blocksFor traffic (cube.h*cube.b) (symbols^(cube.pred+1))
    let cap := _root_.OAI.Computability.BorderVNP.Cube.Physical.declarationCap cube.pred symbols blocks cube.b cube.h cube.width
    let dim := pairedTableParameters (l+1) (size₁)+
      Fintype.card (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    L.header = JointHeader.PositiveFields.width (SeedPlan.profileReserve (r₁) (l+1)) cube.pred symbols cap
      (R₁+1) dim (b.physical.tally (l+1)) ∧ 0<L.header ∧ L.width=(fun _ _ => 0) := by
  have fields := (cal.blank chart reader chargeFit).choose_spec
  dsimp only
  have transport {R r x y : ℕ} (eqn : x=y) (L : Routing.WireLayout R r x) :
      (eqn ▸ L : Routing.WireLayout R r y).header=L.header ∧
      (eqn ▸ L : Routing.WireLayout R r y).width=L.width := by cases eqn; exact ⟨rfl,rfl⟩
  let kept := transport (signed_link_length (b:=b) (l:=l)) (blank₀)
  exact ⟨kept.1.trans fields.1,kept.1.symm ▸ fields.2.1,kept.2.trans fields.2.2.1⟩

end Diagonal

end BorderVNP
end Computability
end OAI
