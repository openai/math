import OAI.Hierarchy.DescentProfiledPrefixCensus
import OAI.Hierarchy.DescentRegisteredOrdinaryHeaderWriter
import OAI.Hierarchy.DescentRegisterCutInduction
import OAI.Hierarchy.DescentPhysicalSignedLayout
import OAI.Hierarchy.DescentDatedRoutedArguments
import OAI.Hierarchy.DescentOrdinaryRegisteredWordRoom

namespace OAI
/-! The printed cable serial, neighbor, flattened argument and grain fit the two
actual word formats of an ordinary dated resolver. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentOperandWidth DescentDatedPublicGrain DescentSIMDLookup
open scoped Fin.CommRing
noncomputable section
set_option maxHeartbeats 1200000
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)

local notation "S" => v.schedule
local notation "G" => v.gadget
local notation "phys" => v.withIssuedSigned

/-- The dated grain is an actual short number in the registered resolver. -/
theorem original_grain {tail drift degree p:ℕ} (hp:0<p) (branch:(G).b≤2^(S).capGain)
    (dateGrain:v.z=(S).grainAt (G).b p v.age) (size:v.resolver.size+2=recordBits G S v.k tail drift degree p) :
    (phys).chosenGrain.val=v.prior.placement.stage.z/p:=by
  have room (a:ℕ) (le:a≤bound G S drift degree) : a<2^(v.resolver.size+2):=by
    rw [size]
    exact (numeric (k:=v.k) (tail:=tail) (degree:=degree) G S le).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
  have rawRoom:raw S≤bound G S drift degree:=(Nat.le_max_left ..).trans
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have capRoom:publicCap S≤raw S:=by unfold raw; omega
  have phase:(S).rounds*(S).height-(S).ordinaryDone v.age≤(S).length:=
    (Nat.sub_le ..).trans (Nat.mul_le_mul_right (S).height (Nat.le_succ (S).rounds))
  have grainRoom:amount S (G).b v.age≤publicCap S:=calc
    _ ≤ (2^(S).capGain)^((S).rounds*(S).height-(S).ordinaryDone v.age):=Nat.pow_le_pow_left branch _
    _ = 2^((S).capGain*((S).rounds*(S).height-(S).ordinaryDone v.age)):=(pow_mul ..).symm
    _ ≤ publicCap S:=Nat.pow_le_pow_right (by decide)
      ((Nat.mul_le_mul_left _ phase).trans (Nat.le_add_left ..))
  have grainFit:=room _ (grainRoom.trans (capRoom.trans rawRoom))
  change ((amount S (G).b v.age:Cell (v.resolver.size+2))).val = v.prior.placement.z/p
  rw [Fin.val_natCast,Nat.mod_eq_of_lt grainFit,v.prior.grain,dateGrain,bits_per_bundle,
      Nat.mul_div_cancel_left _ hp]
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
set_option maxHeartbeats 1200000
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)


set_option hygiene true
attribute [local irreducible] SeedNamed.issued
variable (walk : (last).Choice)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}

theorem ordinary_original_grain {U : MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q₀:ℝ} {he₀:0≤fee}
    {r:Reached U G price fee S k i z D ((S).epochPower^(S).priceExponent) s} {stage:StageInput U G q₀ fee}
    {pick:(stage.result he₀).Choice} {norm:Normalize ((stage.result he₀).state pick)}
    {next:Reached norm.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink r he₀ stage pick norm next) (before:Path (trace walk).origin.source r)
    (after_:Path next (trace walk).target) (located:(before.ordinary ticket).append after_=(trace walk).path)
    (ports:DatePorts) (op:RotorSpec) (tailBits drift degree payload seats root:ℕ)
    (schedule:ℕ→Dated.Ordinary) :
    let v:=DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root schedule
    v.withIssuedSigned.chosenGrain.val=r.placement.stage.z/p:=by
  let v:=DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root schedule
  have joined:before.append ((Path.here.ordinary ticket).append after_)=(trace walk).path:=
    (Path.append_cut_assoc before (Path.here.ordinary ticket) after_).symm.trans located
  let t := traceAt X G S ordinary reset branch positive room shorten walk
  have tk : t.path.kinds = kindCalendar S.rounds S.height := by
    dsimp only [t, traceAt]
    exact (trace walk).kinds
  have tf : t.firstGrain = S.grainAt G.b p 0 := by
    dsimp only [t, traceAt]
  let atFirst : Path t.first r := by
    dsimp only [t, traceAt]
    exact before
  let atLast : Path r t.last := by
    dsimp only [t, traceAt]
    exact (Path.here.ordinary ticket).append after_
  have atTrace : atFirst.append atLast = t.path := by
    dsimp only [t, traceAt, atFirst, atLast]
    exact joined
  have grain : z = S.grainAt G.b p i := Path.snapshot_cut_grain
    (t:=t) (r:=r) (p:=p) tk tf atFirst atLast atTrace
  exact v.original_grain positive branch grain
    (OrdinaryBooks.record_width G S op g k i p tailBits drift degree payload seats ports).1

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
