import OAI.Computability.BorderVNP.DiagonalJointBootedSupport
import OAI.Computability.BorderVNP.DiagonalNativeWiredFiber

/-! # Building a live column from the actual booted and jointly returning teams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ChosenReader

open Branch Crossing ResidueBox ResiduePins ResidueIndex TeamContraction ProcessorSlots
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator BorderVNP.Cube
open scoped Classical BigOperators

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {e : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField e aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pin exp t link inner : ℕ} (reader : ChosenReader chart (R+1) r mult tally w pin)
    {Edge : Type} {dim box lanes selectors symbols : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)

local notation "h" => pairedTableParameters (k+1) s
local notation "Idx" => Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin h) (chart.pinRadius (R+1) r)
local notation "codec" => boxPinCodec h reader.rankFits reader.boxFits
local notation "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock (k+1))

variable (G : Wiring R r t ((pairedTableParameters (k+1) s+2)*pin) link inner (k+1) Edge)
    (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (limit burst : ℕ) (cap : TeamScales.width (k+1) (1/2) ≤ burst)
    (Path : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Type) [∀ raw, Fintype (Path raw)]
    (assigned : ∀ raw, Path raw → Tally (Fin (R+1)) (Fin (pairedTableParameters (k+1) s)) (e.Entry ⊕ ι) exp)

set_option maxRecDepth 4500
set_option maxHeartbeats 1300000

variable (j : Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin (pairedTableParameters (k+1) s)) (chart.pinRadius (R+1) r))
    (B : (x : {ext // PositiveExterior G args ((boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j) w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args ((boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j) x.val u)

local notation3 (prettyPrint := false) "active" => PinStart.preCallSupport (fun x u => (B x u).start) id
local notation3 (prettyPrint := false) "X" => {ext // PositiveExterior G args ((boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j) w ext ∧ active ext}

variable (next : (x : {ext // PositiveExterior G args ((boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j) w ext ∧
        PinStart.preCallSupport (fun z u => (B z u).start) id ext}) → (u : Fin (R+1)) →
      let bt := B ⟨x.val,x.property.1⟩ u
      PositiveContinuation id gen (k+1) (pub u) (TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock (k+1))) bt.start.bank bt.memory bt.pins bt.used limit)

local notation3 (prettyPrint := false) "teams" => BootedPinStart.supportedTeam id B limit burst cap next

/-- On the chosen reader pin the physical boot fixes the support, local
pin dictionaries, native program, rejection of every losing exterior and the
remaining clocks. The cell checks and the path bijection use the complete
tuple of jointly returning teams. -/
noncomputable def executionOfBoots (paid : ∀ x u, (B x u).used ≤ limit)
    (joined : (x : X) → (a : (u : Fin (R+1)) → (teams x u).Prefix) →
      JoinedCells (fun u => (teams x u).pub) (fun u => (teams x u).postMemory) (fun u => (teams x u).generated) a)
    (fiber : NativeColumnFiber reader teams joined Path assigned j) :
    reader.WiredPinExecution id gen G args mac pub reg limit burst Path assigned j :=
  ⟨active,BootedPinStart.product_zero id B limit burst ((k+1)^25),teams,joined,
    BootedPinStart.supportedTeam_value id B limit burst cap next paid,fiber⟩

end Diagonal.ChosenReader

end BorderVNP
end Computability
end OAI
