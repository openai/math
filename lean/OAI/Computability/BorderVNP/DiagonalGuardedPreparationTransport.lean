import OAI.Computability.BorderVNP.DiagonalGuardedPreparedColumn

/-! # Guarded packets along the original preparation equality -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier ResidueRates
open DiagonalResidueRAM VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader RoutingISA.Evaluator
open CompactMachine CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical BigOperators
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 3000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {common : CommonField G aux q k s ord} {chart : AdvisedBranch common}
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    {R r mult w pin : ℕ} (reader : ChosenReader chart (R+1) r mult w w pin)
local notation "bits" => (pairedTableParameters (k+1) s+2)*pin
local notation "query" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pin w (G.Entry ⊕ ι))
local notation "dim" => pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)

variable (l : SignedTaskArena.Layout) (A : StartupArena)
    {sites time link inner n : ℕ} {Edge : Type}
    (wire : Wiring R sites time ((pairedTableParameters (k+1) s+2)*pin) link inner n Edge)
    {pub : Fin (R+1) → Arg → Word w} {regs : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    (col : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool)
    (boot : (x : {ext // PositiveExterior wire args col w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver wire pub regs args col x.val u)
    (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst)
open Routing BootedPinStart

/-- Transport the protected packet using the identified physical preparation.
The equality determines the original routed inverse and all report witnesses. -/
theorem ChosenReader.preparedPacketsAlong
    {Hist : Type}
    {reserve groups capacity digits : ℕ}
    {L : WireLayout (R+1) sites link} {headerWidth : L.header=PositiveFields.width reserve l.cube.n groups capacity (R+1) dim digits}
    {enc : Hist ↪ (Fin reserve → Bool)} {fixed : Block (R+1)} {hw : 0<w}
    {size : ∀ u, (args u).header=L.header} {base : Fin (R+1) → ℕ}
    {fit : ∀ u,(wire.transferFrame u (args u).header (args u).dst).Fits w (base u)}
    (decoder : PreparedHistoryDecoder SparseExterior.driver l.id wire pub regs col L headerWidth enc args fixed hw size base fit boot)
    (issued : reader.GuardedIssuedDecoder l A wire col boot limit burst cap decoder)
    (run : (x : {ext // PositiveExterior wire args col w ext ∧ PinStart.preCallSupport (fun z u => (boot z u).start) l.id ext}) →
      (u : Fin (R+1)) → let b := boot ⟨x.val,x.property.1⟩ u
        PositiveContinuation l.id SparseExterior.driver n (pub u)
          (TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n))
          b.start.bank b.memory b.pins b.used limit)
    {Route : Hist → Type} {Report : (Fin bits → Bool) → (h : Hist) → Route h → Type}
    {routed : ∀ (i : Fin bits → Bool) (h : Hist) (claim : Fin ((R+1)*dim*digits) → Bool),
      (Σ c : Physical.Broadcast l.cube.n groups capacity,
        ParsedPreCall wire args col L fixed hw size base fit headerWidth (fun x u => (boot x u).start)
          (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase)
          (fun _ _ => rfl) l.id i ⟨enc h,c,claim⟩) ≃ Σ v : Route h,Report i h v}
    {prep : JointBeforeCells (BootedPinStart.supportedTeam l.id boot limit burst cap run) ≃
      PreparedFields (Fin bits → Bool) Hist (Fin ((R+1)*dim*digits) → Bool) Route Report}
    (same : prep = (decoder.supported limit burst cap run Route Report routed).val) :
    reader.GuardedPreparedColumn l A wire col boot limit burst cap run reserve groups capacity digits prep := by
  rw [same]
  refine fun {Private} => ?_
  exact reader.preparedPacketsOnIssued l A wire col boot limit burst cap decoder issued run routed (Private:=Private)

end Diagonal

end BorderVNP
end Computability
end OAI
