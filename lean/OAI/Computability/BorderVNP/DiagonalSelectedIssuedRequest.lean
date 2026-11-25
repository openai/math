import OAI.Computability.BorderVNP.DiagonalSelectedIssuedExecution

/-! # The type of an issued execution at the selected residue index -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments BorderVNP.Cube
open Branch ResidueBox ResidueIndex ResiduePins
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3500000
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000
variable {D m : ℕ} [NeZero D] {K F : Type} [Field K] [Field F] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pin link k d a rw ec s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work) (cube : FixedCube F) (φ : F →+* K)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {qchar : ℕ}
    {common : CommonField e (φ ∘ cube.table) qchar k s ord} (chart : AdvisedBranch common)
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (fit : 2*((UniversalMachine.programPrefix (cube.signedSiteProgram e)).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r 64 rw ec (rw+1) ≤ k+1)
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d order position copies).Tables K)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
variable (hp : (fieldSewParams (SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) (cube.signedSiteProgram e) fit free ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d).Valid)
    (α ξ : ℝ) (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix (cube.signedSiteProgram e)).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)
open RoutingISA RoutingISA.Evaluator RoutingISA.CellDispatch TeamContraction.ProcessorSlots
open TeamContraction.JointHeader DiagonalTallyCellReports CellMacro.Generator VPVNP.BurstRAM VPVNP.VerifierNetwork
variable (parameters : SignedTaskArena.Parameters) (arenaBase profileBits : ℕ)
    (frame origin : Fin (R+1) → ℕ)
    {σ : Type} [Fintype σ] (input : σ → Bool)
    (initial : ((plan.execute (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k) (a:=a) (cube.signedSiteProgram e) fit ((pairedTableParameters (k+1) s+2)*pin)) order position σ).choose).eval input = words)
    (widths : ℕ → ℕ) (slots : ∀ i, EnrichedOuter.Machine.Guess S (d+1) (fun _ _ => 60*logWidth r (k+1)) i ≃ Fin (widths i))
    (fits : broadcastWidth (fan S) widths T ≤ profileBits)
variable {mult : ℕ} (reader : ChosenReader chart (R+1) r mult rw rw pin)
    (pub : Fin (R+1) → Arg → Word rw) (reg : Fin (R+1) → Bank rw) (args : Fin (R+1) → UnitAddresses)
    (limit burst : ℕ) (privateSize : TeamScales.width (k+1) (1/2) ≤ burst)
    (j : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (k+1) s)) (chart.pinRadius (R+1) r))

attribute [local irreducible] Nat.clog UniversalMachine.programPrefix

include plan cube φ ord chart fit W position sites edges ports table words good seeds free count hp α ξ
  calibrated lit hd number parameters arenaBase profileBits frame origin input initial widths slots fits
  reader pub reg args limit burst privateSize j

local notation3 (prettyPrint := false) "requestAt" => @selectedIssuedExecution D m _ K F _ _ e S
  R r pin link k d a rw ec s copies T header work plan cube φ ord qchar common chart _ _ fit
  order W position ns ne np sites edges ports table words good seeds free count hp α ξ calibrated lit hd
  cells number parameters arenaBase profileBits frame origin σ _ input initial widths slots fits mult reader
  pub reg args limit burst privateSize j

/-- The six receipts and boot data left by the issued evaluator at one chosen reader pin. -/
noncomputable def SelectedIssuedRequest : Type _ := type_of% (requestAt)

/-- Apply the original selected execution at this pin using its named type. -/
noncomputable def selectedIssuedRequest :
    @SelectedIssuedRequest D m _ K F _ _ e S R r pin link k d a rw ec s copies T header work plan cube φ ord
      qchar common chart _ _ fit order W position ns ne np sites edges ports table words good seeds free count
      hp α ξ calibrated lit hd cells number parameters arenaBase profileBits frame origin σ _ input initial
      widths slots fits mult reader pub reg args limit burst privateSize j :=
  requestAt

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
