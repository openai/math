import OAI.Computability.BorderVNP.DiagonalFrozenPrefixFinishCalibration
import OAI.Computability.BorderVNP.DiagonalSupportedPostRate
import OAI.Computability.BorderVNP.DiagonalSelectedPostWindows
import OAI.Computability.BorderVNP.DiagonalNativeGeometryWindow

/-! # Post-call capacities of the selected signed geometry and reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales Filter DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins VPVNP VPVNP.BurstRAM
open RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena TeamContraction TeamContraction.JointHeader
open TeamContraction.ProcessorSlots GeometryAdvice _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

open PackedHistoryCircuit PackedHistoryCircuit.TerminalCells CellPacketGeometry Packing.RoutingOutputs VPVNP.VerifierNetwork

/-- At one length threshold, every admitted chart and frozen signed emitter
has the same public and local work windows. The capacities refer to the
actual task above its appended bank packet, including the separate reader
and the report widths of that chosen chart. -/
theorem JointSchedule.eventually_frozen_signed_post_windows (φ : K →+* F) (q : ℕ)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k headerFactor U degree lg : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ l, n=l+1 →
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let W := b.physical.word n
      let link := b.physical.link n
      let lit := literal s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let entries := (epochCopies S)^T*V
      let reserve := SeedPlan.profileReserve r n
      let symbols := alphabet s.α n
      let X := (R+1)*exterior ((s.τ:ℝ)/5) r n
      let cap := declarationCap cube.pred symbols (blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1)))
        cube.b cube.h cube.width
      let lim := f (adviceScale b.σ b.ρ n)
      Nonempty (SeedPlan S n r (start-1) T (width n s.α) headerFactor Q) →
      ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (R+1) r W W W (lim+6)), reader.charge≤c*(lim+1)^k →
        let par := pairedTableParameters (l+1) size
        let scalars := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
        let len := PositiveFields.width reserve cube.pred symbols cap (R+1) (par+scalars) W
        let initial : StartupArena := ⟨R+1,r,lit,link,len,reader.packetBitCount⟩
        let query := Fintype.card (Board.Physical par (lim+6) W (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
        let guesses := Fintype.card (Guess (Fin par) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
        ∀ (desc field live p d depth chunks : ℕ),
          let ceiling := geometryGateCeiling U degree r n
          let dir := freeDirectory R r lit link V (blockWidth (r*n) V) entries desc
          let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
          let cables := (boundary S start T).edges+4*((R+1)*V)
          let ordinary := signedGridOutputCount cables cells entries live 37 (Total p d)
          let outputs := ordinary+(2^depth+2^depth)
          let dest := Allocation.dest (initial.next+7*dir.candidates) reserve ceiling outputs field
          let ctl := controlsBase dest cables cells entries live
          let startWords := Retained.packetBase dest cables cells entries live 37
          let dirs := GeometryDirectories.published startWords p d (cells+1) chunks ctl (Total p d) depth
          let task := b.frozenSignedTask cube n l size headerFactor initial dir reserve ceiling outputs field dirs
          ∀ {Input History Port : Type} [Fintype Input] [Fintype History] [Fintype Port] {active : ℕ}
            (hist : Frame (Input ⊕ History) (Port ⊕ Unit)) (order : History ≃ Fin active) (fit : active ≤ reserve)
            (emit : Frame ((Input ⊕ Fin reserve) ⊕ Port) (Fin outputs × Fin field)) (x : Input → Bool),
            1 ≤ field → NativeGeometryReceipt U degree n r W (R+1) V entries hist order fit emit x →
            task.FinishAddresses initial ctl reserve cube.pred symbols cap W W query guesses reader.gates ∧
            task.FinishWindows r W p d (Nat.clog 2 (r*(2*l+1)+1)) (exterior ((s.τ:ℝ)/5) r n)
              ⌈RoutingISA.Evaluator.publicWork (cube.pred+1) s.α r n (R+1)⌉₊
              ⌈RoutingISA.Evaluator.localWork (cube.pred+1) lg s.α ((s.τ:ℝ)/5) r n (R+1)⌉₊ reader.charge := by
  filter_upwards [b.eventually_startup_post_rates (aux:=φ ∘ cube.table) (q:=q) cube f hf c k,
    b.eventually_frozen_finish_addresses cube φ q f hf c k headerFactor,eventually_ge_atTop 1] with n rates addresses hn
  intro l index r R W link lit start V T entries reserve symbols X cap lim seed size ord common chart _ _
    reader charged par scalars len initial query guesses desc field live p d depth chunks
    ceiling dir cells cables ordinary outputs dest ctl startWords dirs task Input History Port _ _ _ active
    hist order fit emit x fieldPos receipt
  have room := addresses l index seed chart reader charged desc U degree field live p d depth chunks
    hist order fit emit x fieldPos receipt
  let axes := Fintype.card (Epoch.Cube D)
  have cost := rates l index chart reader charged
    (Allocation.stop (initial.next+7*dir.candidates) reserve ceiling outputs field W) X
    cells cables dir.candidates reserve entries (DeckGrid.seedSiteCapacity n r axes (start-1))
    (headerFactor*logWidth r n)
    (BottomGridBank.bodyBudget (DeckGrid.seedBoxCapacity n r axes (start-1) (Fintype.card (DeckGrid.Direction axes))))
    (cube.cubeID G) dirs
  let bits := Nat.clog 2 (r*(2*l+1)+1)
  have slots : task.cube.teams*(task.p.parameters*bits) ≤ r := cost.1
  have emitted : Total p d ≤ outputs :=
    ((((Nat.le_add_left (Total p d) 37).trans (Nat.le_add_left ..)).trans (Nat.le_add_left ..)).trans
      (Nat.le_add_left ..)).trans (Nat.le_add_right ..)
  have ξle : (s.τ:ℝ)/5≤1 := by linarith [s.tau_small,s.alpha_small]
  have caps := RoutingISA.Evaluator.ScheduleClock.post_window_capacities (a:=cube.pred+1) (D:=lg) (α:=s.α) (ξ:=(s.τ:ℝ)/5)
    hn (stretch_one b.ρ n) (Nat.succ_pos R) ξle room.wordPos fieldPos emitted receipt.2.2.2 slots
  exact ⟨room,slots,cost.2,caps.1,caps.2.1,caps.2.2⟩

end Diagonal

end BorderVNP
end Computability
end OAI
