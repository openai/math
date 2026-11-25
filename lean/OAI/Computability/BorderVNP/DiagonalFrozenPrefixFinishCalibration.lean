import OAI.Computability.BorderVNP.DiagonalPrefixFinishCalibration
import OAI.Computability.BorderVNP.DiagonalNativeGeometryWindow

/-! # The selected signed finish fits the original reader and real geometry directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open DiagonalTallyAllocation BorderVNP.Cube

/-- Length-only data for the positive finish, common to all teams, histories
and private outcomes. The two directory bounds reach the packet base because
the installed problem may read that bank after the sparse instruction. -/
structure Layout.FinishAddresses (task : Layout) (initial : StartupArena)
    (ctl reserve axes groups cap width w query guesses gates : ℕ) : Prop where
  endFit : task.endAddress w query guesses gates < 2^w
  position : initial.next ≤ task.cube.header.header
  headerSize : initial.header = PositiveFields.width reserve axes groups cap task.cube.teams task.dim width
  widthFit : width ≤ w
  wordPos : 0<w
  reportDim : task.dim<2^w
  teamsFit : task.cube.teams<2^w
  place : task.SparsePlacement initial.frame ctl
  sortedHi : task.p.sorted+task.p.padded ≤ task.cube.header.packetBase
  ctlHi : ctl+37 ≤ task.cube.header.packetBase
  reportWidth : task.p.report.countWidth = w
  digitsFit : Tally.argumentWidth task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s = task.p.report.cubeWidth
  vertices : task.cube.vertexCap = task.p.report.vertices
  idFit : ∀ e, task.id e < task.p.report.gadgets
  controlAbove : initial.next ≤ ctl
  geometryAbove : initial.next ≤ task.p.sorted

end RoutingISA.SignedTaskArena

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

/-- One length threshold certifies the true signed call and finish addresses
of every admitted reader on the frozen installation. The public header and
the gate ceiling are fixed before an individual report return is chosen. -/
theorem JointSchedule.eventually_frozen_finish_addresses (φ : K →+* F) (q : ℕ)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k headerFactor : ℕ) :
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
        ∀ (desc U degree field live p d depth chunks : ℕ),
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
            task.FinishAddresses initial ctl reserve cube.pred symbols cap W W query guesses reader.gates := by
  obtain ⟨_,_,calibrated⟩ := b.eventually_frozen_signed_task cube φ q f hf c k headerFactor
  filter_upwards [calibrated] with n selected
  intro l index r R W link lit start V T entries reserve symbols X cap lim seed size ord common chart _ _
    reader charged par scalars len initial query guesses desc U degree field live p d depth chunks
    ceiling dir cells cables ordinary outputs dest ctl startWords dirs task Input History Port _ _ _ active
    hist order fit emit x fieldPos receipt
  have outputRoom : GeometryAdviceRate.packetWords ceiling reserve outputs field*W ≤ r*width n (95/100:ℝ) :=
    (Nat.le_add_left ..).trans receipt.2.2.2
  have measured := selected l index seed chart reader charged desc ceiling outputs field dirs fieldPos outputRoom
  have endFit : task.endAddress W query guesses reader.gates < 2^W := measured.2.1
  have bounds := task.finish_word_room endFit
  obtain ⟨place,sortBound,ctlBound⟩ := Retained.signed_finish_directories task initial dir.candidates
    reserve ceiling entries live p d depth field W chunks rfl rfl rfl le_rfl
  have fromFresh : initial.next+7*dir.candidates ≤ dest := by dsimp only [dest,Allocation.dest,Allocation.temp]; omega
  have controlAbove : initial.next ≤ ctl := ((Nat.le_add_right ..).trans fromFresh).trans
    (by dsimp only [ctl,controlsBase,bases]; omega)
  have geometryAbove : ctl ≤ task.p.sorted := by
    change ctl ≤ (ctl+37)+(2^p+2^p)
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨endFit,measured.2.2.1,rfl,le_rfl,bounds.1,bounds.2.1,bounds.2.2.1,
    place,sortBound,ctlBound,rfl,rfl,rfl,
    fun e => (Fintype.equivFin (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width) (.inr e)).isLt,
    controlAbove,controlAbove.trans geometryAbove⟩

end Diagonal

end BorderVNP
end Computability
end OAI
