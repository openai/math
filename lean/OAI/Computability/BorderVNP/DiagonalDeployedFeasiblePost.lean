import OAI.Computability.BorderVNP.DiagonalFrozenSignedPostWindows
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedReportFrame

/-! # Numerical inputs of the native post on the selected frozen signed task -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP BurstRAM TeamContraction.ProcessorSlots DiagonalTallyAllocation

/-- Static inputs common to all issued arguments on one deployed signed tape.
The bounds refer both to the original startup and to the frozen geometry. -/
structure Layout.DeployedFeasiblePost (task : Layout) (A : StartupArena) (dir : Packing.Directory.Layout)
    (ctl reserve axes groups cap w query guesses gates indices r wp wd digits outside publicCost localCost reader teams parameters scalars : ℕ) : Prop where
  addresses : task.FinishAddresses A ctl reserve axes groups cap w w query guesses gates
  windows : task.FinishWindows r w wp wd digits outside publicCost localCost reader
  teamCount : task.cube.teams=teams
  dimension : task.dim=parameters+scalars
  parametersAt : task.p.parameters=parameters
  scalarsAt : task.p.report.gadgets=scalars
  positive : 0<task.cube.h*task.cube.b
  alphabet : 0<task.cube.header.d
  directories : ∀ pp lp, (dir.directory pp lp).length+task.cube.header.d.choose 2 ≤ task.cube.maxRows
  readerCopied : (6+3*gates+query)*w≤A.copied
  readerIndices : indices≤A.count
  frameRoom : A.frame+30<2^w

namespace Layout.DeployedFeasiblePost

variable {task : Layout} {A : StartupArena} {D : Packing.Directory.Layout}
    {ctl reserve axes groups cap w query guesses gates indices r wp wd digits outside publicCost localCost reader teams parameters scalars : ℕ}
    (fit : task.DeployedFeasiblePost A D ctl reserve axes groups cap w query guesses gates indices r wp wd digits
      outside publicCost localCost reader teams parameters scalars)

include fit in
/-- The true scanner uses this task's two scratch banks, the cube sentinel
and one full physical word for each submitted counter. -/
theorem report (frame : ℕ) :
    let L := reportLayout task.before task.after frame ctl task.p.parameters task.p.siteWidth task.p.bodyCap task.cube.stop
    L.zeroAddr=task.cube.stop ∧ L.countWidth=w ∧ L.parameters=task.p.parameters ∧ L.gadgets=task.p.report.gadgets :=
  ⟨rfl,fit.addresses.reportWidth,rfl,rfl⟩

include fit in
/-- Reading ordinary operand zero of the deployed packet bank yields the
untruncated frame address of the retained startup. -/
theorem headOfOperands {bits off : ℕ} (u : Fin A.teams) (packet : ReferencePacket w bits)
    (ordinary bank : Arg → Word w) (issued : bank=(A.operands u off packet).bank ordinary) :
    (bank 0).val=A.frame := by
  rw [issued]
  change A.frame % (2^w)=A.frame
  exact Nat.mod_eq_of_lt ((Nat.le_add_right A.frame 30).trans_lt fit.frameRoom)

end Layout.DeployedFeasiblePost
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

/-- One physical chart and geometry receipt supply all scalar, directory and
startup bounds needed by the issued post, uniformly over the later returned
preparations, routing selectors and report words. -/
theorem JointSchedule.eventually_deployed_feasible_post (φ : K →+* F) (q : ℕ)
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
            task.DeployedFeasiblePost initial dir ctl reserve cube.pred symbols cap W query guesses reader.gates
              ((par+2)*(lim+6)) r p d (Nat.clog 2 (r*(2*l+1)+1)) (exterior ((s.τ:ℝ)/5) r n)
              ⌈RoutingISA.Evaluator.publicWork (cube.pred+1) s.α r n (R+1)⌉₊
              ⌈RoutingISA.Evaluator.localWork (cube.pred+1) lg s.α ((s.τ:ℝ)/5) r n (R+1)⌉₊
              reader.charge (R+1) par scalars := by
  filter_upwards [b.eventually_frozen_signed_post_windows cube φ q f hf c k headerFactor U degree lg,
    b.physical.eventually_nativePackets (G:=G) (aux:=φ ∘ cube.table) (q:=q) f hf c k 1,
    eventually_ge_atTop 1] with n selected packets hn
  intro l index r R W link lit start V T entries reserve symbols X cap lim seed size ord common chart _ _
    reader charged par scalars len initial query guesses desc field live p d depth chunks ceiling dir
    cells cables ordinary outputs dest ctl startWords dirs task Input History Port _ _ _ active
    hist order fit emit x fieldPos receipt
  obtain ⟨addr,windows⟩ := selected l index seed chart reader charged desc field live p d depth chunks
    hist order fit emit x fieldPos receipt
  have counted : reader.packetBitCount=W*(6+3*reader.gates+query+81)+(par+2)*(lim+6) := rfl
  let sample := reader.nativePacket 0 0 0 0 0 (fun _ => 0)
  have budget := packets chart reader charged 0 0 0 0 0 (fun _ => 0)
  change 1*(sample.bits.length+_+_+1+_) < r at budget
  let dummy : ReaderPlacement W := ⟨0,0,0,0,0,0,0,0,fun _ => 0⟩
  have bitCount : sample.bits.length=reader.packetBitCount := reader.packetAt_length dummy
  have copied : reader.packetBitCount≤r := by omega
  have litPos : 1 ≤ lit := Nat.le_floor (by
    simpa using Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ))
      (show 0 ≤ 1-(s.α:ℝ)/3 by linarith [s.alpha_small]))
  have readPins : (par+2)*(lim+6) ≤ initial.count := by
    change _ ≤ r*lit
    exact ((Nat.le_add_left _ _).trans (counted ▸ copied)).trans (Nat.le_mul_of_pos_right _ litPos)
  have readEntries : (6+3*reader.gates+query)*W ≤ initial.copied := by
    change _ ≤ reader.packetBitCount
    rw [counted,Nat.mul_comm (6+3*reader.gates+query)]
    exact (Nat.mul_le_mul_left W (Nat.le_add_right _ 81)).trans (Nat.le_add_right _ _)
  have groupPos : 0 < alphabet s.α n := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn : 0<(n:ℝ)) _)
  refine ⟨addr,windows,rfl,rfl,rfl,rfl,cube.block_pos,groupPos,?_,readEntries,readPins,?_⟩
  · intro pp lp
    change (dir.directory pp lp).length+symbols.choose 2 ≤ dir.candidates+symbols.choose 2
    exact Nat.add_le_add_right (dir.directory_length_le pp lp) _
  · exact (task.reader_room initial addr.position readPins readEntries addr.endFit).1

end Diagonal

end BorderVNP
end Computability
end OAI
