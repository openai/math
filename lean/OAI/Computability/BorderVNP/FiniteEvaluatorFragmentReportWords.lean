import OAI.Computability.BorderVNP.FiniteEvaluatorRetainedClockGeometry
import OAI.Computability.BorderVNP.FragmentDirectoryInputPublication

/-! # Original words at a finite scalar reporter return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open FiniteEvaluator Packing BorderVNP.Cube VPVNP.BurstRAM RoutingISA.Evaluator ScheduleClock
open private host_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits

/-- The immutable part of the primary frame and the actual cell bank pointers
at a scalar report exit. A signed report may additionally write the descriptor count at frame word 35. -/
structure ReportWords (a : Layout) (frame : ℕ) (initial written result : ℕ → ℕ) (signed : Bool := false) : Prop where
  primary : frame+112 ≤ a.cube.header.header
  lower : ∀ x < a.cube.header.header, x≠frame+13 → x≠frame+46 → x≠frame+90 → (signed = true → x≠frame+35) → result x=initial x
  banks : ∀ c<a.cube.cells, result (a.cube.hostDirectory+c*2+1)=written (a.cube.hostDirectory+c*2+1)

variable (a : Layout) {team frame offsets control live ports bundles b : ℕ}
    (owner : Fin bundles → Fin a.cube.cells) (hdr : Fin bundles → BottomReports.BundleHeader)
local notation "H" => a.openInputs team frame offsets control live ports bundles b owner hdr

/-- A chronological report can only touch its assigned banks and report
directories. Below those banks the opened control count is the one extra
primary word changed by the four opening passes. -/
theorem Layout.report_words {w : ℕ} {s : Bank w} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {entry : Memory w} {initial written : ℕ → ℕ} (base : (pub 0).val=frame)
    (keep : CubeAllocation.HostRetention a.cube frame initial written (readings entry))
    (valid : OpenSuffix.Ready (H) frame (readings entry) w)
    (place : OpenSuffix.Placement (H) a.cube a.before frame (readings entry))
    (opened : Returns OpenSuffix.code pub mac s entry) {banks : CellBanks.Layout} {scalars digits : ℕ} {source : ℕ → ℕ}
    (dir : Reports.Directory pub opened.val.2.2 a.before banks (a.controlRows team frame offsets control live ports)
      source scalars digits) (bankAt : banks.bankStart=a.cube.cellBank)
    (reported : Returns prepareReports pub mac opened.val.2.1 opened.val.2.2) :
    ReportWords a frame initial written (readings reported.val.2.2) := by
  have atFrame : OpenSuffix.Ready (H) (pub 0).val (readings entry) w := by simpa only [base] using valid
  have img := ((OpenSuffix.run (H) atFrame).sound opened.property).2
  rw [base] at img
  have opening (x : ℕ) (low : x<a.cube.cellBank) (ne : x≠frame+90) :
      readings reported.val.2.2 x=readings entry x :=
    (dir.low reported _ (bankAt.symm ▸ low)).trans ((congrFun img x).trans (a.open_image_low owner hdr place x low ne))
  obtain ⟨headBelow,_,_,hostBelow,_,_⟩ := host_order a.cube
  refine ⟨keep.primary,fun x hx n13 n46 n90 _ => (opening x (hx.trans_le headBelow) n90).trans
    (keep.lower x hx n13 n46),?_⟩
  intro c hc
  obtain ⟨first,pubEnd,link,ownerEnd,pairEnd,hostEnd,_,_⟩ := a.cube.writer_order
  have before := keep.primary
  have inTable : a.cube.publicBase ≤ a.cube.hostDirectory+c*2+1 ∧
      a.cube.hostDirectory+c*2+1 < a.cube.records := by omega
  exact (opening _ (by omega) (by omega)).trans (keep.tables _ inTable.1 inTable.2)

variable {a : Layout} {initial written result : ℕ → ℕ} {signed : Bool} (h : ReportWords a frame initial written result signed)

include h

/-- Original primary words outside the three updated counters. -/
theorem ReportWords.frame_word (j : ℕ) (old : j<112) (a13 : j≠13) (a46 : j≠46) (a90 : j≠90)
    (a35 : signed = true → j≠35 := by simp) :
    result (frame+j)=initial (frame+j) := by
  have low := h.primary
  exact h.lower _ (by omega) (by omega) (by omega) (by omega) (by intro hs; have := a35 hs; omega)

/-- The whole geometry buffer survives the report below the secondary arena. -/
theorem ReportWords.geometry (x : ℕ) (lo : frame+112 ≤ x) (hi : x<a.cube.header.header) : result x=initial x :=
  h.lower x hi (by omega) (by omega) (by omega) (by intro; omega)

/-- All native label chooser frame words remain available at the later report. -/
theorem ReportWords.labelLayout : LabelIndex.layout frame result = LabelIndex.layout frame initial := by
  dsimp only [LabelIndex.layout]
  congr 1 <;> exact h.frame_word _ (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)

/-- Endpoints decoded by the reported fragment generator are exactly the
earlier populated endpoints, including all zero-width cable slots. -/
theorem ReportWords.endpoints (e : LabelIndex.Endpoints (LabelIndex.layout frame initial) initial)
    {origin cableCount raw count : ℕ} (cables : initial (frame+6)=origin) (edges : initial (frame+7)=cableCount)
    (delivery : initial (frame+8)=raw) (entries : initial (frame+9)=count)
    (cableLow : frame+112 ≤ origin) (cableHigh : origin+3*cableCount ≤ a.cube.header.header)
    (rawLow : frame+112 ≤ raw) (rawHigh : raw+7*count ≤ a.cube.header.header) :
    LabelIndex.Endpoints (LabelIndex.layout frame result) result := by
  rw [h.labelLayout]
  constructor
  · intro i hi
    have src := (e.cables i hi).1
    have dst := (e.cables i hi).2
    change i < initial (frame+7) at hi
    rw [edges] at hi
    dsimp only [LabelIndex.cableAt,LabelIndex.layout] at src dst ⊢
    rw [cables] at src dst ⊢
    rw [h.geometry (origin+i*3) (by omega) (by omega),h.geometry (origin+i*3+1) (by omega) (by omega)]
    exact ⟨src,dst⟩
  · intro i hi
    have row := e.deliveries i hi
    change i < initial (frame+9) at hi
    rw [entries] at hi
    dsimp only [LabelIndex.deliveryAt,LabelIndex.layout] at row ⊢
    rw [delivery] at row ⊢
    rw [h.geometry (raw+i*7+4) (by omega) (by omega)]
    exact row

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
