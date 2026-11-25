import OAI.Hierarchy.TraceFactorReceiver
import OAI.Hierarchy.TraceReceiverGather

namespace OAI
/-! # The common field machine and its product on the selected chronological sites -/

noncomputable section
namespace Hierarchy.TraceReceiverProgram

open ThreeFlat Diagonal RAM
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure TraceFactorReceiver
open TickWeightedBank BitLayout Contraction HistoryContraction
open scoped Classical BigOperators

/-- The common executable. The source procedure is fixed as a function of
the architecture and physical block. At execution it reads the tick ordinal,
selector, and assigned pins from the input tape. -/
def machine {F : Type*} [Field F] [Fintype F] {W p H J : ℕ}
    (fit : Fits (shape F p H J) W) (src : Procedure W)
    (cursor control header «meta» lut : ℕ) :=
  fromTape fit (src.seq (Gather.procedure W cursor)) control header «meta» lut

/-- The gather loop, input shuffle, and finite-field evaluator add constant text and
public operands to the sparse root producer, independently of w and the selected list. -/
theorem machine_dimensions {F : Type*} [Field F] [Fintype F] {W p H J : ℕ}
    (fit : Fits (shape F p H J) W) (src : Procedure W)
    (cursor control header «meta» lut : ℕ) :
    dimensions (machine fit src cursor control header «meta» lut) =
      (37+(src.labels+400)+(overhead F).1,19+(src.registers+129)+(overhead F).2.1,
        6+(src.slots+1)+(overhead F).2.2) := by
  rw [machine,fromTape_dimensions]
  obtain ⟨labels,regs,slots⟩:=Gather.dimensions W cursor
  simp only [Procedure.seq,labels,regs,slots]

/-- Local correctness for a whole selected list from actual source rows,
per-root address translations, and the limited pin frame. The universal
trace runs the padded common machine on the original compact input. -/
theorem local_tick {F : Type*} [Field F] [Fintype F] {W p H J : ℕ}
    (fit : Fits (shape F p H J) W) (src : Procedure W) {S : HistoryContraction.Shape} {Pins α : Type*}
    (P : Plan F S) (h : P.History) {V : Form S Pins} (A : P.Assembly V)
    (seed : Forest F V) (x : Pins) (boundary : (P.finish h).Boundary)
    (items : List α) (site : α → (P.finish h).Site)
    (wires : ∀ i : Fin items.length, Fin ((P.assemble h A seed).1.width (site items[i])) → Fin p)
    (input : ℕ→Bool) (localReads : ∀ i j,input (wires i j).val=(P.assemble h A seed).1.read
      (site items[i]) x ((P.finish h).graph.atVertex boundary (site items[i])) j)
    (cursor control cmdBase header «meta» lut : ℕ) (spans : List Gather.Span) (price : ℕ)
    (wide : 4<2^W) (hm : footprint (shape F p H J) ≤ «meta») (hl : footprint (shape F p H J) ≤ lut)
    (low : cellsBase p H≤«meta») (rows : «meta»+4*J≤lut)
    (tables : lut+8*(TickTerminalPadding.tables F+2)≤header)
    (headerRoom : header+4<2^W) (ctrlRoom : control+3<2^W)
    (apart : control+4≤header ∨ header+4≤control) (shiftRoom : 2+p+p<2^W)
    (hf : Fintype.card F≤2^W) (st : Word W) :
    let pin:=fun i : Fin p=>input i.val
    let nets:=fun i : Fin items.length => ((P.assemble h A seed).2 (site items[i])).compile
    let N:=forest nets wires
    let pad:=H-N.internal
    let fill:=J-(N.cells+pad)
    let code:=machine fit src cursor control header «meta» lut
    N.internal≤H → N.cells+pad≤J →
    src.Spec (·=TickMountedPins.memory (w:=W) pin)
      (fun _ z=>Gather.Prepared nets (ctrl:=cursor) (control:=control) (atCmd:=cmdBase) (H:=H)
        wires pin «meta» spans z) price →
    ∀ {pc regs slots depth fuel : ℕ} (hp : (dimensions code).1≤pc)
      (hr : (dimensions code).2.1≤regs) (hk : (dimensions code).2.2≤ slots),
      let recv:=CapacityPadding.pad code hp hr hk
      ∀ (honest : NativeTrace.Fits recv p 0 depth fuel),
      (∀ i,input i.val=NativeTrace.executable recv i) →
      (28+16*p+(price+Gather.fuel spans)+TickTerminalPadding.budget F pad fill)+evalCost F H J≤fuel →
      (NativeTrace.network recv honest hf st).eval (TraceBitHeader.advicePins 0 (NativeTrace.executable recv) input) =
        (items.map (fun v=>P.cells h (V.values seed x) (site v)
          ((P.finish h).graph.atVertex boundary (site v)))).prod := by
  intro pin nets N pad fill code bits cells written pc regs slots depth fuel hp hr hk recv honest authentic clock
  have fetched : (src.seq (Gather.procedure W cursor)).Spec (·=TickMountedPins.memory pin)
      (fun _ z=>TickTerminalPadding.recorded (H:=H) N pin control «meta» z) (price+Gather.fuel spans) := by
    intro _ _ _ M
    exact Gather.from_streams nets wires pin «meta» spans src _ price wide written M
  have ret:=tick_product fit (src.seq (Gather.procedure W cursor)) nets wires input control header
    «meta» lut bits cells hm hl low rows tables headerRoom ctrlRoom apart shiftRoom _ fetched hf st
    hp hr hk honest authentic clock
  calc
    _ = ∏ i, (nets i).eval (pin ∘ wires i) := ret
    _ = N.eval pin := (forest_eval nets wires pin).symm
    _ = _ := selected_product P h A seed x boundary items site pin wires localReads

end Hierarchy.TraceReceiverProgram
end

end OAI
