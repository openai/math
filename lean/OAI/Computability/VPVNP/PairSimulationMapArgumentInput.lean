import OAI.Computability.VPVNP.PairSimulationMapArgumentWriter
import OAI.Computability.VPVNP.PairSimulationMapCallSetup

/-!
# Reading a published private descriptor as the input of a grouped map

The map's raw incident fields already occupy private memory before its argument
writer executes. For each live bit, the physical layout separates the bit from
both the call descriptor and the selector directory. Thus the stores establish
the descriptor readback while preserving all demand and supply bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapArgumentWriter

open MotifSelector MotifBlocks MotifGrid MotifConversion MotifEntry
open BurstRAM BurstRAM.PrivateRAM MapPortAgreement MapResidentAgreement
open CompressorRecords CompressorRecords.PhaseRecipe
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k p w t u : ℕ}
  (A : MapEntryTable.Allocation B z j r k) (args : MapCallSetup.Arg D E ≃ Fin
    (Fintype.card (MapCallSetup.Arg D E))) (loc : A.Address → Fin p)
  {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
  {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
  (X : MapEntry.Program.Workspace (A.program loc) demand v d x t w)

/-- Each live cell lies outside both the private argument range and the future
selector directory. The pointer directory can wrap around the word modulus. -/
def separated (addr cell : BurstRAM.Word w) : Prop :=
  (cell.val < addr.val ∨ addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ cell.val) ∧
    ∀ i : MapDirectoryInit.Row A, cell ≠ X.directory + (i.val : BurstRAM.Word w)

/-- Physical readback and layout of the old half-wire buffers before publishing
the map's private call descriptor. -/
structure ResidentFields (addr : BurstRAM.Word w)
    (mem : BurstRAM.Word w → BurstRAM.Word w) : Prop where
  payloadFit : ∀ e, v e < 2 ^ w
  supplyBase : ∀ t : Port G j,
    X.portBase t = (X.base (MapDirectoryInit.portField t) : BurstRAM.Word w)
  supply : ∀ (t : Port G j) (i : Fin (v (edge t) + u * B.selectorBits)),
    let cell := X.portBase t + (i.val : BurstRAM.Word w)
    mem cell = PrimedInputRAM.encodeBit w (field x t i) ∧ separated A loc X addr cell
  demandCells : ∀ (q : Bool × D) (i : Fin (MapRow.endpoint src dst j demand d q).1),
    let cell := ((X.base (.inl q) + i.val : ℕ) : BurstRAM.Word w)
    mem cell = PrimedInputRAM.encodeBit w ((MapRow.endpoint src dst j demand d q).2 i) ∧
      separated A loc X addr cell

/-- Descriptor stores may be performed by an enclosing machine. The map only
reads its pointer and the shared private memory of the resulting configuration. -/
theorem input_of_published (addr : BurstRAM.Word w) (old : BurstRAM.Word w → BurstRAM.Word w)
    (c : Config w p r) (ptr : Fin r) (hp : c.reg ptr = addr)
    (stored : ∀ a, c.privateMem (addr + ((args a).val : BurstRAM.Word w)) =
      MapCallSetup.values A loc X a)
    (frame : ∀ q : BurstRAM.Word w, q.val < addr.val ∨
      addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ q.val → c.privateMem q = old q)
    (cells : ResidentFields A loc X addr old) : MapCallSetup.Input A args loc X ptr c := by
  refine ⟨fun a ↦ hp ▸ stored a, cells.payloadFit, cells.supplyBase, ?_, ?_,
    fun t i ↦ (cells.supply t i).2.2, fun q i ↦ (cells.demandCells q i).2.2⟩
  · intro t i
    exact (frame _ (cells.supply t i).2.1).trans (cells.supply t i).1
  · intro q i
    exact (frame _ (cells.demandCells q i).2.1).trans (cells.demandCells q i).1

variable (base : Expr) (fields : MapCallSetup.Arg D E → Expr)

local notation "f" => fields ∘ args.symm

/-- A compiled writer whose expressions read the recorded term's argument
values delivers the typed input to the map's register and directory initializer. -/
theorem native_input (vm : Fin (RegisterSetup.regCount (recipes base f)) ↪ Fin r)
    (inputs : Fin 6 → Fin r) (aux : Fin 3 ↪ Fin r) (place : Address base f → Fin p)
    (done : Fin p) (M : Machine w p r k) (link : ∀ a,
      M.code (place a) = (text base f vm inputs aux place done a).resize w)
    (safe : ∀ i q, vm i ≠ inputs q) (apart : ∀ i q, vm i ≠ aux q)
    (c : Config w p r) (m : Memory w) (start : c.pc = setupPC base f place 0) :
    let pub := fun i : Fin 5 ↦ c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := base.eval pub state m
    addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ 2 ^ w →
    (∀ a, (fields a).eval pub state m = MapCallSetup.values A loc X a) →
    ResidentFields A loc X addr c.privateMem →
    ∃ (ev : List (Event w)) (out : Config w p r),
      ev.length = clock base f ∧ countProbes ev = ∑ i, ((recipes base f) i).loads ∧
      choiceBits ev = [] ∧ out.pc = done ∧ out.reg (aux 0) = addr ∧
      MapCallSetup.Input A args loc X (aux 0) out ∧ out.persistent = c.persistent ∧
      (∀ q : BurstRAM.Word w, q.val < addr.val ∨
        addr.val + Fintype.card (MapCallSetup.Arg D E) ≤ q.val →
        out.privateMem q = c.privateMem q) ∧
      (∀ q, (∀ i, q ≠ vm i) → (∀ i, q ≠ aux i) → out.reg q = c.reg q) ∧
      ∀ fuel bs, execute M.program (fuel + ev.length) c m bs =
        (execute M.program fuel out m bs).map (fun rep ↦ ⟨ev ++ rep.events, rep.result⟩) := by
  intro pub state addr fit read cells
  obtain ⟨ev, out, len, probes, choices, stop, ptr, per, words, frame, regs, run⟩ :=
    native base f vm inputs aux place done M link safe apart c m start fit
  refine ⟨ev, out, len, probes, choices, stop, ptr, ?_, per, frame, regs, run⟩
  apply input_of_published A args loc X addr c.privateMem out (aux 0) ptr _ frame cells
  intro a
  rw [words]
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using read a

end PairSimulation.MapArgumentWriter

end VPVNP
end Computability
end OAI
