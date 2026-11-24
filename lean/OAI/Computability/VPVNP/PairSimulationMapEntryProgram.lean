import OAI.Computability.VPVNP.PairSimulationMapBank
import OAI.Computability.VPVNP.PairSimulationMapSelectors
import OAI.Computability.VPVNP.PairSimulationMapFinish

/-!
# The linked instruction blocks of one grouped map entry

The program uses one selector directory and fixed matrix bank at a chosen grid
point and party. The width guards and histogram scan share the same machine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapEntry

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM MotifSelector MotifBlocks MotifGrid MotifConversion
open MapPortAgreement
open scoped Fin.CommRing

variable {K J D E : Type} [Field K] [Fintype J] [Fintype D] [Fintype E]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (j : J) {w p r k : ℕ}

/-- Locations of the fixed instructions and registers used by the four phases. -/
structure Program (p r k : ℕ) where
  /-- The selector directory scan and decoder for the block. -/
  selector : MapSelectors.Program (Selector B) p r k
  /-- Registers and public ports for the matrix rows at grid point `z` and party `j`. -/
  bank : MapBank.Allocation B z j r k
  /-- Machine instruction address assigned to each bank address. -/
  loc : bank.Address → Fin p
  /-- Order in which the width guard checks the supply edges. -/
  edgeOrder : Fin (Fintype.card E) ≃ E
  /-- Register holding the expected total width for each edge. -/
  expected : E → Fin r
  /-- Register compared with itself at the end of the width guard. -/
  guardTemp : Fin r
  /-- Machine instruction addresses of the width comparisons. -/
  guardPC : (MapWidths.checkCode (fun e ↦ bank.rowReg (.offset (.inr e))) expected guardTemp
    (List.ofFn edgeOrder) : Flow r k).Label → Fin p
  /-- Instruction addresses of the histogram scan. -/
  histPC : Fin 7 → Fin p
  /-- Machine registers used by the histogram scan. -/
  histReg : Fin 6 ↪ Fin r
  /-- Continuation after the histogram scan finishes. -/
  done : Fin p
  /-- Rejection address shared by the selector, row driver and width guard. -/
  bad : Fin p

namespace Program

variable {B z j} (P : Program B z j p r k)

/-- The matrix row driver at the instruction addresses assigned by `P.loc`. -/
noncomputable abbrev driver := P.bank.driver P.loc

/-- Compare each accumulated edge offset with its expected width in `P.edgeOrder`. -/
noncomputable abbrev guardCode : Flow r k := MapWidths.checkCode
  (fun e ↦ P.bank.rowReg (.offset (.inr e))) P.expected P.guardTemp (List.ofFn P.edgeOrder)

/-- Instruction links for the common machine, including the shared rejection target. -/
structure Linked (M : Machine w p r k) : Prop where
  selector : P.selector.Linked M
  table : P.selector.decoder.xs = selectorTable B
  selectorExit : P.selector.decoder.done = P.driver.pc 0
  selectorBad : P.selector.decoder.bad = P.bad
  rowExit : P.driver.checkWidths = P.guardPC P.guardCode.entry
  rowBad : P.driver.bad = P.bad
  body : ∀ a, P.bank.inBody a = true → M.code (P.loc a) = (P.bank.text P.loc a).resize w
  guard : Flow.Linked M P.guardCode P.guardPC (P.histPC 0) P.bad
  histogram : PrivateLabels.Linked M P.histPC P.histReg P.done

/-- An exterior register survives the selector directory walk and decoder. -/
def SelectorSaved (a : Fin r) : Prop := MapPortScan.Preserved P.selector.reg a ∧
  ∀ i, a ≠ P.selector.decoder.reg i

/-- The row bank, width targets and histogram operands can all be prepared
before entering the selector walk. Only the row bank uses the row scratch words. -/
structure Separate : Prop where
  bank : ∀ a, P.SelectorSaved (P.bank.register a)
  expected : ∀ e, P.SelectorSaved (P.expected e)
  histogram : ∀ i, P.SelectorSaved (P.histReg i)
  expectedRow : ∀ e a, P.expected e ≠ P.bank.register a
  histRow : ∀ i a, P.histReg i ≠ P.bank.register a

/-- The fixed code bits and matrix keys use the live word size. The two
selector phases share the same ordinal for each selector. -/
structure Public (M : Machine w p r k) (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) (fb : B.selectorBits ≤ w)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w) : Prop where
  key : ∀ s, M.publicData (P.selector.decoder.key s) = MapLookup.widen fb (selectorCode B s)
  name : ∀ s, M.publicData (P.selector.decoder.name s) = M.publicData (P.bank.selectorPort s)
  rows : ∀ a, M.publicData (P.bank.port a) = MapBank.Allocation.words fd fs selector ordinal a

end Program
end PairSimulation.MapEntry

end VPVNP
end Computability
end OAI
