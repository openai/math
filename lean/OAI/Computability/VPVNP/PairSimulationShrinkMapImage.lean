import OAI.Computability.VPVNP.PairSimulationMapHandlerImage
import OAI.Computability.VPVNP.PairSimulationMapResidentInputs
import OAI.Computability.VPVNP.PairSimulationResidentDispatchImage
import OAI.Computability.VPVNP.PairSimulationResidentMapLoop
import Mathlib.Data.List.NodupEquivFin

/-!
# The shrinking node's resident map loop in one finite instruction bank

The count reader and each item reader feed the actual grid and party chains.
Their targets are the lowered, descriptor-writing map handlers. Successful
entries return to the common row increment; exhausting the row reaches the
role continuation. All emitted instructions use the live five-bit literal format.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage

open BurstRAM BurstRAM.PrivateRAM Compression.ShrinkMotif MotifSelector MotifGrid
open MotifBlocks MotifConversion MapHandlerImage
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w : ℕ} (F : MapHandlerImage.Family B t shared)

/-- Exactly the order of the grid numbers written by the selected-term worker. -/
noncomputable def demandOrder (s : Finset K) : Fin s.toList.length ≃ s := by
  classical
  exact (List.Nodup.getEquiv s.toList s.nodup_toList).trans
    (Equiv.subtypeEquivRight (fun _ ↦ Finset.mem_toList))

/-- Instruction labels for the resident readers, loop, dispatcher, map handlers, and reject row. -/
noncomputable abbrev Address := MapResidentInputs.Address ⊕ Bool ⊕
  ResidentDispatchImage.Address B.grid.demands (Fin 6) ⊕ F.Address ⊕ Unit

/-- The eleven header registers have their resident reader roles. The extra
zero register serves the ordinal dispatcher and lies outside that reader bank. -/
structure Registers (shared : ℕ) where
  /-- Placement of the eleven reader registers in the shared bank. -/
  header : Fin 11 ↪ Fin shared
  /-- Shared register used for zero by the grid and party dispatcher. -/
  zero : Fin shared
  apart : ∀ i, zero ≠ header i

namespace Registers

variable (S : Registers shared) (loc : Address F → Fin p) (dfs : Fin 9 ↪ Fin r)
  (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r) (own : F.PrivateReg ↪ Fin r)
  (done : Fin p)

/-- Machine address of an instruction in the resident header or item reader. -/
def inputPC (a : MapResidentInputs.Address) := loc (.inl a)

/-- Machine address of a grid or party dispatch instruction. -/
def casePC (a : ResidentDispatchImage.Address B.grid.demands (Fin 6)) := loc (.inr (.inr (.inl a)))

/-- Machine address of a descriptor writer or map instruction in the handler family. -/
noncomputable def handlerPC (a : F.Address) := loc (.inr (.inr (.inr (.inl a))))

/-- Machine address of the cursor test (`false`) or increment (`true`). -/
def loopPC (b : Bool) := loc (.inr (.inl b))

/-- Reject address for a grid or party ordinal outside the dispatch table. -/
def badPC := loc (.inr (.inr (.inr (.inr ()))))

/-- Physical register assignment for the eleven resident reader registers. -/
def headerReg : Fin 11 ↪ Fin r := S.header.trans common

/-- Dispatches the grid and party ordinals read from an item to its descriptor writer. -/
noncomputable def cases : ResidentDispatchImage.Image B.grid.demands (Fin 6)
    B.grid.demands.toList.length 6 p r where
  grids := demandOrder B.grid.demands
  parties := Equiv.refl _
  place := casePC F loc
  target z j := F.target (handlerPC F loc) (z, j)
  bad := badPC F loc
  grid := (S.headerReg common) 9
  party := (S.headerReg common) 7
  zero := common S.zero
  one := (S.headerReg common) 10

/-- Tests the reader's cursor against the end of the row and advances it after each handler. -/
noncomputable def loop : ResidentMapLoop.Program p r where
  test := loopPC F loc false
  advance := loopPC F loc true
  item := inputPC F loc (.inr 0)
  done := done
  cursor := (S.headerReg common) 2
  stop := (S.headerReg common) 3
  one := (S.headerReg common) 10
  stopApart := (S.headerReg common).injective.ne (by decide)
  oneApart := (S.headerReg common).injective.ne (by decide)

theorem distinct : (cases F S loc common).Distinct := by
  constructor
  · exact common.injective.ne (S.apart 9)
  · exact common.injective.ne (S.apart 7)
  · exact (S.headerReg common).injective.ne (by decide)
  · exact (S.headerReg common).injective.ne (by decide)
  · exact common.injective.ne (S.apart 10).symm
  · exact (S.headerReg common).injective.ne (by decide)

/-- Five-bit instructions for one resident map row scan, including all dispatch targets. -/
noncomputable def text : Address F → Instr 5 p r 11
  | .inl a => MapResidentInputs.text (inputPC F loc) (S.headerReg common)
      (loopPC F loc false) (casePC F loc (.inl ())) a
  | .inr (.inl b) => (loop F S loc common done).control b
  | .inr (.inr (.inl a)) => (cases F S loc common).text a
  | .inr (.inr (.inr (.inl a))) =>
    F.text (handlerPC F loc) dfs saved common own (loopPC F loc true) a
  | .inr (.inr (.inr (.inr _))) => .reject

/-- Placing the one fixed table supplies the four program links and the
complete handler family rows, with no condition on the external memory. -/
theorem linked (M : Machine w p r 11)
    (rows : ∀ a, M.code (loc a) = (text F S loc dfs saved common own done a).resize w) :
    MapResidentInputs.HeaderLinked M (inputPC F loc ∘ Sum.inl) (S.headerReg common)
      (loopPC F loc false) ∧
    MapResidentInputs.ItemLinked M (inputPC F loc ∘ Sum.inr) (S.headerReg common)
      (casePC F loc (.inl ())) ∧
    (loop F S loc common done).Linked M ∧ (cases F S loc common).Linked M ∧
    (∀ a, M.code (handlerPC F loc a) =
      (F.text (handlerPC F loc) dfs saved common own (loopPC F loc true) a).resize w) ∧
    M.code (badPC F loc) = .reject := by
  obtain ⟨header, item⟩ := MapResidentInputs.linked M (inputPC F loc) (S.headerReg common)
    (loopPC F loc false) (casePC F loc (.inl ())) (fun a ↦ rows (.inl a))
  exact ⟨header, item, ⟨rows (.inr (.inl false)), rows (.inr (.inl true))⟩,
    fun a ↦ rows (.inr (.inr (.inl a))), fun a ↦ rows (.inr (.inr (.inr (.inl a)))),
    rows (.inr (.inr (.inr (.inr ()))))⟩

/-- Numbering of the complete resident-map portion, independent of the input length. -/
noncomputable def locations : Address F ≃ Fin (Nat.card (Address F)) := by
  classical
  letI := Fintype.ofFinite (Address F)
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- Embeds the role's shared registers into the segment's numbered register bank. -/
noncomputable def sharedRegs : Fin shared ↪ Fin (Nat.card (Fin shared ⊕ F.PrivateReg)) :=
  Function.Embedding.inl.trans F.registers.toEmbedding

/-- Embeds the handlers' private registers into the segment's numbered register bank. -/
noncomputable def mapRegs : F.PrivateReg ↪ Fin (Nat.card (Fin shared ⊕ F.PrivateReg)) :=
  Function.Embedding.inr.trans F.registers.toEmbedding

/-- A segment compatible with the final-vertex image. The caller's level
and packed-site inputs are its header registers zero and one. -/
noncomputable def segment : VertexImage.Segment where
  count := Nat.card (Address F)
  privateRegs := Nat.card (Fin shared ⊕ F.PrivateReg)
  entry := inputPC F (locations F) (.inl 0)
  row place dfs saved locals ret i := text F S (place ∘ locations F) dfs saved
    ((sharedRegs F).trans locals) ((mapRegs F).trans locals) ret ((locations F).symm i)

/-- Recover the typed opcode rows inside any installation of this whole segment. -/
theorem segment_rows (place : Fin (Nat.card (Address F)) → Fin p)
    (locals : Fin (Nat.card (Fin shared ⊕ F.PrivateReg)) ↪ Fin r) (M : Machine w p r 11)
    (h : ∀ a, M.code (place a) = ((segment F S).row place dfs saved locals done a).resize w)
    (a : Address F) : M.code ((place ∘ locations F) a) =
      (text F S (place ∘ locations F) dfs saved ((sharedRegs F).trans locals)
        ((mapRegs F).trans locals) done a).resize w := by
  simpa [segment] using h (locations F a)

end Registers
end PairSimulation.ShrinkMapImage

end VPVNP
end Computability
end OAI
