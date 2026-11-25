import OAI.Computability.BorderVNP.DiagonalJointSparseReadback
import OAI.Computability.BorderVNP.DiagonalSignedSparseVisit
import OAI.Computability.BorderVNP.DiagonalSignedLaunchedCells

/-! # Sparse packet submission on the exact reached public preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM TeamContraction CompactMachine BorderVNP.Cube ScheduleClock CellMacro.Generator
open CellDispatch CellPacket CellSparse
open scoped Classical

variable {R n w axes b h K s : ℕ} (id : TableEntry axes b h K s → ℕ)
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) {u : Fin (R+1)} (p : (U u).Prefix id)

local notation3 (prettyPrint := false) "mac" => install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "v" => visits id U p
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv (U u).pub mac
  (v).reports.val.2.1 (v).reports.val.2.2).symm (v).arguments

/-- The patched memory and returned typed arguments are those of the
genuine preparation; both the originating logical row and its physical
compressed bits survive relocation along the stated native return. -/
theorem source_of_launched {built : Memory w}
    (address : built=(stages).2.1.val.2.2)
    (arg : SparseCallInput (U u).pub built) (decoded : SparseArgumentCells n arg)
    (input : ℕ → CellInput) (payload : ℕ → List Bool)
    (rows : decoded.rows.cells=input) (bits : decoded.rows.payload=payload) :
    ∃ data : SparseSource id U p, data.logicalAt=input ∧ data.bytesAt=payload := by
  change built=sparseMemory id U p at address
  subst built
  let data : SparseSource id U p := ⟨arg,decoded⟩
  exact ⟨data,rows,bits⟩

/-- The ownership, allocation, and sparse operand facts of the issued
native task survive the same memory identification. The clock can therefore
be checked on the very source used to reconstruct the private cell. -/
theorem source_of_recorded_launch {built : Memory w}
    (address : built=(stages).2.1.val.2.2)
    (arg : SparseCallInput (U u).pub built) (decoded : SparseArgumentCells n arg)
    (input : ℕ → CellInput) (payload : ℕ → List Bool)
    (rows : decoded.rows.cells=input) (bits : decoded.rows.payload=payload)
    {Site : Type} (arena : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (places : ℕ → Placed Site) (geometry : ℕ → ℕ) (extra : ℕ → List Record)
    (roster : ProducedRoster arena l raw places geometry extra arg)
    (saved : (m : Memory w) → SparseCallInput (U u).pub m → Prop) (more : saved built arg) :
    ∃ data : SparseSource id U p, data.logicalAt=input ∧ data.bytesAt=payload ∧
      ProducedRoster arena l raw places geometry extra data.source ∧ saved _ data.source := by
  change built=sparseMemory id U p at address
  subst built
  exact ⟨⟨arg,decoded⟩,rows,bits,roster,more⟩

/-- The suffix returned by the real argument patch ends at precisely the
final state of the positive prefix, even if that prefix's subsequent
private checks or reader entry reject. -/
theorem argument_returned_state : (v).arguments.val.2 = p.2.val.2 := by
  let F := SignedPrep.visitsEquiv id (U u).pub mac ((U u).pins p.1).val.2.1 ((U u).pins p.1).val.2.2
  calc
    _ = (F (F.symm p.2)).val.2 := (SignedPrep.visitsEquiv_outState id (U u).pub mac (v)).symm
    _ = _ := congrArg (fun z => z.val.2) (F.apply_symm_apply p.2)

/-- The same sparse physical submission already yields generated private
cells on the terminal prefix memory. The canonical report and sparse-word
readbacks are available before any independent private bank is selected. -/
theorem submitted_source_and_calls {built : Memory w} {bank : Bank w}
    (address : built=(stages).2.1.val.2.2) (arg : SparseCallInput (U u).pub built)
    (decoded : SparseArgumentCells n arg) (input : ℕ → CellInput) (payload : ℕ → List Bool)
    (rows : decoded.rows.cells=input) (bits : decoded.rows.payload=payload)
    (last : Returns (.block [Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) (U u).pub mac bank built)
    (returned : last.val.2=(v).arguments.val.2)
    (generated : ∃ c : GeneratedCells SparseExterior.driver n (U u).pub last.val.2.2,
      c.cell=input ∧ c.payload=decoded.rows.payload) :
    (∃ data : SparseSource id U p, data.logicalAt=input ∧ data.bytesAt=payload) ∧
    ∃ c : GeneratedCells SparseExterior.driver n (U u).pub p.2.val.2.2,
      c.cell=input ∧ c.payload=payload := by
  refine ⟨source_of_launched id U p address arg decoded input payload rows bits,?_⟩
  have ending := congrArg Prod.snd (returned.trans (argument_returned_state id U p))
  rw [←ending]
  obtain ⟨c,read,raw⟩ := generated
  exact ⟨c,read,raw.trans bits⟩

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
