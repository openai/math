import OAI.Computability.BorderVNP.DiagonalNativeCallState
import OAI.Computability.BorderVNP.RoutingISASparseCells

/-! # Native weighted cell calls with a state-dependent continuation

The signed finite enumeration of private cell outcomes factors from the remaining
tally and residue computation. Every accepting private outcome in one directory
leaves the external continuation in the same registers and memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CellDispatch CompactMachine CellMacro.Generator
open scoped BigOperators Classical

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)

/-- The final bank after scanning the call directory. Choosing the initial bank in
the empty case has no effect on any weighted sum because the directory rejects. -/
noncomputable def cellBank : Bank w :=
  if h : Nonempty (Returns callOwnedCells pub mac s m) then h.some.val.2.1 else s

/-- Enumerated real directory events correspond to full returns with their post-state.
This also proves finiteness on every bounded input for which the private outcomes are finite. -/
noncomputable def cellHistoriesEquiv {choices : List (Word w) → Finset Outcome}
    (spec : ∀ v o, o ∈ choices v ↔ mac 0 v o.1 = some o.2)
    (frameFit : (pub 0).val+15 < 2^w) (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w) :
    Returns callOwnedCells pub mac s m ≃ ↑((Frame.ofMemory pub m).histories pub m choices) := by
  let f (z : Returns callOwnedCells pub mac s m) : ↑((Frame.ofMemory pub m).histories pub m choices) :=
    ⟨z.val.1,(Frame.mem_histories spec frameFit room _).2 z.property.execute⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b h
    have e : a.val.1 = b.val.1 := congrArg Subtype.val h
    obtain ⟨r1,r2⟩ := CellDispatch.same_post a.property b.property
    exact Subtype.ext (Prod.ext e (Prod.ext r1 r2))
  · rintro ⟨es,he⟩
    obtain ⟨⟨t,mt,r⟩,_⟩ := (Code.execute_iff_runs (c := callOwnedCells) (by decide)).mp
      ((Frame.mem_histories (s := s) spec frameFit room _).1 he)
    exact ⟨⟨(es,t,mt),r⟩,rfl⟩

/-- All private weights multiply the same continuation value. An empty private
history set contributes zero, irrespective of the continuation. -/
theorem cell_sum_with {choices : List (Word w) → Finset Outcome}
    (spec : ∀ v o, o ∈ choices v ↔ mac 0 v o.1 = some o.2)
    (frameFit : (pub 0).val+15 < 2^w) (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (next : Bank w → Memory w → ℤ) [Fintype (Returns callOwnedCells pub mac s m)] :
    (∑ z : Returns callOwnedCells pub mac s m, pathWeight z.val.1 * next z.val.2.1 z.val.2.2) =
      (∑ es ∈ (Frame.ofMemory pub m).histories pub m choices, pathWeight es) * next (cellBank pub mac s m) m := by
  let e := cellHistoriesEquiv pub mac s m spec frameFit room
  rw [Finset.sum_mul,← Finset.sum_coe_sort ((Frame.ofMemory pub m).histories pub m choices)
    (fun es => pathWeight es * next (cellBank pub mac s m) m),← e.sum_comp (fun z => pathWeight z.val * next (cellBank pub mac s m) m)]
  apply Finset.sum_congr rfl
  intro z _
  have nonempty : Nonempty (Returns callOwnedCells pub mac s m) := ⟨z⟩
  have reg := (CellDispatch.same_post z.property nonempty.some.property).1
  obtain ⟨_,_,_,_,_,mem⟩ := CellDispatch.directory_decode frameFit room z.property
  change pathWeight z.val.1 * next z.val.2.1 z.val.2.2 = pathWeight z.val.1 * next (cellBank pub mac s m) m
  rw [mem,cellBank,dite_eq_left nonempty,reg]

/-- For the installed fixed private generator the coefficient of a native continuation
is the product of all owned sparse cell weights. The actual argument words, clock and
burst constraints are the same as those of the native private machine. -/
theorem sparseCell_sum_with (d h n : ℕ) (cells : ℕ → CellInput) (hw : 0 < w)
    (frameFit : (pub 0).val+15 < 2^w) (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (span : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val = (Frame.ofMemory pub m).team →
      (m ((Frame.ofMemory pub m).address i+1)).val + (m ((Frame.ofMemory pub m).address i+2)).val ≤ 2^w)
    (cap : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val = (Frame.ofMemory pub m).team →
      (m ((Frame.ofMemory pub m).address i+2)).val ≤ TeamScales.width n (1/2))
    (words : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val = (Frame.ofMemory pub m).team →
      TeamRAM.previous m ((Frame.ofMemory pub m).burst m i) = CompactFrame.pack w (serialized d (cells i).stmt))
    (depth : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val = (Frame.ofMemory pub m).team →
      ((cells i).directory.program (cells i).privateWires).FitsDepth d h)
    (clock : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val = (Frame.ofMemory pub m).team →
      2*(cells i).allowance w d ≤ n^25) (next : Bank w → Memory w → ℤ)
    [Fintype (Returns callOwnedCells pub (install (generate d h) n mac) s m)] :
    let f := Frame.ofMemory pub m
    let compiled := install (generate d h) n mac
    (∑ z : Returns callOwnedCells pub compiled s m, pathWeight z.val.1 * next z.val.2.1 z.val.2.2) =
      ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod * next (cellBank pub compiled s m) m := by
  let compiled := install (generate d h) n mac
  have matchRows := sparse_directory_sum (d := d) (h := h) (n := n) pub cells hw span cap words depth clock
  exact (cell_sum_with pub compiled s m (mem_choices (generate d h) n mac) frameFit room next).trans
    (congrArg (· * next (cellBank pub compiled s m) m) matchRows)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
