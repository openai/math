import OAI.Computability.VPVNP.PairSimulationScanTrace
import OAI.Computability.VPVNP.PairSimulationEndpointBits
import OAI.Computability.VPVNP.CompressorSlicePreparation
import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout

/-!
# Publishing final arc offsets and total bit width

The terminal prefix worker reads the final state's outgoing widths in physical
base, lane and slot order. The running total before each arc is precisely the
offset expected by the endpoint reader. The accumulator after the last arc
holds the exclusive end of the shared bit array, relative to its base.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression LocalHistory PrimedStackRAM
open scoped Fin.CommRing
open private actualWidth scanWidth scanWidth_sum from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {a g w : ℕ}

/-- The edge order used by both the terminal bit scan and the physical incidence directory. -/
abbrev arcCount (X : State a g) := (edgeOrder X).length

/-- Width of the final arc at this ordinal in the terminal prefix scan's physical order. -/
def width (X : State a g) (i : Fin (arcCount X)) := scanWidth X i

theorem width_sum (X : State a g) : ∑ i, width X i = X.totalWidth := scanWidth_sum X

theorem actualPort_eq (X : State a g) (e : X.network.Edge) :
    IncidenceDirectory.actualPort (w := w) X e =
      (((edgeOrder X).entries.symm e).val : Word w) :=
  IncidenceDirectory.actualPort_number X e

/-- Three physical operands of the standard one-arc prefix worker. -/
def operands (T : IncidenceDirectory w) (prefixBase totalCell : Word w) : Fin 3 → Word w :=
  ![T.width, prefixBase, totalCell]

/-- Prefix-sum instruction template for the terminal width array, entered with an initial zero
running total. -/
abbrev table := template SliceRAM.prefixOps 0

private theorem take_sum {n : ℕ} (values : Fin n → ℕ) (j : Fin n) :
    ((List.ofFn values).take j.val).sum = EndpointBits.offset values j := by
  have h : (List.ofFn values).take j.val =
      List.ofFn (fun i : Fin j.val => values (i.castLE j.isLt.le)) := by
    apply List.ext_getElem
    · simp [j.isLt.le]
    · intro i hi hi'
      simp
  rw [h, List.sum_ofFn, EndpointBits.offset]

/-- Every live start cell, the running total and the unchanged memory around the
two output regions. These facts also apply to an empty final graph. -/
structure Stored (X : State a g) (T : IncidenceDirectory w) (prefixBase totalCell : Word w)
    (initial final : Memory w) : Prop where
  start : ∀ i : Fin (arcCount X),
    (final (prefixBase.val + i.val)).val = EndpointBits.offset (width X) i
  total : (final totalCell.val).val = X.totalWidth
  widths : ∀ i : Fin (arcCount X), (final (T.width.val + i.val)).val = width X i
  outside : ∀ x, x ≠ totalCell.val →
    (x < prefixBase.val ∨ prefixBase.val + arcCount X ≤ x) → final x = initial x

private theorem width_cells (X : State a g) (T : IncidenceDirectory w) (m : Memory w)
    (rep : T.ActualColumns X m) (room : T.width.val + arcCount X ≤ 2 ^ w)
    (totalFit : X.totalWidth < 2 ^ w) (i : Fin (arcCount X)) :
    (m (T.width.val + i.val)).val = width X i := by
  let e := (edgeOrder X).entries i
  have port : IncidenceDirectory.actualPort (w := w) X e = (i.val : Word w) := by
    simp only [e, actualPort_eq, Equiv.symm_apply_apply]
  have bound := Finset.single_le_sum (f := width X) (fun j _ => Nat.zero_le (width X j))
    (Finset.mem_univ i)
  have small : width X i < 2 ^ w := bound.trans_lt ((width_sum X).trans_lt totalFit)
  have hv := congrArg Fin.val (rep.width e)
  rw [port] at hv
  have loc : (T.width + (i.val : Word w)).val = T.width.val + i.val := by
    have hi := i.isLt
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : i.val < 2 ^ w),
      Nat.mod_eq_of_lt (by omega : T.width.val + i.val < 2 ^ w)]
  rw [loc] at hv
  exact hv.trans (Nat.mod_eq_of_lt small)

/-- Execute one call per outgoing arc. The word-indexed incidence column is the
source. The start and total cells are the only cells the execution can change. -/
theorem run (X : State a g) (T : IncidenceDirectory w) (m : Memory w)
    (rep : T.ActualColumns X m) (prefixBase totalCell : Word w)
    (regions : SliceRAM.PrefixRegions (operands T prefixBase totalCell) (arcCount X))
    (countFit : arcCount X < 2 ^ w) (totalFit : X.totalWidth < 2 ^ w)
    (zero : m totalCell.val = 0) :
    let M := table.instantiate w (operands T prefixBase totalCell)
    ∃ rs, runSegment M.program 14 (some 0) m (List.replicate (arcCount X) []) = some rs ∧
      Stored X T prefixBase totalCell m (after m (eventLog rs)) ∧
      endState (some 0) rs = some (arcCount X : Word w) ∧ rs.length = arcCount X ∧
      ∀ r ∈ rs, r.probes = 4 ∧ r.events.length = 13 := by
  let pub := operands T prefixBase totalCell
  let ws := List.ofFn (width X)
  have hlen : ws.length = arcCount X := List.length_ofFn
  have hsum : ws.sum = X.totalWidth := List.sum_ofFn.trans (width_sum X)
  have values (i : ℕ) (hi : i < ws.length) : (m ((pub 0).val + i)).val = ws[i] := by
    change (m (T.width.val + i)).val = _
    simpa only [ws, List.getElem_ofFn] using width_cells X T m rep regions.widthsFit totalFit
      ⟨i, hlen ▸ hi⟩
  obtain ⟨rs, executed, filled, ended, calls, traffic⟩ := SliceRAM.prefixPass_run
    (pub := pub) (ws := ws) (hlen ▸ regions) (hlen.trans_lt countFit) (hsum.trans_lt totalFit)
    values (by rw [show pub 2 = totalCell from rfl, zero]; rfl)
  refine ⟨rs, hlen ▸ executed, ⟨?_, ?_, ?_, ?_⟩, hlen ▸ ended, calls.trans hlen, ?_⟩
  · intro i
    exact (filled.starts i.val (i.isLt.trans_eq hlen.symm)).trans (take_sum (width X) i)
  · change (after m (eventLog rs) (pub 2).val).val = _
    simpa only [List.take_length, hsum] using filled.total
  · intro i
    change (after m (eventLog rs) ((pub 0).val + i.val)).val = _
    simpa only [ws, List.getElem_ofFn] using filled.widths i.val (i.isLt.trans_eq hlen.symm)
  · exact fun x hx outside => filled.outside x hx (hlen ▸ outside)
  · intro r hr
    obtain ⟨hp, ht⟩ := traffic r hr
    exact ⟨hp, by omega⟩

end PairSimulation.TerminalPrefix

end VPVNP
end Computability
end OAI
