import OAI.Computability.BorderVNP.RoutingISAFiniteScalarBatch
import OAI.Computability.BorderVNP.FiniteScalarLibrarySign

/-! # The native scalar suffix with the actual finite-field routine installed

The ordinal for each scalar is fixed in the finite control. A cell supplies
only its bit-major digit bank, as physically addressed in the task table.
All extracted private events and their finite-field outputs agree with
the original cell subtotals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FiniteScalarBatch

open VPVNP.BurstRAM TeamSite FiniteScalarRounds FiniteScalarLibrary

/-- On a well-formed finite-field row the fixed library at slot one has only the
empty successful choice string. Its unique native return is the row's field multiplier. -/
theorem Row.scalar {Q : Type} {m d w fuel : ℕ} (F : Type*) [Field F] [Fintype F]
    (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth) (old : FieldProcessor.Returns Q (Option Bool) F m 8)
    (r : Row) (c : Index F → Fin d → Bool) (hw : 0 < w) (claims : r.claims=stream F c)
    (clock : 2*d*Fintype.card F < fuel) :
    (∀ bs, TeamSiteEvents.macros (combine F lib) fuel 1 (r.words w) bs =
      if bs.isEmpty then some .plus else none) ∧
    FieldProcessor.returned (combine F lib 1) (returns F lib old 1) fuel (r.event w) =
      some (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (c i))) := by
  constructor
  · intro bs
    rw [Row.words,claims]
    exact macro_one F lib c hw fuel clock bs
  · have oldWords : (r.event w).old=CompactFrame.pack w (stream F c) := congrArg (CompactFrame.pack w) claims
    rw [scalar_return F lib old c hw (r.event w) fuel oldWords clock]
    rfl

/-- The checked digit suffix is physically present whenever the real task's external
bank is the supplied-port prefix followed by that digit bank. -/
theorem Row.source {w : ℕ} (r : Row) (m : Memory w) (bank : r.task.cell.external = r.supplied ++ r.claims)
    (actual : CompactWrite.Source m r.task.cell.externalBase r.task.cell.external) :
    CompactWrite.Source m r.src r.claims := by
  rw [bank] at actual
  intro i hi
  have h := actual (r.supplied.length+i) (by simp;omega)
  simpa only [Row.src,Nat.add_assoc,List.getElem_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left] using h

/-- Every private event of the true scalar-stage chronology receives its original
field product. Retaining the event itself also distinguishes a zero field return
from a failing count validation at the preceding signed cell. -/
theorem field_run {Q : Type} {w m table count calls tails fuel : ℕ} (F : Type*) [Field F] [Fintype F]
    (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth) (old : FieldProcessor.Returns Q (Option Bool) F m 8)
    (pub : Arg → Word w) (s : Bank w) (mem : Memory w) (rows : ℕ → Row)
    (d : ℕ → ℕ) (claim : (i : ℕ) → Index F → Fin (d i) → Bool)
    (frame : (pub 0).val+92 < 2^w) (width : (mem ((pub 0).val+30)).val=w)
    (tableWord : (mem ((pub 0).val+89)).val=table) (len : (mem ((pub 0).val+90)).val=count)
    (callWord : (mem ((pub 0).val+14)).val=calls) (control : (mem ((pub 0).val+92)).val+7 < 2^w)
    (tailWord : (mem ((mem ((pub 0).val+92)).val+7)).val=tails) (space : table+7*count ≤ 2^w)
    (source : ∀ i < count, Stored (rows i) (written mem rows i) table calls tails i)
    (fit : ∀ i < count, Fits (rows i) w tails)
    (streamAt : ∀ i < count, (rows i).claims=stream F (claim i))
    (clock : ∀ i < count, 2*d i*Fintype.card F < fuel) :
    let mac := TeamSiteEvents.macros (combine F lib) fuel
    ∃ es t, Runs pub mac code s mem es t (written mem rows count) ∧
      traceCost es ≤ setup.slots+(∑ j ∈ Finset.range count, ((rows j).cost w+1))+1 ∧
      bursts es = (List.range count).map (fun j => (rows j).event w) ∧
      (bursts es).map (FieldProcessor.returned (combine F lib 1) (returns F lib old 1) fuel) =
        (List.range count).map (fun j => some (∏ i, (Fintype.equivFin F).symm i ^
          FieldPowers.digits (List.ofFn (claim j i)))) ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      ∀ gs v mu, Runs pub mac code s mem gs v mu → gs=es ∧ v=t ∧ mu=written mem rows count := by
  intro mac
  have hw : 0 < w := by cases w with
    | zero => simp at frame
    | succ w => exact Nat.zero_lt_succ w
  have h (i : ℕ) (hi : i < count) := (rows i).scalar F lib old (claim i) hw (streamAt i hi) (clock i hi)
  obtain ⟨es,t,r,cost,events,clean,unique⟩ := run pub mac s mem rows frame width tableWord len callWord
    control tailWord space source fit (fun i hi => (h i hi).1)
  refine ⟨es,t,r,cost,events,?_,clean,unique⟩
  rw [events,List.map_map]
  exact List.map_congr_left (fun i hi => (h i (List.mem_range.mp hi)).2)

end RoutingISA.FiniteScalarBatch

end BorderVNP
end Computability
end OAI
