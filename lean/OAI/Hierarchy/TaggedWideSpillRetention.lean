import OAI.Hierarchy.TaggedWideSpillAfterRoles
import OAI.Hierarchy.TaggedWidePageSweep

namespace OAI
/-! # The final spill-turn publisher preserves every preceding dated result -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM ProbeStage.CoreBoard.HistoryRoles
open scoped Classical
variable {T W : ℕ} (z : SpillDates T) (rom old start : ℕ)
variable (count : ∀j,z.original.controlColumns j=SiteControls.fieldCount z.original.roleCount)
local notation "R" => 3*((T+1)*3)
local notation "role" => z.roleSheet rom start
local notation "ballot" => z.ballot rom old start
local notation "packet" => z.packetControl rom old start
local notation "spill" => fun j=>z.spillControl rom old start j count

theorem SpillDates.results_prefix_below (rr : Fin R→Memory W→Prop) (br pr sr : Fin T→Memory W→Prop)
    (rLocal : PagePrefixLocal role rr) (bLocal : PagePrefixLocal ballot br)
    (pLocal : PagePrefixLocal packet pr) (sLocal : PagePrefixLocal spill sr)
    (input out : Memory W) (low : ∀a,a<z.endAt start → out a=input a)
    (r : ∀i,rr i input) (b : ∀i,br i input) (p : ∀i,pr i input) (s : ∀i,sr i input) :
    (∀i,rr i out) ∧ (∀i,br i out) ∧ (∀i,pr i out) ∧ ∀i,sr i out := by
  have e : R+(T+(T+T))=SpillDates.last T+1:=by dsimp [SpillDates.last];omega
  let pages : Fin (R+(T+(T+T))) → Scatter := Fin.addCases role (Fin.addCases ballot (Fin.addCases packet spill))
  have max (j : Fin (R+(T+(T+T)))) : (pages j).stop≤z.endAt start := by
    simpa only [pages,SpillDates.sheets,Function.comp_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using
      (z.ordered rom old start count).upper (Fin.cast e j)
  have transfer {n : ℕ} {pages : Fin n→Scatter} {facts : Fin n→Memory W→Prop}
      (keep : PagePrefixLocal pages facts) (i : Fin n) (held : facts i input)
      (bound : (pages i).stop≤z.endAt start) : facts i out :=
    keep i input out (fun a small=>low a (small.trans_le bound)) held
  refine ⟨fun i=>transfer rLocal i (r i) ?_,fun i=>transfer bLocal i (b i) ?_,
    fun i=>transfer pLocal i (p i) ?_,fun i=>transfer sLocal i (s i) ?_⟩
  · simpa only [pages,Fin.addCases_left] using max (Fin.castAdd (T+(T+T)) i)
  · simpa only [pages,Fin.addCases_right,Fin.addCases_left] using max (Fin.natAdd R (i.castAdd (T+T)))
  · simpa only [pages,Fin.addCases_right,Fin.addCases_left] using max (Fin.natAdd R (Fin.natAdd T (i.castAdd T)))
  · simpa only [pages,Fin.addCases_right] using max (Fin.natAdd R (Fin.natAdd T (Fin.natAdd T i)))

theorem SpillDates.results_below (rr : ∀i,PageResult W (role i)) (br : ∀i,PageResult W (ballot i))
    (pr : ∀i,PageResult W (packet i)) (sr : ∀i,PageResult W (spill i)) (input out : Computability.VPVNP.BurstRAM.Memory W)
    (low : ∀a,a<z.endAt start → out a=input a)
    (r : ∀i,(rr i).holds input) (b : ∀i,(br i).holds input)
    (p : ∀i,(pr i).holds input) (s : ∀i,(sr i).holds input) :
    (∀i,(rr i).holds out) ∧ (∀i,(br i).holds out) ∧ (∀i,(pr i).holds out) ∧ ∀i,(sr i).holds out :=
  z.results_prefix_below rom old start count (fun i=>(rr i).holds) (fun i=>(br i).holds)
    (fun i=>(pr i).holds) (fun i=>(sr i).holds)
    (fun i x y same=>(rr i).localize x y (fun a _ small=>same a small))
    (fun i x y same=>(br i).localize x y (fun a _ small=>same a small))
    (fun i x y same=>(pr i).localize x y (fun a _ small=>same a small))
    (fun i x y same=>(sr i).localize x y (fun a _ small=>same a small))
    input out low r b p s

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
