import OAI.Computability.BorderVNP.DiagonalSparseReportSources
import OAI.Computability.BorderVNP.CellSparseExteriorTeamCost

/-! # Measured native fields of an arbitrary owned signed call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM SparseExterior TypedTaskBuilder Diagonal.ExternalSew.Fragments

variable {w : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before (readings e.output) (R).cells
local notation "idx" => globalCell (R).toLayout (readings e.output)
variable (rows : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
    SparseCell a f orig data i.val)
    (ownerOrder : ∀ i, (rows i).number.val=globalCell (a.controlRows team frame offsets ctl live ports).toLayout (readings e.output) i.val)
local notation "owned" => e.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows

include ownerOrder in
/-- At each true global owned cell the physical compressed field reads the
scanner's supplied-width scalar and the actual selected report tail. Each
span has a positive bit extent before any private generator has run. -/
theorem SparseEmission.measuredField (c : Fin a.cube.cells) (mine : (R).owner raw c.val=(R).team) :
    ∃ i : Fin num, (rows i).number=c ∧
    let field := (owned c.val).field
    field.width=readings orig (f.supplied+c.val) ∧ field.tail=(rows i).tail ∧
      Ordered field.width 0 field.spans ∧ ∀ span∈field.spans, 0<span.bits.length := by
  let i : Fin num := ⟨(R).before raw c.val,(R).toLayout.before_strict raw c.isLt mine⟩
  have found : idx i.val=c.val := global_at (R).toLayout raw c.isLt mine
  have number : (rows i).number=c := Fin.ext ((ownerOrder i).trans found)
  have cellRow := e.globalCells_at (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) rows i
  rw [found] at cellRow
  refine ⟨i,number,?_⟩
  dsimp only
  rw [cellRow]
  refine ⟨?_,rfl,(rows i).ordered,fun s hs => stream_positive _ _ _ _ _ _ _ hs⟩
  change readings orig (f.supplied+(rows i).number.val)=_
  rw [number]

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
