import OAI.Hierarchy.DescentTerminalPrimitiveArenaKit
import OAI.Hierarchy.DescentTerminalPrimitiveNames
import OAI.Hierarchy.DescentTerminalPointerPair
import OAI.Hierarchy.DescentTerminalPrimitiveFrames

namespace OAI
/-! # The complete terminal primitive procedure with its real numerical address plan -/
namespace Hierarchy.DescentTerminalPrimitiveArena
open DescentTerminalVertexFields DescentTerminalPrimitiveNames DescentEpochTagKeys DescentSIMDLookup
open DescentTerminalPointerDigits DescentTerminalCombinedRole ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {U:Type} {n a g p r N M blocks shops groups wb cap d dc u v:ℕ}
    (old:Codec U n) (raw:Fin 6→Bank) (advice start pop:ℕ) (occupied:Fin blocks→Bank)
    (pages:Gather.Pages blocks cap M)
    (f0:(Fin (columns cap N M)→Cell d)→Cell u) (f7:(Fin (columns cap N M)→Cell d)→Cell v)
    (q hid:ℕ)
local notation "s" => actual blocks shops cap N M d dc
local notation "bits" => fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups
local notation "first" => DescentTerminalRoleTables.role bits raw advice
local notation "second" => DescentTerminalRoleTables.arity bits raw advice
local notation "origin" => Shape.gather s start
local notation "chart" => pages.address (N:=N)
local notation "src" => Shape.sources s start pop
local notation "pg" => Gather.dropOff origin blocks shops (Shape.columns s) chart
local notation "roleEnd" => DescentTerminalCombinedRole.memory first second start (Shape.rows s)
local notation "working" => Gather.banks (L:=Shape.columns s) origin (Shape.rows s)
local notation "cost" => DescentTerminalPrimitiveNames.clocks d dc origin shops chart

def issue :=
  DescentTerminalPrimitiveNames.program wb first second start origin shops chart f0 f7 src dc ((s).counting start) ((s).widths start)
    q hid N M groups p
def image (m:Memory wb) :=
  let cols:=ProtocolRAM.result pg (roleEnd m)
  let publicMem:=DescentTerminalPointerFrame.result ((s).rom start) working (s).rows f0 cols
  let ptrMem:=DescentTerminalPointerFrame.result ((s).public start+(s).rows) working (s).rows f7 publicMem
  DescentTerminalCountWidthPair.final dc q hid N M groups blocks shops p ((s).counting start) ((s).widths start) src ptrMem

local notation "machine" => issue (n:=n) (a:=a) (g:=g) (r:=r) (p:=p) (N:=N) (groups:=groups)
  (wb:=wb) (shops:=shops) (dc:=dc) raw advice start pop pages f0 f7 q hid
local notation "after" => image (n:=n) (a:=a) (g:=g) (r:=r) (p:=p) (N:=N) (groups:=groups)
  (shops:=shops) (dc:=dc) raw advice start pop pages f0 f7 q hid
theorem native (initial mountedMem:Memory wb) (prior:(s).Prior start pop occupied) (limit:(s).finish start<2^wb)
    (input:∀f,(raw f).Fits wb start) (romEnd:advice+DescentTerminalRoleTables.count bits≤ start)
    (bounded:∀ (j : Fin (columns cap N M)) (b : Fin blocks),(chart j b).Fits origin shops wb)
    (mounted:∀j,advice≤j→j<advice+DescentTerminalRoleTables.count bits→initial j=
      DescentStaticWordColumn.image advice
        (DescentTerminalRoleTables.literal (A:=a) (G:=g) (p:=p) (R:=r) (N:=N) (groups:=groups) old M)
        mountedMem (DescentTerminalRoleTables.count bits) j) :
    (machine).Exec initial (after initial) cost ∧ CheapCode machine ∧
    (∀j,j<start→after initial j=initial j) ∧
    (∀b,(((s).channels start pop occupied).occupied b).Fits wb ((s).finish start)) ∧
    (∀b f,(((s).channels start pop occupied).primitive b f).Fits wb ((s).finish start)) ∧
    cost≤40+10*(2*fee (s).columns d+fee 3 dc)+4*((s).columns*blocks)+(s).rows*(476+70*(s).columns) ∧
    DescentStaticWordColumn.names machine≤1030+104*(s).columns+15*(2*fee (s).columns d+fee 3 dc)+39*((s).columns*blocks) := by
  have pos : 0 < (s).columns := by
    change 0 < columns cap N M
    unfold columns
    omega
  have kit:=(s).realized start pop occupied prior limit pos
  have bulk:=(s).paired_fits start limit bits raw advice input romEnd
  have romRoom:advice+DescentTerminalRoleTables.count bits<2^wb:=by
    have pre:=kit.role_first;omega
  have pairTables:=DescentTerminalRoleTables.persistent (A:=a) (G:=g) (p:=p) (R:=r) (N:=N) (groups:=groups)
    old M raw advice mountedMem romRoom initial mounted
  have later: (emit second).Fits wb (start+(s).rows):=ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) bulk.2
  have pair:=DescentTerminalCombinedRole.both old first second start (Shape.rows s) initial bulk.1 bulk.2 later kit.role_first pairTables.1 pairTables.2 rfl
  have write:=Gather.Pages.pair pages (roleEnd initial) origin shops f0 f7 bounded kit.pointer_radix kit.pointer_limit
  let cols:=ProtocolRAM.result pg (roleEnd initial)
  let pub:=DescentTerminalPointerFrame.result ((s).rom start) working (s).rows f0 cols
  let ptr:=DescentTerminalPointerFrame.result ((s).public start+(s).rows) working (s).rows f7 pub
  have last:=DescentTerminalCountWidthPair.run (q:=q) (hid:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups)
    src ((s).counting start) ((s).widths start) ptr kit.source_room kit.count_later kit.width_limit
  refine ⟨?_, ?_,
    ?_,fun b=>(kit.live_inputs b).1,fun b=>(kit.live_inputs b).2,?_,?_⟩
  · exact @Procedure.Exec.then wb _ _ initial (roleEnd initial) (after initial) _ _ (@pair.1)
      (@Procedure.Exec.then wb _ _ (roleEnd initial) ptr (after initial) _ _ (@write.1) (@last.1))
  · exact @DescentTerminalPrimitiveNames.cheap (columns cap N M) blocks d u v wb first second start origin shops
      chart f0 f7 src dc ((s).counting start) ((s).widths start) q hid N M groups p
  · intro j hj
    exact (last.2.2 j (.inl (hj.trans_le (kit.phase_order.1.trans kit.phase_order.2)))).trans
      ((write.2.2.2.1 j (.inl (hj.trans_le kit.phase_order.1))).trans
        (DescentTerminalPrimitiveFrames.paired_below first second start (Shape.rows s) initial j hj))
  · exact DescentTerminalPrimitiveNames.clocks_le ..
  · exact DescentTerminalPrimitiveNames.names_le ..

end
end Hierarchy.DescentTerminalPrimitiveArena

end OAI
