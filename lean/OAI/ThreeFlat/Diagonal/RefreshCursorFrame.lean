import OAI.ThreeFlat.Diagonal.RefreshCursorRuns

namespace OAI
/-! # Native procedure returns preserve the immutable chronological cursor -/

namespace ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory
open RefreshDemandRows CompressorPacking.Native RAM.PhysicalProcedure

variable {W v a t h pad K : ℕ} {cur : Word W} {mem : Memory W} {c : Cursor}
    (u : CursorSpace cur mem c K v a t h pad)
set_option quotPrecheck false
local notation "e" => allocate K c (.refresh v (mPort a) (2^t) h pad)
local notation "keep" => fun i : ℕ=>i<c.heap ∨ (e).next.heap≤ i

include u

theorem frame (out : Memory W) (kept : ∀ i,keep i → out i=mem i) : CursorSpace cur out c K v a t h pad where
  header := ⟨(congrArg Fin.val (kept _ (.inr u.controls))).trans u.header.pointer,
    u.header.fit,fun i hi=>(congrArg Fin.val (kept _ (u.start_live i hi))).trans (u.header.values i hi)⟩
  graph := u.graph
  widths := u.widths
  counts := u.counts
  earlier := u.earlier
  controls := u.controls

theorem call (p : Scans W) (safe : p.every (Scans.Safe 63 (e).words keep)) :
    let exe := p.pipeline cur
    exe.program.Spec (fun n=>n=mem)
      (fun _ out=>out=exe.run mem ∧ CursorSpace cur out c K v a t h pad ∧ ∀ i,keep i → out i=mem i)
      (p.time (e).words) := by
  refine Procedure.Spec.mono (A:=(p.pipeline cur).program) (pre:=fun n=>n=mem)
    (post:=fun _ out=>out=(p.pipeline cur).run mem ∧ ∀ i,keep i → out i=mem i)
    (budget:=p.time (e).words)
    (p.native_spec cur mem c.header 63 (e).words keep u.header (.inr u.controls) u.start_live safe)
    (fun _=>id) ?_ le_rfl
  intro _ out result
  exact ⟨result.1,u.frame out result.2,result.2⟩


end ThreeFlat.Diagonal.RefreshStageNav.CursorSpace

end OAI
