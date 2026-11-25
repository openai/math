import OAI.Hierarchy.ProtocolRAMTerminalSinkSpace
import OAI.Hierarchy.ProtocolRAMCoreRouteMount
import OAI.Hierarchy.ProtocolRAMCatalystArchiveRun

namespace OAI
/-! # Mounting native walk directories in the terminal settlement sink -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
variable {z W k w R attempts edges K q goods n : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)

theorem before (p : Recipes) (x : Source) (s : Sink r edges) (π : Equiv.Perm (Fin (2^z)))
    (place : Site z D k→Fin K) (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k)
    (o : Orders z D k) (physical : ∀e,(B.row e).val=(order.symm e).val) (m : Memory w)
    (data : Readable x S z W k attempts order π m) (ci : Commodity (Fin (2^z)) N k→ℕ)
    (cj : Columns z D×Fin k→ℕ) (rom : Installed p o ci cj m) (words : Owners s.owners edges m)
    (space : SinkSpace s w) (cap : 2*r≤2^w) (wider : 2<2^w) (menu : Fintype.card (Actions N k)≤2^w)
    (kindCap : 2*r≤ s.banks.kind.size) (indexCap : 2*r≤ s.banks.index.size)
    (apart : s.banks.kind.base+2*r≤ s.banks.index.base)
    (early : s.owners.base+s.owners.size≤ s.banks.kind.base)
    (prior : (indexWord p x S z W k attempts).Fits w s.banks.kind.base) :
    s.Before (result (stages s.banks p x S z W k attempts) m) (enum B o) ci cj := by
  refine ⟨actual p x s.banks π place B order o physical m data ci cj rom cap wider menu kindCap indexCap apart prior,
    ?_,space.kind,space.index,space.ownerReserve,space.ownerWidth,space.inputs,space.source,space.width,
    space.wide,space.fields,space.table,space.destination,space.apart⟩
  intro i j
  let a : Word w := (8*i.val+j.val:ℕ)
  have low := (Nat.add_lt_add_left (Nat.mod_lt a.val (Nat.two_pow_pos s.owners.bits)) s.owners.base).trans_le early
  exact (result_below _ _ _ (by
    intro pass member
    simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact low
    · exact low.trans_le ((Nat.le_add_right s.banks.kind.base (2*r)).trans apart))).trans (words i j)

/-- The preexisting occurrence-owner code and the CT geometry survive checkout,
paid width accumulation and all guarded owner scans below the new route directory. -/
theorem owners_at_route (C : Chart w q goods) (A : Arena) (ledger : CatalystArchive.OwnerLedger)
    (flag count : ℕ) (s : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice) (m : Memory w)
    (owners : Owners s.owners edges m) (scheduled : mounted C (events C.mesh) m)
    (floor : ∀e a,a<A.base C.mesh e→protected C a e) (fixed : s.owners.base+s.owners.size≤A.first)
    (flagHigh : A.first≤flag) (cash : A.first≤ s.banks.width.base) (ids : s.banks.width.base≤ledger.arena.first)
    (fits : ∀p∈ss,p.Fits s.banks.width edges src w) :
    Owners s.owners edges (result (ledger.scans C.mesh count)
      (PaidWidths.output s.banks.width edges src ss (checkedOut C flag m))) := by
  intro i j
  let a : Word w := (8*i.val+j.val:ℕ)
  let addr := s.owners.base+a.val%s.owners.size
  have low : addr<A.first := (Nat.add_lt_add_left (Nat.mod_lt a.val (Nat.two_pow_pos s.owners.bits)) _).trans_le fixed
  have keep := run_frame C (events C.mesh) m addr scheduled
    (fun e _=>floor e addr (low.trans_le (Nat.le_add_right ..)))
  have chk : checkedOut C flag m addr=m addr := by
    exact (ProtocolRAMGeneratedWrite.frame_image flag 1 (historyFlag C (events C.mesh))
      (run C (events C.mesh) m) addr (.inl (low.trans_le flagHigh))).trans keep
  exact (ledger.before C.mesh count _ addr (low.trans_le (cash.trans ids))).trans
    ((PaidWidths.frame _ _ _ _ _ _ fits (low.trans_le cash)).trans (chk.trans (owners i j)))

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
