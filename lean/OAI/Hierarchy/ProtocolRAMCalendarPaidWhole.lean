import OAI.Hierarchy.ProtocolRAMCalendarPricedWhole
import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter

namespace OAI
/-! # The original finite header and the actual earned terminal link widths -/

namespace Hierarchy.ProtocolRAM.Calendar.Whole.Priced.Paid
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe PurchaseStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {z d k q goods r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}
variable (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (s : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
local notation "C" => pricedInstalled c finish prices format feeds s idBase role ids
local notation "V" => markets c finish prices format
local notation "W" => wordBits z d copies

def program (flag src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :=
  (subdivisionProgram z d).seq (paidReporter C flag s src ss a count n reserve)

def ticks (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :=
  subdivisionConstant d*2^z+paidReporterTime C s ss a count n reserve

local notation "P" => program c finish prices format feeds s idBase role ids
local notation "T" => ticks c finish prices format feeds s idBase role ids

attribute [local irreducible] CheapCode Procedure.Exec

theorem cheap (flag src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    CheapCode (P flag src ss a count n reserve) :=
  cheap_seq (subdivision_cheap z d) (paidReporter_cheap C flag s src ss a count n reserve)

omit [Fintype I] [Fintype J] in
theorem exec {size n count : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→Fin count)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (wide : s.banks.width.base+edges<2^W)
    (paid : PaidWidths.Mounted s.banks.width edges src ss (checkedOut C flag (Boot.booted V size words)))
    (actual : Reconciliation s a reserve site debit e ci cj
      (PaidWidths.output s.banks.width edges src ss (checkedOut C flag (Boot.booted V size words)))) :
    (P flag src ss a count n reserve).Exec
      (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words))
      (s.output (paidSource C flag s src ss a reserve site debit (Boot.booted V size words))
        e ci (fun j=>(cj j).val)) (T ss a count n reserve) := by
  have sunk := actual.ports.mounted a reserve site debit actual.archive actual.usedSize actual.reserveSize
    actual.funded actual.word
  have tail := paidReporter_exec C flag s src ss a reserve site debit e ci (fun j=>(cj j).val)
    (Boot.booted V size words) scheduled fit room wide paid actual.archive sunk
  exact Procedure.Exec.then (Boot.start V layout hd π words authentic).1 tail

omit [Fintype I] [Fintype J] in
theorem run {size n count : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag src : ℕ)
    (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→Fin count) (state : Word W)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words)) (order : separated C (events (C).mesh))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (wide : s.banks.width.base+edges<2^W)
    (paid : PaidWidths.Mounted s.banks.width edges src ss (checkedOut C flag (Boot.booted V size words)))
    (actual : Reconciliation s a reserve site debit e ci cj
      (PaidWidths.output s.banks.width edges src ss (checkedOut C flag (Boot.booted V size words))))
    (below : flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let M := machine (P flag src ss a count n reserve) (flag:Word W)
    let out := s.output (paidSource C flag s src ss a reserve site debit (Boot.booted V size words))
      e ci (fun j=>(cj j).val)
    ∃ t≤T ss a count n reserve+2, ∃ term,
      advance M.program t (M.program.start state) (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words))=
        some (term,out) ∧ M.program.step term=.finish (some (out flag)) ∧
      (out flag=0 ↔ admissible C (events (C).mesh) (Boot.booted V size words)) := by
  dsimp only
  let start := Boot.booted V size words
  let m := PaidWidths.output s.banks.width edges src ss (checkedOut C flag start)
  let out := s.output (paidSource C flag s src ss a reserve site debit start) e ci (fun j=>(cj j).val)
  have ran := exec c finish prices format feeds s idBase role ids layout hd π words authentic flag src ss a
    reserve site debit e ci cj scheduled fit room wide paid actual
  obtain ⟨t,ht,term,adv,halt⟩ := machine_run (P flag src ss a count n reserve)
    (flag:Word W) state (Boot.initial V size words) out _ ran
  rw [Fin.val_cast_of_lt (by omega : flag<2^W)] at halt
  refine ⟨t,ht,term,adv,halt,?_⟩
  obtain ⟨res,used,scratch,stock,tab,dest⟩ := below
  change s.output (ReserveUse.output a s.banks reserve site debit m) e ci (fun j=>(cj j).val) flag=0 ↔ _
  rw [s.frame _ _ _ _ _ stock tab dest actual.ports.width,
    ReserveUse.frame _ _ _ _ _ m flag (.inl res) (.inl used) (.inl scratch)]
  change PaidWidths.output s.banks.width edges src ss (checkedOut C flag start) flag=0 ↔ _
  rw [PaidWidths.frame _ _ _ _ _ _ (fun x hx=>(paid x hx).1) stock]
  exact checked_read C flag _ scheduled order (by have := actual.ports.wide;omega)

end
end Hierarchy.ProtocolRAM.Calendar.Whole.Priced.Paid

end OAI
