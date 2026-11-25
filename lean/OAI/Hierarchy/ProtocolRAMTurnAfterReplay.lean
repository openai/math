import OAI.Hierarchy.ProtocolRAMTurnReplayed
import OAI.Hierarchy.ProtocolRAMCalendarPrefixWidths
import OAI.Hierarchy.ProtocolRAMTurnPaidCost

namespace OAI
/-! # Chronological weighted turn origins after the genuine paid-prefix and reserve replay -/
noncomputable section
namespace Hierarchy.ProtocolRAMTurnReplayed
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAM.RouteSettlement ProtocolRAM.Calendar
open scoped Classical Fin.CommRing
variable {W K edges r : ℕ} {I C : Type} [Fintype I] [Fintype C]

private theorem retained_bank (b : Bank) (archive out : Memory W) (floor : ℕ)
    (low : b.base+b.size≤floor) (keep : ∀x<floor,out x=archive x) (j : Word W) :
    b.read out j=b.read archive j := by
  exact keep _ ((Nat.add_lt_add_left (Nat.mod_lt j.val (Nat.two_pow_pos b.bits)) _).trans_le low)

omit [Fintype I] [Fintype C] in
theorem after_last (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (calendar : Mesh) (compile : Event→List PaidWidths.Slice) (L : PrefixWidths.Layout edges)
    (lo : ℕ) (b : Banks) (archive m : Memory W) {paidSource : Memory W} (ci : I→ℕ) (cj : C→ℕ)
    (before : Directory b archive enum ci cj)
    (low : ∀cell∈[b.index,b.kind,b.stock,b.reserved,b.used],cell.base+cell.size≤L.archive)
    (kept : ∀x<L.archive,m x=archive x)
    (paid : ∀i : Fin edges,(m ((L.bank (events calendar).length).base+i.val)).val=
      PaidWidths.total ((events calendar).flatMap compile) paidSource i)
    (inputs : ∀cell∈[L.bank (events calendar).length,b.index,b.kind,b.stock,b.reserved,b.used],cell.Fits W lo)
    (room : endAt lo (edges+r) edges<2^W) (wide : 2<2^W)
    (budget : ∀j,actual b.used archive (cj j)≤actual b.reserved archive (cj j))
    (p : Procedure W) (raw : Memory W) (ticks : ℕ) (ran : p.Exec raw m ticks) :
    let n:=edges+r
    let fixed:=fun i : Fin edges=>PaidWidths.total ((events calendar).flatMap compile) paidSource i
    let widths:=B.nativeWidth enum fixed (fun i=>actual b.stock archive (ci i)) (fun j=>actual b.reserved archive (cj j))
      (fun j=>actual b.used archive (cj j))
    ∃ out,(p.seq (procedure W lo edges r b (L.bank (events calendar).length))).Exec raw out
      (ticks+(66+539*n+6*edges)) ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word W)) ∧
      (∀a<lo,out a=m a) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word W)) ∧
      ∀i : Fin n,out ((weight lo n).base+i.val)=(widths i:Word W) := by
  intro n fixed widths
  let last:=(events calendar).length
  have reads (cell : Bank) (member : cell∈[b.index,b.kind,b.stock,b.reserved,b.used]) (j : Word W) :
      cell.read m j=cell.read archive j := retained_bank cell archive m L.archive (low cell member) kept j
  have dir : Directory b m enum ci cj := ⟨fun i=>(reads _ (by simp) _).trans (before.headKind i),
    fun i=>(reads _ (by simp) _).trans (before.headIndex i),fun i=>(reads _ (by simp) _).trans (before.tailKind i),
    fun i=>(reads _ (by simp) _).trans (before.tailIndex i)⟩
  have amounts (cell : Bank) (mem : cell∈[b.index,b.kind,b.stock,b.reserved,b.used]) :
      actual cell m=actual cell archive := funext fun i=>congrArg Fin.val (reads cell mem (i:Word W))
  have stock:=amounts b.stock (by simp)
  have res:=amounts b.reserved (by simp)
  have used:=amounts b.used (by simp)
  have fixedRead (i : Fin edges) : (m ((L.bank last).base+i.val)).val=fixed i := by
    exact paid i
  have cap:=inputs (L.bank last) (by simp only [last,List.mem_cons_self])
  have bound : edges≤2^W := L.covered.trans cap.2.1.le
  obtain ⟨out,run,starts,frame,keys,weights⟩:=ProtocolRAMTurnReplayed.run B enum lo b (L.bank last) m ci cj fixed
    dir L.covered bound fixedRead inputs room wide (fun j=>by rw [used,res];exact budget j)
  have exactTime : time lo edges r b (L.bank last)=66+539*n+6*edges :=
    ProtocolRAMTurnPaidCost.rank_clock ..
  rw [exactTime] at run
  rw [stock,res,used] at starts weights
  exact ⟨out,Procedure.Exec.then ran run,starts,frame,keys,weights⟩

omit [Fintype I] [Fintype C] in
theorem after_replay (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (calendar : Mesh) (compile : Event→List PaidWidths.Slice) (L : PrefixWidths.Layout edges)
    (lo : ℕ) (b : Banks) (archive m : Memory W) {paidSource : Memory W} (ci : I→ℕ) (cj : C→ℕ)
    (before : Directory b archive enum ci cj)
    (low : ∀cell∈[b.index,b.kind,b.stock,b.reserved,b.used],cell.base+cell.size≤L.archive)
    (kept : ∀x<L.archive,m x=archive x)
    (paid : ∀j≤(events calendar).length,∀i : Fin edges, (m ((L.bank j).base+i.val)).val=
      PaidWidths.total (PrefixWidths.prefixRows (events calendar) compile j) paidSource i)
    (inputs : ∀cell∈[L.bank (events calendar).length,b.index,b.kind,b.stock,b.reserved,b.used],cell.Fits W lo)
    (room : endAt lo (edges+r) edges<2^W) (wide : 2<2^W)
    (budget : ∀j,actual b.used archive (cj j)≤actual b.reserved archive (cj j))
    (p : Procedure W) (raw : Memory W) (ticks : ℕ) (ran : p.Exec raw m ticks) :
    let n:=edges+r
    let fixed:=fun i : Fin edges=>PaidWidths.total ((events calendar).flatMap compile) paidSource i
    let widths:=B.nativeWidth enum fixed (fun i=>actual b.stock archive (ci i)) (fun j=>actual b.reserved archive (cj j))
      (fun j=>actual b.used archive (cj j))
    ∃ out,(p.seq (procedure W lo edges r b (L.bank (events calendar).length))).Exec raw out
      (ticks+(66+539*n+6*edges)) ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word W)) ∧
      (∀a<lo,out a=m a) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word W)) ∧
      ∀i : Fin n,out ((weight lo n).base+i.val)=(widths i:Word W) := by
  apply after_last B enum calendar compile L lo b archive m ci cj before low kept _ inputs room wide budget p raw ticks ran
  intro i
  simpa only [PrefixWidths.prefixRows,List.take_length] using paid (events calendar).length le_rfl i

end Hierarchy.ProtocolRAMTurnReplayed
end

end OAI
