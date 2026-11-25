import OAI.Hierarchy.DescentTerminalRouteRows
import OAI.Hierarchy.DescentTerminalRouteLedger
import OAI.Hierarchy.DescentTerminalScanFacts
import OAI.Hierarchy.DescentTerminalHeaderPrefixAny

namespace OAI
/-! # Two fixed native scans publish the true per-bin route dictionary selector -/
namespace Hierarchy.DescentTerminalRouteIssue
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRouteRows DescentTerminalRouteLedger
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w K W q a : ℕ}
local notation "c" => rowBits q a
local notation "B" => W*c

structure Layout where
  names : Bank
  offset : Bank
  phase : Bank
  update : Bank
  lastRow : Bank
  decode : Bank
  progress : Bank
  gate : Bank

def row (L : Layout) : Expr := .op .add (.lookup L.offset (.lookup L.names .row)) (.lookup L.phase .row)
def project (L : Layout) : Expr := .lookup L.decode (.lookup L.progress (.lookup L.lastRow .row))
def program (L : Layout) (w n : ℕ) := (DescentTerminalHeaderPrefixRAM.program w L.progress.base n (.read L.update) (row L)).seq
  (scan w L.gate.base (3*n) (project L))
def progress (L : Layout) (n : ℕ) (m : Memory w) :=
  DescentTerminalHeaderPrefixRAM.result L.progress.base n (.read L.update) (row L) m
def finalMem (L : Layout) (n : ℕ) (m : Memory w) := image L.gate.base (3*n) (project L) (progress L n m)

structure Fits (L : Layout) (w n : ℕ) : Prop where
  first : ∀b∈[L.names,L.offset,L.phase,L.update,L.lastRow,L.decode],b.Fits w L.progress.base
  middle : L.progress.Fits w L.gate.base
  size : n≤L.progress.size
  room : L.gate.base+3*n<2^w

def clocks (L : Layout) (n : ℕ) := (4+n*(2*DescentTerminalHeaderPrefixRAM.work (.read L.update) (row L)+4))+
  (4+(3*n)*(2*(project L).work+4))

theorem clocks_bound (L : Layout) (n : ℕ) : clocks L n ≤ 8+400*n := by
  dsimp [clocks,project,row,DescentTerminalHeaderPrefixRAM.work,Expr.work]
  omega

theorem run {extent : ℕ} (L : Layout) (fits : Fits L w extent) (m : Memory w) :
    (program L w extent).Exec m (finalMem L extent m) (clocks L extent) ∧ CheapCode (program L w extent) := by
  have f:=fits.first
  have low:=fits.middle.2.2;have cnt:=fits.size;have hi:=fits.room
  let p := DescentTerminalHeaderPrefixRAM.program w L.progress.base extent (.read L.update) (row L)
  let g := scan w L.gate.base (3*extent) (project L)
  have a : p.Exec m (progress L extent m)
      (4+extent*(2*DescentTerminalHeaderPrefixRAM.work (.read L.update) (row L)+4)) :=
    @DescentTerminalHeaderPrefixRAM.exec_any w L.progress.base extent (.read L.update) (row L) m
      (f L.update (by simp)) ⟨⟨f L.offset (by simp),f L.names (by simp),trivial⟩,f L.phase (by simp),trivial⟩ (by omega)
  have trans (b : Bank) (hx:b∈[L.names,L.offset,L.phase,L.update,L.lastRow,L.decode]) : b.Fits w L.gate.base :=
    DescentTerminalChipRuntime.bankMono (f _ hx) (by omega)
  have b : g.Exec (progress L extent m) (finalMem L extent m) (4+(3*extent)*(2*(project L).work+4)) :=
    @scan_exec w L.gate.base (3*extent) (project L) (progress L extent m)
      ⟨trans L.decode (by simp),fits.middle,trans L.lastRow (by simp),trivial⟩ hi
  exact ⟨@Procedure.Exec.then w p g m (progress L extent m) (finalMem L extent m) _ _ a b,
    @cheap_seq w p g
      (@DescentTerminalHeaderPrefixRAM.cheap w L.progress.base extent (.read L.update) (row L))
      (@scan_cheap w L.gate.base (3*extent) (project L))⟩

local notation "n" => K*W

structure Reads (L : Layout) (rows : Fin n→Row q a) (m : Memory w) : Prop where
  names : ∀i:Fin n,L.names.read m (i.val:Word w)=((pack (rows i)).val:Word w)
  offset : ∀s:Word c,L.offset.read m (s.val:Word w)=((2^B*s.val:ℕ):Word w)
  phase : ∀i:Fin n,L.phase.read m (i.val:Word w)=((2^B*(2^c*(finProdFinEquiv.symm i : Fin K×Fin W).2.val):ℕ):Word w)
  update : ∀s:Fin (radix W c),L.update.read m (s.val:Word w)=((stepROM s).val:Word w)
  lastRow : ∀i:Fin n,L.lastRow.read m ((3*i.val:ℕ):Word w)=
    ((((finProdFinEquiv.symm i : Fin K×Fin W).1.val*W+W-1:ℕ)):Word w)
  decode : ∀s:Word B,L.decode.read m (s.val:Word w)=((lookup (W:=W) (q:=q) (a:=a) s).val:Word w)

theorem «prefix» (L : Layout) (rows : Fin n→Row q a) (m : Memory w) (_fits : Fits L w n) (input : Reads L rows m) :
    ∀i:Fin n,progress L n m (L.progress.base+i.val)=((history (pack ∘ rows) (i.val+1)).val:Word w) := by
  let desired := fun t:ℕ=>((history (pack ∘ rows) t).val:Word w)
  have step : ∀i:Fin n,DescentTerminalHeaderPrefixRAM.value (.read L.update) m (desired i.val)
      ((row L).eval m (i.val:Word w))=desired (i.val+1) := by
    intro i
    let t:=history (pack ∘ rows) i.val
    let s:=pack (rows i)
    let slot:Fin W:=(finProdFinEquiv.symm i : Fin K×Fin W).2
    have readRow : (row L).eval m (i.val:Word w)=((2^B*s.val+2^B*(2^c*slot.val):ℕ):Word w) := by
      change L.offset.read m (L.names.read m (i.val:Word w)) + L.phase.read m (i.val:Word w) = _
      rw [input.names i,input.offset,input.phase i,Nat.cast_add]
    have addr : (desired i.val+(row L).eval m (i.val:Word w))=((key slot t s).val:Word w) := by
      rw [key_val,readRow]
      change (t.val:Word w)+_ = _
      rw [←Nat.cast_add]
      apply congrArg (fun u : ℕ => (u : Word w))
      ring
    change L.update.read m (desired i.val+(row L).eval m (i.val:Word w))=_
    rw [addr,input.update (key slot t s),step_at slot t s]
    change _ = ((history (pack ∘ rows) (i.val+1)).val:Word w)
    rw [history,dite_eq_left i.isLt]
    simp only [slot,t,s,Fin.eta,Function.comp_apply]
  have reached (j : ℕ) (bound : j≤n) :
      DescentTerminalHeaderPrefixRAM.stateOn (.read L.update) (row L) m j=desired j := by
    induction j with
    | zero => simp [desired,history,DescentTerminalHeaderPrefixRAM.stateOn]
    | succ j ih =>
      change DescentTerminalHeaderPrefixRAM.value (.read L.update) m
        (DescentTerminalHeaderPrefixRAM.stateOn (.read L.update) (row L) m j)
        ((row L).eval m (j:Word w)) = desired (j+1)
      rw [ih (Nat.le_of_lt bound)]
      exact step ⟨j,bound⟩
  intro i
  exact (DescentTerminalHeaderPrefixRAM.at_row L.progress.base
    (DescentTerminalHeaderPrefixRAM.stateOn (.read L.update) (row L) m) m i).trans
    (reached (i.val+1) i.isLt)

theorem read (L : Layout) (pos : 0<W) (rows : Fin n→Row q a) (m : Memory w) (fits : Fits L w n)
    (input : Reads L rows m) (i : Fin n) :
    finalMem L n m (L.gate.base+3*i.val)=
      ((lookup (W:=W) (q:=q) (a:=a) (packBin (fun j=>pack (rows (finProdFinEquiv ((finProdFinEquiv.symm i : Fin K×Fin W).1,j)))))).val:Word w) := by
  let b:Fin K:=(finProdFinEquiv.symm i : Fin K×Fin W).1
  let s:Fin W:=⟨W-1,by omega⟩
  let last:Fin n:=finProdFinEquiv (b,s)
  have lv : last.val=b.val*W+W-1 := by change W-1+W*b.val=_;rw [Nat.mul_comm];omega
  have stay (bank : Bank) (valid : bank∈[L.names,L.offset,L.phase,L.update,L.lastRow,L.decode]) (x : Word w) :
      bank.read (progress L n m) x=bank.read m x := by
    have bound:=(fits.first bank valid).2.2
    have low:=Nat.mod_lt x.val (fits.first bank valid).1
    simp [Bank.read,progress,DescentTerminalHeaderPrefixRAM.result,fillSegment,
      not_le.mpr (show bank.base+x.val%bank.size<L.progress.base by omega)]
  have cap:=last.isLt.trans_le fits.size
  have endStep : last.val+1=b.val*W+W:=by omega
  let packed := packBin (fun lane : Fin W => pack (rows (finProdFinEquiv (b,lane))))
  have lastRead : L.lastRow.read (progress L n m) ((3*i.val:ℕ):Word w)=(last.val:Word w) := by
    rw [stay L.lastRow (by simp),input.lastRow i,lv]
  have progressRead : L.progress.read (progress L n m) (last.val:Word w)=(packed.val:Word w) := by
    rw [Bank.read,Fin.val_cast_of_lt (cap.trans fits.middle.2.1),Nat.mod_eq_of_lt cap,
      «prefix» L rows m fits input last,endStep,at_end (pack ∘ rows) b]
    simp only [packed,Function.comp_apply]
  let j:Fin (3*n):=⟨3*i.val,by have:=i.isLt;omega⟩
  change image L.gate.base (3*n) (project L) (progress L n m) (L.gate.base+j.val) =
    ((lookup (q:=q) (a:=a) packed).val:Word w)
  rw [DescentTerminalChipRuntime.image_at (progress L n m) L.gate.base (3*n) (project L) j]
  change L.decode.read (progress L n m)
    (L.progress.read (progress L n m) (L.lastRow.read (progress L n m) ((3*i.val:ℕ):Word w))) = _
  rw [lastRead,progressRead,stay L.decode (by simp),input.decode packed]

end
end Hierarchy.DescentTerminalRouteIssue

end OAI
