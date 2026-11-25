import OAI.Hierarchy.DescentTerminalMaskPage
import OAI.Hierarchy.DescentTerminalReachedPanels

namespace OAI
/-! # Direct native per-host issue from the true sparse group-and-block fields -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalRecipeRows
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V groups blocks S B bits W n stop : ℕ}
local notation "width" => span q t H N A w
local notation "size" => channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) (blocks:=blocks)
local notation "Inputs" => BlockFields q t H N A w groups blocks
local notation "capacity" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) (blocks:=blocks)
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

def weightAt (j : Fin (channels blocks)) := ∏k:Fin j.val,2^(size (k.castLE j.isLt.le))

def maskTerm (L : MaskedShelf blocks) (f : Fin (channels blocks)) : Expr := .lookup (L.weight f) (.lookup (L.channel f) .row)
def maskedRow (L : MaskedShelf blocks) : Expr := .lookup L.table (sumExpr (maskTerm L) (List.finRange (channels blocks)))
def guardedMask (L : MaskedShelf blocks) (S : ℕ) : Expr := .branch .lt .row (.lit S) (maskedRow L) (.lit 0)

theorem sum_work (rs : List (Fin (channels blocks))) (L : MaskedShelf blocks) :
    (sumExpr (maskTerm L) rs).work=1+13*rs.length := by
  induction rs with
  | nil=>rfl
  | cons j l ih=>simp [sumExpr,maskTerm,Expr.work,ih];omega

theorem masked_work (L : MaskedShelf blocks) : (guardedMask L S).work=11+117*blocks := by
  have total := sum_work (List.finRange (channels blocks)) L
  simp only [List.length_finRange] at total
  simp only [guardedMask,maskedRow,Expr.work]
  rw [total]
  unfold channels
  omega

def dictionary (fit : V*width≤B) (j : Fin capacity) := homePage fit (finPiFinEquiv.symm j : Inputs)

structure MountedMask (L : MaskedShelf blocks) (mem : Memory bits) (fit : V*width≤B) : Prop where
  shift : ∀f,∀z:Word bits,(L.weight f).read mem z=
    (((z.val%2^(size f))*weightAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) f:ℕ):Word bits)
  menu : ∀j:Fin capacity,L.table.read mem (j.val:Word bits)=((dictionary fit j).val:Word bits)

theorem mask_index_eval (L : MaskedShelf blocks) (m : Memory bits)
    (shift : ∀f,∀z:Word bits,(L.weight f).read m z=
      (((z.val%2^(size f))*weightAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) f:ℕ):Word bits))
    (i : Fin S) :
    (sumExpr (maskTerm L) (List.finRange (channels blocks))).eval m (i.val:Word bits)=
      ((finPiFinEquiv (measured L m (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) i)).val:Word bits) := by
  let data:Inputs:=measured L m i
  let value:=fun f : Fin (channels blocks)=>(data f).val*weightAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) f
  have digits (f : Fin (channels blocks)) : (maskTerm L f).eval m (i.val:Word bits)=(value f:Word bits) := by
    simp [maskTerm,Expr.eval,shift,value,data,measured,Fin.val_natCast]
  have key : ((List.finRange (channels blocks)).map value).sum=(finPiFinEquiv data).val := by
    rw [finPiFinEquiv_apply]
    simp only [List.finRange,List.map_ofFn,List.sum_ofFn]; rfl
  simp only [sum_read _ _ _ _ digits,key,data]

theorem masked_eval (L : MaskedShelf blocks) (m : Memory bits) (fit : V*width≤B) (src : MountedMask L m (groups:=groups) fit) (i : Fin S) :
    (maskedRow L).eval m (i.val:Word bits)=((homePage fit (measured L m (groups:=groups) i)).val:Word bits) := by
  simp only [maskedRow,Expr.eval,mask_index_eval L m src.shift i]
  have loaded := src.menu (finPiFinEquiv (measured L m (groups:=groups) i))
  simpa only [dictionary,Equiv.symm_apply_apply] using loaded

def maskedMem (L : MaskedShelf blocks) (D : Directory) (S : ℕ) (m : Memory bits) :=
  image D.texture.base (S+1) (guardedMask L S) m

theorem mask_run (L : MaskedShelf blocks) (D : Directory) (m : Memory bits) (fit : (guardedMask L S).Fits bits D.texture.base)
    (endAt : D.texture.base+(S+1)<2^bits) :
    (scan bits D.texture.base (S+1) (guardedMask L S)).Exec m (maskedMem L D S m) (4+(S+1)*(26+234*blocks)) ∧
      CheapCode (scan bits D.texture.base (S+1) (guardedMask L S)) := by
  have tariff : 4+(S+1)*(2*(guardedMask L S).work+4)=4+(S+1)*(26+234*blocks) := by
    rw [masked_work]
    ring
  refine ⟨?_,@scan_cheap bits D.texture.base (S+1) (guardedMask L S)⟩
  rw [←tariff]
  exact @scan_exec bits D.texture.base (S+1) (guardedMask L S) m fit endAt

theorem mask_directory (L : MaskedShelf blocks) (D : Directory) (m : Memory bits) (sites : Fin S→Site) (owns : ∀i,(sites i).rows q≤W)
    (books : Fin S→Raw) (fit : V*width≤B) (bp : 0<B) (shared : MountedMask L m (groups:=groups) fit)
    (header : Controls (B:=B) (n:=n) D m sites owns books) (endAt : D.texture.base+(S+1)<2^bits)
    (stored : D.texture.Fits bits stop) (room : S+1≤D.texture.size)
    (keep : ∀b∈[D.span.active,D.span.owner,D.span.localRow,D.ports,D.count,D.firstWord,D.skip,D.countShift,D.modeShift,
      D.skipShift,D.wordShift],b.Fits bits D.texture.base) :
    Reached (pool:=n) D (maskedMem L D S m) sites owns books (fun i=>i.val*B)
      (bitsAt (fun i : Fin S=>homePage fit (measured L m (groups:=groups) i)) bp) bp :=
  reached_expr (maskedRow L) D m sites owns books _ bp (masked_eval L m fit shared) header endAt stored room keep

end
end Hierarchy.DescentTerminalVertexFields

end OAI
