import OAI.Hierarchy.DescentTerminalRecordPadding
import OAI.Hierarchy.DescentTerminalVertexPanelRAM

namespace OAI
/-! # Clearing inactive private widths and argument slots in the shared panel lookup -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalPrintedFields
open DescentTerminalScalarHeader DescentTerminalChronologicalBooks DescentTerminalLeafDigits DescentKernelHistory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V S B : ℕ}
local notation "K" => Key H N A
local notation "width" => span q t H N A w
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
local notation "Vertex" => DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)

def raw (s : Rows) (v : Fin V) (k : K) :=
  ((wordBits (bits q t H N A w k)).symm (fun j=>wordBits _ (s (group k)) (locate v k j))).val

def clean (x : K→ℕ) (k : K) := if allows x k then x k else 0

theorem allows_congr (x y : K→ℕ) (live : ∀k,allows y k→x k=y k) (k : K) : allows x k↔allows y k := by
  have hc:=live hiddenCount trivial
  have nc:=live nodeCount trivial
  rcases k with _|(_|(_|(_|(a|(b|(c|d))))))
  all_goals try exact Iff.rfl
  · simp [allows,hc]
  · simp [allows,nc]
  · simp [allows,nc]
  · by_cases node : d.2.1.val<y nodeCount
    · have arity:=live (nodeArity d.2.1) node
      simp [allows,nc,arity]
    · simp [allows,nc,node]

def clippedPage (s : Rows) (_fit : V*width≤B) : Computability.VPVNP.BurstRAM.Word B :=
  (wordBits _).symm fun i=>
    if hi:i.val<V*width then
      let vb:Fin V×Fin width:=finProdFinEquiv.symm ⟨i.val,hi⟩
      let z:=slotOrder.symm vb.2
      (clean (raw s vb.1) z.1).testBit z.2.val
    else false

theorem clipped_read (s : Rows) (fit : V*width≤B) (v : Fin V) (k : K) (j : Fin (bits q t H N A w k)) :
    wordBits B (clippedPage s fit) ((finProdFinEquiv (v,offset k j)).castLE fit)=(clean (raw s v) k).testBit j.val := by
  let z : (i : K)×Fin (bits q t H N A w i):=⟨k,j⟩
  let E : ((i : K) × Fin (bits q t H N A w i)) ≃ Fin width := slotOrder
  let readAt (r : (i : K) × Fin (bits q t H N A w i)) :=
    (clean (raw s v) r.1).testBit r.2.val
  have addr : offset k j=E z := rfl
  simp only [clippedPage,Equiv.apply_symm_apply,Fin.val_castLE,
    (finProdFinEquiv (v,offset k j)).isLt,dite_eq_left]
  change (let slot := slotOrder.symm ((finProdFinEquiv.symm (finProdFinEquiv (v,offset k j))).2)
    ; (clean (raw s (finProdFinEquiv.symm (finProdFinEquiv (v,offset k j))).1) slot.1).testBit slot.2.val) = _
  rw [Equiv.symm_apply_apply,addr]
  change readAt (E.symm (E z)) = readAt z
  rw [E.symm_apply_apply z]

theorem clean_read (z : Vertex) (s : Rows) (v : Fin V) (zero : Zeros z)
    (issued : ∀k,allows (fun j=>(value z j).val) k→ raw s v k=(value z k).val) (k : K) :
    clean (raw s v) k=(value z k).val := by
  unfold clean
  by_cases ok : allows (fun j=>(value z j).val) k
  · rw [ite_eq_left ((allows_congr _ _ issued k).mpr ok)]
    exact issued _ ok
  · rw [ite_eq_right (fun yes=>ok ((allows_congr _ _ issued k).mp yes))]
    exact (zero _ ok).symm

theorem clipped_source (books : Fin S→Raw) (s : Fin S→Rows) (fit : V*width≤B) (bp : 0<B)
    (zero : ∀i v,Zeros ((books i).2 v)) (issued : ∀i (v : Fin (books i).1.val) k,
      allows (fun a=>(value ((books i).2 v) a).val) k→ raw (s i) (v.castLE (Nat.le_of_lt_succ (books i).1.isLt)) k=(value ((books i).2 v) k).val) (i : Fin S) :
    Source (books i) (i.val*B) (bitsAt (fun a=>clippedPage (s a) fit) bp) := by
  intro v k j
  let v0:=v.castLE (Nat.le_of_lt_succ (books i).1.isLt)
  let b:=finProdFinEquiv (v0,offset k j)
  have ordinal : b.val=v.val*width+(offset k j).val := by change (offset k j).val+width*v.val=_;ring
  let page (a : Fin S) := clippedPage (s a) fit
  have atPage := congrArg (fun x : Computability.VPVNP.BurstRAM.Word B => wordBits B x (b.castLE fit)) (dense_page page bp i.val)
  have read : bitsAt page bp (i.val*B+b.val)=wordBits B (page i) (b.castLE fit) := by
    simpa only [DescentTerminalDenseWindow.dense,Equiv.apply_symm_apply,Fin.val_castLE,
      aligned,i.isLt,dite_eq_left,Fin.eta] using atPage
  change bitsAt page bp (i.val*B+(v.val*width+(offset k j).val))=_
  rw [←ordinal]
  exact read.trans ((clipped_read (s i) fit v0 k j).trans
    (congrArg (fun a : ℕ => a.testBit j.val) (clean_read _ _ v0 (zero i v) (issued i v) k)))

end
end Hierarchy.DescentTerminalVertexFields

end OAI
