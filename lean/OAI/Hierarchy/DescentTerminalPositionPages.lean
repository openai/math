import OAI.Hierarchy.DescentTerminalPositionAlphabet
import OAI.Hierarchy.DescentTerminalSiteShelfWords
import OAI.Hierarchy.DescentTerminalVertexWord

namespace OAI
/-! # Direct read of the contributing vertex records from their genuine stored bit ranges -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentTerminalDenseWindow (dense)
open Computability.VPVNP.BurstRAM (Word)
open Computability.VPVNP.RAMSerialization (wordBits)
open scoped Classical
noncomputable section
variable {q t H N A w V B ℓ W : ℕ}
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
local notation "R" => rowRange q t H N A w

def page (n : Fin (V+1)) (ℓ : ℕ) (skip : Fin B) (lo hi : Word B) : Raw :=
  ⟨n,fun v=>
    let x:=vertex ℓ skip lo hi v.val
    if h : x.val<R then loadRow ⟨x.val,h⟩ else (0,DescentTerminalScalarHeader.emptyBook q t H N A w)⟩

/-- Physical upstream bank assertion only on the little-endian chronological
per-vertex fields. It gives neither their packed neighbor word nor the scalar request. -/
def Texture (z : Raw) (start ℓ : ℕ) (stream : ℕ→Bool) : Prop :=
  ∀v : Fin z.1.val,∀j : Fin ℓ,stream (start+(v.val*ℓ+j.val))=(storeRow (z.2 v)).val.testBit j.val

theorem page_read (z : Raw) (start : ℕ) (stream : ℕ→Bool) (bp : 0<B) (short : R≤2^ℓ)
    (occupied : z.1.val*ℓ≤B) (tex : Texture z start ℓ stream) :
    page z.1 ℓ ⟨start%B,Nat.mod_lt _ bp⟩ (dense B stream (start/B)) (dense B stream (start/B+1))=z := by
  rcases z with ⟨n,records⟩
  unfold page
  apply congrArg (Sigma.mk n)
  funext v
  let book:=storeRow (records v)
  have small : book.val<2^ℓ:=book.isLt.trans_le short
  have room := (Nat.mul_le_mul_right ℓ v.isLt).trans occupied
  have eqn : vertex ℓ ⟨start%B,Nat.mod_lt _ bp⟩ (dense B stream (start/B)) (dense B stream (start/B+1)) v.val=
      (⟨book.val,small⟩:Word ℓ) := by
    apply (wordBits _).injective
    funext j
    exact (vertex_dense_at ℓ start v.val stream bp room j).trans
      ((tex v j).trans (Computability.VPVNP.LiveHeader.testBit_wordBits (⟨book.val,small⟩:Word ℓ) j))
  dsimp only
  rw [eqn]
  simp only [dite_eq_left book.isLt]
  exact row_back (records v)

def index (n : Fin (V+1)) (which : Fin (W+1)) (skip : Fin B) (lo hi : Word B) : Fin (alphabet V W B) :=
  finProdFinEquiv (n,finProdFinEquiv (which,finProdFinEquiv (skip,finProdFinEquiv (lo,hi))))

def pageBy (decode : Word ℓ→DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w))
    (n : Fin (V+1)) (skip : Fin B) (lo hi : Word B) : Raw :=
  ⟨n,fun v=>decode (vertex ℓ skip lo hi v.val)⟩

def entryBy (decode : Word ℓ→DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w))
    (qp : 0<q) (key : Fin (alphabet V W B)) : ℕ :=
  let a:=finProdFinEquiv.symm key
  let c:=finProdFinEquiv.symm a.2
  let u:=finProdFinEquiv.symm c.2
  let x:=finProdFinEquiv.symm u.2
  DescentTerminalLeafFold.code (selectMode (pageBy decode a.1 u.1 x.1 x.2) qp c.1)

theorem entryBy_read (decode : Word ℓ→DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w))
    (z : Raw) (start : ℕ) (stream : ℕ→Bool) (bp : 0<B)
    (words : ∀v : Fin z.1.val,decode (vertex ℓ ⟨start%B,Nat.mod_lt _ bp⟩ (dense B stream (start/B))
      (dense B stream (start/B+1)) v.val)=z.2 v) (qp : 0<q) (which : Fin (W+1)) :
    entryBy decode qp (index z.1 which ⟨start%B,Nat.mod_lt _ bp⟩ (dense B stream (start/B)) (dense B stream (start/B+1)))=
      DescentTerminalLeafFold.code (selectMode z qp which) := by
  have eqn : pageBy decode z.1 ⟨start%B,Nat.mod_lt _ bp⟩ (dense B stream (start/B)) (dense B stream (start/B+1))=z := by
    rcases z with ⟨n,records⟩
    exact congrArg (Sigma.mk n) (funext words)
  simp only [entryBy,index,Equiv.symm_apply_apply,eqn]

theorem entryBy_blank (decode : Word ℓ→DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w))
    (qp : 0<q) (n : Fin (V+1)) (skip : Fin B) (lo hi : Word B) :
    entryBy decode qp (index n (0:Fin (W+1)) skip lo hi)=0 := by simp [entryBy,index,selectMode,DescentTerminalLeafFold.code]

def entry (qp : 0<q) (ℓ : ℕ) (key : Fin (alphabet V W B)) : ℕ :=
  let a:=finProdFinEquiv.symm key
  let c:=finProdFinEquiv.symm a.2
  let u:=finProdFinEquiv.symm c.2
  let x:=finProdFinEquiv.symm u.2
  DescentTerminalLeafFold.code (selectMode (page a.1 ℓ u.1 x.1 x.2 : Raw) qp c.1)

theorem entry_read (z : Raw) (start : ℕ) (stream : ℕ→Bool) (bp : 0<B) (short : R≤2^ℓ)
    (occupied : z.1.val*ℓ≤B) (tex : Texture z start ℓ stream) (qp : 0<q) (which : Fin (W+1)) :
    entry (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) qp ℓ (index z.1 which ⟨start%B,Nat.mod_lt _ bp⟩
      (dense B stream (start/B)) (dense B stream (start/B+1)))=DescentTerminalLeafFold.code (selectMode z qp which) := by
  simp only [entry,index,Equiv.symm_apply_apply,page_read z start stream bp short occupied tex]

theorem entry_blank (qp : 0<q) (n : Fin (V+1)) (skip : Fin B) (lo hi : Word B) :
    entry (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) qp ℓ (index n (0:Fin (W+1)) skip lo hi)=0 := by
  simp [entry,index,selectMode,DescentTerminalLeafFold.code]

end
end Hierarchy.DescentTerminalSiteShelves

end OAI
