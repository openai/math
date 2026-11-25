import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentColonySplitRAM

namespace OAI
/-! # Monotone short donor ranks from the actual four-hop endpoint column -/
namespace Hierarchy.DescentHaloWalkRAM.Ranks
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentColonies.SplitRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {H P w : ℕ}

def earlier (endpoint : Fin H→Fin P→ℕ) (v : Fin H) (rack : ℕ) := (Finset.univ.filter (fun j=>endpoint v j<rack)).card

theorem strict (endpoint : Fin H→Fin P→ℕ) (v : Fin H) {x y : ℕ} (reachable : ∃i,endpoint v i=x) (comp : x<y) :
    earlier endpoint v x<earlier endpoint v y :=by
  obtain ⟨j,reachable⟩:=reachable;apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (show Finset.univ.filter (fun i=>endpoint v i<x)⊆ Finset.univ.filter (fun i=>endpoint v i<y) from
    fun i fresh=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp fresh).2.trans comp⟩)).2
  exact ⟨j,by simp [reachable,comp],by simp [reachable]⟩

theorem bound (endpoint : Fin H→Fin P→ℕ) (v : Fin H) (p : Fin P) : earlier endpoint v (endpoint v p)<P :=by
  have live : Finset.univ.filter (fun j=>endpoint v j<endpoint v p) ⊂ Finset.univ :=by
    exact (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2 ⟨p,Finset.mem_univ _,by simp⟩
  simpa [earlier] using Finset.card_lt_card live

theorem compare (endpoint : Fin H→Fin P→ℕ) (v : Fin H) (p q : Fin P) :
    earlier endpoint v (endpoint v p)<earlier endpoint v (endpoint v q) ↔ endpoint v p<endpoint v q :=by
  rcases lt_trichotomy (endpoint v p) (endpoint v q) with l|e|r
  · exact iff_of_true (strict endpoint v ⟨p,rfl⟩ l) l
  · simp [e]
  · exact iff_of_false (not_lt.mpr (strict endpoint v ⟨q,rfl⟩ r).le) (not_lt.mpr r.le)

structure Columns where
  endpoints : Bank
  start : Bank

def id (v : Fin H) (p : Fin P) : Fin (H*P):=finProdFinEquiv (v,p)

structure Fits (C : Columns) (out H P w : ℕ) : Prop where
  endpoints : C.endpoints.Fits w out
  start : C.start.Fits w out
  sizeEnd : H*P≤C.endpoints.size
  sizeStart : H*P≤C.start.size
  output : out+H*P<2^w

structure Reads (C : Columns) (endpoint : Fin H→Fin P→ℕ) (m : Memory w) : Prop where
  endpoints : ∀v p,m (C.endpoints.base+(v.val*P+p.val))=(endpoint v p:Word w)
  start : ∀(v:Fin H)(p:Fin P),m (C.start.base+(id v p).val)=((v.val*P:ℕ):Word w)
  addressBound : ∀v p,endpoint v p<2^w

def term (C : Columns) (j : Fin P) : Expr :=
  .branch .lt (.lookup C.endpoints (.op .add (.lookup C.start .row) (.lit j.val))) (.lookup C.endpoints .row) (.lit 1) (.lit 0)

def body (C : Columns) (P : ℕ) := total (term C) (List.finRange P)

private theorem bank_at (b : Bank) {out i : ℕ} (ok : b.Fits w out) (hi : i<b.size) (m : Memory w) :
    b.read m (i:Word w)=m (b.base+i) :=by simp [Bank.read,Fin.val_cast_of_lt (hi.trans ok.2.1),Nat.mod_eq_of_lt hi]

private theorem eval_total {α : Type} (f : α→Expr) (a : α→ℕ) (m : Memory w) (r : Word w)
    (ok : ∀i,(f i).eval m r=(a i:Word w)) (xs : List α) :
    (total f xs).eval m r=((xs.map a).sum:Word w) :=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ok,ih]

theorem body_at (C : Columns) (out : ℕ) (room : Fits C out H P w) (endpoint : Fin H→Fin P→ℕ)
    (m : Memory w) (data : Reads C endpoint m) (v : Fin H) (p : Fin P):
    (body C P).eval m ((id v p).val:Word w)=(earlier endpoint v (endpoint v p):Word w):=by
  let val (j : Fin P):=if endpoint v j<endpoint v p then 1 else 0
  have first : (id v p).val=v.val*P+p.val:=by simp [id,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have atTerm (j : Fin P) : (term C j).eval m ((id v p).val:Word w)=(val j:Word w):=by
    have size : v.val*P+j.val<C.endpoints.size:=by have h:=(id v j).isLt;simpa [id,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using h.trans_le room.sizeEnd
    have old : C.start.read m ((id v p).val:Word w)=((v.val*P:ℕ):Word w):=
      (bank_at C.start room.start ((id v p).isLt.trans_le room.sizeStart) m).trans (data.start v p)
    have left : C.endpoints.read m (((v.val*P:ℕ):Word w)+(j.val:Word w))=(endpoint v j:Word w):=by
      rw [←Nat.cast_add];exact (bank_at C.endpoints room.endpoints size m).trans (data.endpoints v j)
    have right : C.endpoints.read m ((id v p).val:Word w)=(endpoint v p:Word w):=by
      rw [bank_at C.endpoints room.endpoints ((id v p).isLt.trans_le room.sizeEnd),first];exact data.endpoints v p
    simp only [Nat.cast_mul] at left
    have comp : (endpoint v j : Word w) < (endpoint v p : Word w) ↔ endpoint v j < endpoint v p := by
      change ((endpoint v j : Word w)).val < ((endpoint v p : Word w)).val ↔ _
      rw [Fin.val_cast_of_lt (data.addressBound v j),Fin.val_cast_of_lt (data.addressBound v p)]
    by_cases less : endpoint v j<endpoint v p <;>
      simp [term,Expr.eval,RowOp.opcode,BinaryOp.eval,DescriptorExpr.Comparison.test,old,left,right,comp,less,val]
  rw [body,eval_total _ val m _ atTerm,←List.ofFn_eq_map,List.sum_ofFn]
  have sum : ∑j,val j=earlier endpoint v (endpoint v p):=by simp [val,earlier]
  rw [sum]

theorem body_fits (C : Columns) (out : ℕ) (room : Fits C out H P w) : (body C P).Fits w out :=
  fits_total (term C : Fin P→Expr) (fun _=>⟨⟨room.endpoints,⟨⟨room.start,trivial⟩,trivial⟩⟩,⟨room.endpoints,trivial⟩,trivial,trivial⟩) _

theorem body_work (C : Columns) (P : ℕ) : (body C P).work≤1+P*32:=by
  have top:=work_total (term C) 31 (fun i=>by simp [term,Expr.work]) (List.finRange P)
  simpa [body] using top

theorem run (C : Columns) (out : ℕ) (room : Fits C out H P w) (endpoint : Fin H→Fin P→ℕ)
    (m : Memory w) (data : Reads C endpoint m) :
    let result:=image out (H*P) (body C P) m
    (scan w out (H*P) (body C P)).Exec m result (4+H*P*(2*(body C P).work+4)) ∧
    (∀v p,result (out+(id v p).val)=(earlier endpoint v (endpoint v p):Word w)) ∧
    CheapCode (scan w out (H*P) (body C P)) :=by
  intro result
  exact ⟨scan_exec _ _ _ _ (body_fits C out room) room.output,
    fun v p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (id v p)).trans (body_at C out room endpoint m data v p),by apply scan_cheap⟩

end
end Hierarchy.DescentHaloWalkRAM.Ranks

end OAI
