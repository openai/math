import OAI.Hierarchy.ProtocolRAMCoreRouteDirectory
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Replaying the immutable core route at each early spill and boundary feed -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped BigOperators Classical Fin.CommRing
variable {z W k w R K attempts edges : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "Goods" => Commodity (Fin (2^z)) N k
local notation "A" => Actions N k

def evenPosition : Expr := .op .add .row .row

def oddPosition : Expr := .op .add evenPosition (.lit 1)

private theorem even_eval (m : Memory w) (i : ℕ) :
    evenPosition.eval m (i:Word w)=((2*i:ℕ):Word w) := by
  simp [evenPosition,Expr.eval,RowOp.opcode,BinaryOp.eval,two_mul]

private theorem odd_eval (m : Memory w) (i : ℕ) :
    oddPosition.eval m (i:Word w)=((2*i+1:ℕ):Word w) := by
  simp only [oddPosition,Expr.eval,RowOp.opcode,BinaryOp.eval,even_eval,Nat.cast_add,Nat.cast_one]

/-- The first part of the ordinary settlement recipe, with the previous stock
row in the adjacent odd word. It uses the same permutation-independent address
order at every repair and feed. -/
def earlyTraversal (p : Recipes) (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ)
    (o : Orders z (2^W) k) (owner parity : Bank) : Traversals :=
  ⟨∑j,arity (o.core.symm j),owner,parity,(indexWord p x S z W k attempts).atRow evenPosition,
    .lookup p.operand oddPosition,none⟩

private theorem ordinary_length (π : Equiv.Perm (Fin (2^z))) (place : Site z D k→Fin K)
    (B : Mount (S:=S) π place edges) (i : Goods) : arity i=(B.ordinary i).length := by
  cases i with
  | inl p => simp [arity,Mount.ordinary,commodityWalk,payload_length]
  | inr q => rcases q with ⟨⟨p,t⟩,l⟩; rfl

theorem earlyTraversal_reads (p : Recipes) (x : Source) (π : Equiv.Perm (Fin (2^z)))
    (place : Site z D k→Fin K) (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k)
    (o : Orders z D k) (physical : ∀e,(B.row e).val=(order.symm e).val) (m : Memory w)
    (data : Readable x S z W k attempts order π m) (cj : Columns z D×Fin k→ℕ)
    (rom : Installed p o (fun i=>(o.core i).val) cj m) (menu : Fintype.card A≤2^w)
    (rowFit : Fintype.card Goods≤2^w) (edgeFit : edges≤2^w) (owner parity : Bank) :
    (earlyTraversal p x S z W k attempts o owner parity).Reads m (fun j=>B.ordinary (o.core.symm j)) := by
  let idx := corePrefix o
  let layout : (Σ i : Goods,Fin (arity i)) ≃ (Σ j,Fin (B.ordinary (o.core.symm j)).length) :=
    Equiv.sigmaCongr o.core fun i=>finCongr (by
      rw [Equiv.symm_apply_apply]
      exact ordinary_length π place B i)
  have selected (v : Σ g : Goods,Fin (arity g)) :
      (idx.symm.trans layout) (idx v)=layout v :=
    congrArg layout (idx.symm_apply_apply v)
  have read_same (u v : List (Fin edges)) (same : u=v) (j : ℕ)
      (hu : j<u.length) (hv : j<v.length) : (u[j]'hu).val=(v[j]'hv).val := by
    cases same
    rfl
  refine ⟨idx.symm.trans layout,?_,?_⟩
  · intro j
    obtain ⟨⟨g,t⟩,rfl⟩ := idx.surjective j
    let v := (⟨g,t⟩ : Σ g : Goods,Fin (arity g))
    let pos := slotOrder o (.inl v)
    have coord : (idx v).val=pos.val := (corePrefix_val o v).symm
    have got := edge_word p x π place B order o physical m data _ cj rom menu pos
    have unrank : getSlot o pos=.inl v := (slotOrder o).symm_apply_apply (.inl v)
    rw [unrank] at got
    change (((indexWord p x S z W k attempts).atRow evenPosition).eval m ((idx v).val:Word w)).val=_
    rw [eval_atRow,even_eval,coord,got,Fin.val_cast_of_lt ((toOccurrence B (.inl v)).edge.isLt.trans_le edgeFit)]
    let readAt (u : Σ j,Fin (B.ordinary (o.core.symm j)).length) :=
      ((B.ordinary (o.core.symm u.1))[u.2.val]'u.2.isLt).val
    change _=readAt ((idx.symm.trans layout) (idx v))
    rw [selected v]
    exact read_same (B.ordinary g) (B.ordinary (o.core.symm (o.core g)))
      (congrArg B.ordinary (o.core.symm_apply_apply g)).symm t.val
      (t.isLt.trans_eq (ordinary_length π place B g)) (layout v).2.isLt
  · intro j
    obtain ⟨⟨g,t⟩,rfl⟩ := idx.surjective j
    let v := (⟨g,t⟩ : Σ g : Goods,Fin (arity g))
    let pos := slotOrder o (.inl v)
    have coord : (idx v).val=pos.val := (corePrefix_val o v).symm
    have got := (rom pos).2.2.2.2
    have unrank : getSlot o pos=.inl v := (slotOrder o).symm_apply_apply (.inl v)
    rw [unrank] at got
    change (p.operand.read m (oddPosition.eval m ((idx v).val:Word w))).val=_
    rw [odd_eval,coord,got]
    change ((o.core g).val:Word w).val=_
    rw [Fin.val_cast_of_lt ((o.core g).isLt.trans_le rowFit)]
    exact (congrArg (fun u : Σ j,Fin (B.ordinary (o.core.symm j)).length => u.1.val) (selected v)).symm

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
