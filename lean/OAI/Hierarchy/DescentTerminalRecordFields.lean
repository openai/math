import OAI.Hierarchy.DescentTerminalVertexFields

namespace OAI
/-! # Numerical meaning of each occupied primitive vertex-record field -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalChronologicalBooks DescentKernelHistory DescentTerminalRecipeRows
open DescentTerminalPrintedFields DescentTerminalLeafDigits DescentTerminalScalarHeader
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w : ℕ} (site : Site) (r : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth : Birth r) (hH : ∀v,Fintype.card (r v).Hidden≤H) (hN : ∀v,Fintype.card (r v).Node≤N)
    (hA : ∀v j,(r v).arity j≤A) (hw : ∀v j,(r v).width j≤w) (short : ∀v,site.arity v≤q) (v : Fin site.nodes)

def record : DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) :=
  (⟨site.arity v,Nat.lt_succ_of_le (short v)⟩,localBook site r birth hH hN hA hw short v)
local notation "z" => record site r birth hH hN hA hw short v
local notation "K" => Key H N A

def publicArity : K := .inl ()
def hiddenCount : K := .inr (.inr (.inl 0))
def nodeCount : K := .inr (.inr (.inr (.inl 0)))
def hiddenWidth (i : Fin H) : K := .inr (.inr (.inr (.inr (.inl (0,i)))))
def nodeRole (i : Fin N) : K := .inr (.inr (.inr (.inr (.inr (.inl (0,i))))))
def nodeArity (i : Fin N) : K := .inr (.inr (.inr (.inr (.inr (.inr (.inl (0,i)))))))
def nodeArg (i : Fin N) (j : Fin A) : K := .inr (.inr (.inr (.inr (.inr (.inr (.inr (0,i,j)))))))

theorem counts_read : (value z publicArity).val=site.arity v ∧
    (value z hiddenCount).val=Fintype.card (r v).Hidden ∧ (value z nodeCount).val=Fintype.card (r v).Node := by
  simp [publicArity,hiddenCount,nodeCount,value,record,one,emit,fill,digit,extend,localBook]

theorem width_read (j : (r v).Hidden) : (value z (hiddenWidth ((ordinal (birth.hidden v) j).castLE (hH v)))).val=(r v).width j := by
  simp [hiddenWidth,value,record,one,emit,fill,digit,extend,localBook,DescentKernelHistory.encode]

theorem node_read (u : (r v).Node) :
    (value z (nodeRole ((ordinal (birth.atom v) u).castLE (hN v)))).val=((r v).tag u).val+1 ∧ (value z (nodeArity ((ordinal (birth.atom v) u).castLE (hN v)))).val=(r v).arity u := by
  simp [nodeRole,nodeArity,value,record,one,emit,fill,DescentTerminalPrintedFields.atom,digit,extend,localBook,DescentKernelHistory.encode]

theorem arg_read (u : (r v).Node) (j : Fin ((r v).arity u)) :
    (value z (nodeArg ((ordinal (birth.atom v) u).castLE (hN v)) (j.castLE (hA v u)))).val=
      ((r v).operand u j).elim (fun b=>b.val+1) (fun h=>q+(ordinal (birth.hidden v) h).val+1) := by
  let book:=localBook site r birth hH hN hA hw short v
  let idx:=ordinal (birth.atom v) u
  let argument (n : (r v).Node) (a : Fin A) : Option (Fin q ⊕ Fin (Fintype.card (r v).Hidden)) :=
    if h:a.val<(r v).arity n then
      some (((r v).operand n ⟨a.val,h⟩).map (Fin.castLE (short v)) (ordinal (birth.hidden v)))
    else none
  let rowAt (n : (r v).Node) :=
    some ((r v).tag n,(⟨(r v).arity n,Nat.lt_succ_of_le (hA v n)⟩ : Fin (A+1)),argument n)
  have original (i : Fin (Fintype.card (r v).Node)) :
      book.2.2.rows i=rowAt ((ordinal (birth.atom v)).symm i) :=rfl
  have row : DescentTerminalPrintedFields.atom book (idx.castLE (hN v))=rowAt u :=by
    unfold DescentTerminalPrintedFields.atom
    refine (DescentTerminalScalarHeader.extend_castLE (n:=Fintype.card (r v).Node) (m:=N)
      book.2.2.rows none (hN v) idx).trans ?_
    exact (original idx).trans (congrArg rowAt ((ordinal (birth.atom v)).symm_apply_apply u))
  change (((DescentTerminalPrintedFields.atom book (idx.castLE (hN v))).map
    (fun entry=>DescentTerminalScalarHeader.ref (Nat.le_of_lt_succ book.1.isLt) (entry.2.2 (j.castLE (hA v u))))).getD 0).val=_
  rw [row]
  have live : argument u (j.castLE (hA v u))=
      some (((r v).operand u j).map (Fin.castLE (short v)) (ordinal (birth.hidden v))) :=by
    unfold argument
    rw [dite_eq_left (show (j.castLE (hA v u)).val<(r v).arity u from j.isLt)]
    rfl
  change (DescentTerminalScalarHeader.ref (hH v) (argument u (j.castLE (hA v u)))).val=_
  rw [live]
  cases eqn : (r v).operand u j with
  | inl b=>simp [DescentTerminalScalarHeader.ref,finSumFinEquiv]
  | inr h=>simp [DescentTerminalScalarHeader.ref,finSumFinEquiv,Nat.add_comm]

end
end Hierarchy.DescentTerminalVertexFields

end OAI
