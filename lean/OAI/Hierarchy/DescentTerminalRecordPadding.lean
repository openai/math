import OAI.Hierarchy.DescentTerminalRecordFields

namespace OAI
/-! # Padding on occupied terminal recipe records -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalPrintedFields
open DescentTerminalScalarHeader DescentTerminalChronologicalBooks DescentTerminalLeafDigits DescentKernelHistory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V S B : ℕ}
local notation "K" => Key H N A
local notation "Vertex" => DescentTerminalSiteShelves.Row (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)

def allows (atKey : K→ℕ) : K→Prop
  | .inl _=>True
  | .inr (.inl _)=>True
  | .inr (.inr (.inl _))=>True
  | .inr (.inr (.inr (.inl _)))=>True
  | .inr (.inr (.inr (.inr (.inl z))))=>z.2.val<atKey hiddenCount
  | .inr (.inr (.inr (.inr (.inr (.inl z)))))=>z.2.val<atKey nodeCount
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl z))))))=>z.2.val<atKey nodeCount
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr z))))))=>z.2.1.val<atKey nodeCount ∧ z.2.2.val<atKey (nodeArity z.2.1)

def Zeros (s : Vertex) := ∀k : K,¬allows (fun j=>(value s j).val) k → (value s k).val=0

section Authentic
variable (site : Site) (r : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v))) (birth : Birth r)
    (hH : ∀v,Fintype.card (r v).Hidden≤H) (hN : ∀v,Fintype.card (r v).Node≤N) (hA : ∀v j,(r v).arity j≤A)
    (hw : ∀v j,(r v).width j≤w) (small : ∀v,site.arity v≤q) (v : Fin site.nodes)
local notation "z" => record site r birth hH hN hA hw small v
theorem record_zeros : Zeros z := by
  intro k bad
  have cnt:=counts_read site r birth hH hN hA hw small v
  rcases k with _|(_|(_|(_|(a|(b|(c|d))))))
  all_goals try exact (bad trivial).elim
  · have no : ¬a.2.val<Fintype.card (r v).Hidden := by simpa [allows,cnt.2.1] using bad
    simp [value,record,one,emit,fill,digit,extend,localBook,no]
  · rcases b with ⟨i,k⟩
    fin_cases i
    have no : ¬k.val<Fintype.card (r v).Node := by simpa [allows,cnt.2.2] using bad
    simp [value,record,one,emit,fill,digit,extend,DescentTerminalPrintedFields.atom,localBook,no]
  · rcases c with ⟨i,k⟩
    fin_cases i
    have no : ¬k.val<Fintype.card (r v).Node := by simpa [allows,cnt.2.2] using bad
    simp [value,record,one,emit,fill,digit,extend,DescentTerminalPrintedFields.atom,localBook,no]
  · rcases d with ⟨i,d⟩
    fin_cases i
    by_cases node : d.1.val<Fintype.card (r v).Node
    · let u:=(ordinal (birth.atom v)).symm ⟨d.1.val,node⟩
      have row : ((ordinal (birth.atom v)) u).castLE (hN v)=d.1 :=
        congrArg (fun k : Fin (Fintype.card (r v).Node)=>k.castLE (hN v))
          ((ordinal (birth.atom v)).apply_symm_apply ⟨d.1.val,node⟩)
      have ar:=(node_read site r birth hH hN hA hw small v u).2
      rw [row] at ar
      have off : ¬d.2.val<(r v).arity u := by simpa [allows,cnt.2.2,node,ar] using bad
      dsimp [u] at off
      simp [value,record,one,emit,fill,digit,extend,DescentTerminalPrintedFields.atom,localBook,DescentKernelHistory.encode,node,ref,off]
    · simp [value,record,one,emit,fill,digit,extend,DescentTerminalPrintedFields.atom,localBook,node]
end Authentic

end
end Hierarchy.DescentTerminalVertexFields

end OAI
