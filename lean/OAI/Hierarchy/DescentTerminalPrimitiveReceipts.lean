import OAI.Hierarchy.DescentTerminalClippedFields

namespace OAI
/-! # A live scalar book is certified by its eight native field families -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalChronologicalBooks DescentKernelHistory DescentTerminalRecipeRows
open DescentTerminalPrintedFields DescentTerminalLeafDigits DescentTerminalScalarHeader
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w : ℕ} (site:Site) (r:∀v:Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth:Birth r) (hH:∀v,Fintype.card (r v).Hidden≤H) (hN:∀v,Fintype.card (r v).Node≤N)
    (hA:∀v j,(r v).arity j≤A) (hw:∀v j,(r v).width j≤w) (short:∀v,site.arity v≤q) (v:Fin site.nodes)
    (data:Key H N A→ℕ)
local notation "r0" => record site r birth hH hN hA hw short v

/-- Physical counts and actual nodes/operands suffice; no premise needs the bytes
of unused operands of a live node, or any values of nonexistent nodes. -/
structure PrimitiveReceipts (nodeTest : Prop → Prop := id) : Prop where
  ports : nodeTest (data publicArity=site.arity v)
  live : nodeTest (data (.inr (.inl ()))=1)
  hidden : data hiddenCount=Fintype.card (r v).Hidden
  nodes : nodeTest (data nodeCount=Fintype.card (r v).Node)
  width : ∀j,data (hiddenWidth ((ordinal (birth.hidden v) j).castLE (hH v)))=(r v).width j
  role : ∀u,data (nodeRole ((ordinal (birth.atom v) u).castLE (hN v)))=((r v).tag u).val+1
  arity : ∀u,data (nodeArity ((ordinal (birth.atom v) u).castLE (hN v)))=(r v).arity u
  operand : ∀u (j:Fin ((r v).arity u)),data (nodeArg ((ordinal (birth.atom v) u).castLE (hN v)) (j.castLE (hA v u)))=
    ((r v).operand u j).elim (fun b=>b.val+1) (fun x=>q+(ordinal (birth.hidden v) x).val+1)

/-- Restore the two scalar observations read from the native presence and population banks. -/
theorem PrimitiveReceipts.with_measured_counts {test:Prop→Prop}
    (rest:PrimitiveReceipts (q:=q) site r birth hH hN hA v data test)
    (public_:data publicArity=site.arity v) (present:data (.inr (.inl ()))=1) (count:data nodeCount=Fintype.card (r v).Node) :
    PrimitiveReceipts (q:=q) site r birth hH hN hA v data :=
  ⟨public_,present,rest.hidden,count,rest.width,rest.role,rest.arity,rest.operand⟩

/-- Turn only the true reached numerical population, widths, role tags, and pointer
observations into the earlier primed family field used by the masked suffix. -/
theorem PrimitiveReceipts.read (h:PrimitiveReceipts (q:=q) site r birth hH hN hA v data)
    (k:Key H N A) (allowed:allows (fun j=>(value r0 j).val) k) : data k=(value r0 k).val := by
  have cnt:=counts_read site r birth hH hN hA hw short v
  have node (b:Fin N) (hb:b.val<Fintype.card (r v).Node) : ∃u,(ordinal (birth.atom v) u).castLE (hN v)=b := by
    refine ⟨(ordinal (birth.atom v)).symm ⟨b.val,hb⟩,?_⟩
    exact congrArg (fun j : Fin (Fintype.card (r v).Node)=>j.castLE (hN v))
      ((ordinal (birth.atom v)).apply_symm_apply ⟨b.val,hb⟩)
  rcases k with u|(u|(i|(i|(⟨i,a⟩|(⟨i,a⟩|(⟨i,a⟩|⟨i,a,b⟩))))))
  · cases u;exact h.ports.trans cnt.1.symm
  · cases u;exact h.live
  · have eq:i=0:=Subsingleton.elim ..;subst i;exact h.hidden.trans cnt.2.1.symm
  · have eq:i=0:=Subsingleton.elim ..;subst i;exact h.nodes.trans cnt.2.2.symm
  · have eq:i=0:=Subsingleton.elim ..;subst i
    have ha:a.val<Fintype.card (r v).Hidden:=by simpa [allows,cnt.2.1] using allowed
    let x:=(ordinal (birth.hidden v)).symm ⟨a.val,ha⟩
    have hxa : (ordinal (birth.hidden v) x).castLE (hH v)=a :=
      congrArg (fun j : Fin (Fintype.card (r v).Hidden)=>j.castLE (hH v))
        ((ordinal (birth.hidden v)).apply_symm_apply ⟨a.val,ha⟩)
    exact hxa ▸ (h.width x).trans (width_read site r birth hH hN hA hw short v x).symm
  · have eq:i=0:=Subsingleton.elim ..;subst i
    obtain ⟨u,rfl⟩:=node a (by simpa [allows,cnt.2.2] using allowed)
    exact (h.role u).trans (node_read site r birth hH hN hA hw short v u).1.symm
  · have eq:i=0:=Subsingleton.elim ..;subst i
    obtain ⟨u,rfl⟩:=node a (by simpa [allows,cnt.2.2] using allowed)
    exact (h.arity u).trans (node_read site r birth hH hN hA hw short v u).2.symm
  · have eq:i=0:=Subsingleton.elim ..;subst i
    have ok:=allowed
    change a.val<(value r0 nodeCount).val ∧ b.val<(value r0 (nodeArity a)).val at ok
    obtain ⟨u,rfl⟩:=node a (cnt.2.2 ▸ ok.1)
    have right:=(node_read site r birth hH hN hA hw short v u).2
    let j:Fin ((r v).arity u):=⟨b.val,right ▸ ok.2⟩
    exact (h.operand u j).trans (arg_read site r birth hH hN hA hw short v u j).symm

end
end Hierarchy.DescentTerminalVertexFields

end OAI
