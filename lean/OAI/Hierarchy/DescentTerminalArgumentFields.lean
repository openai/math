import OAI.Hierarchy.DescentTerminalClippedFields

namespace OAI
/-! # Only node counts, live arities and live operand slots affect the private argument fields -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalChronologicalBooks DescentKernelHistory DescentTerminalRecipeRows
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w : ℕ}
local notation "Raw" => Key H N A→ℕ


structure ArgumentReads (observed actual : Key H N A→ℕ) : Prop where
  count : observed nodeCount=actual nodeCount
  arity (i : Fin N) : i.val<actual nodeCount → observed (nodeArity i)=actual (nodeArity i)
  reference (i : Fin N) (j : Fin A) : i.val<actual nodeCount → j.val<actual (nodeArity i) →
    observed (nodeArg i j)=actual (nodeArg i j)

theorem ArgumentReads.of_allowed {x y : Key H N A→ℕ} (h : ∀k,allows y k→x k=y k) : ArgumentReads x y :=
  ⟨h _ trivial,fun _i inside=>h _ inside,fun _i _j inside slot=>h _ ⟨inside,slot⟩⟩

theorem ArgumentReads.clipped {x y : Key H N A→ℕ} (read : ArgumentReads x y) (i : Fin N) (j : Fin A) :
    clean x (nodeArg i j)=clean y (nodeArg i j) := by
  classical
  by_cases active : i.val<y nodeCount
  · have length:=read.arity i active
    by_cases used : j.val<y (nodeArity i)
    · have ok : allows y (nodeArg i j):=⟨active,used⟩
      have left : allows x (nodeArg i j):=⟨by rwa [read.count],by rwa [length]⟩
      rw [clean,ite_eq_left left,clean,ite_eq_left ok]
      exact read.reference i j active used
    · have no : ¬allows y (nodeArg i j):=fun h=>used h.2
      have left : ¬allows x (nodeArg i j):=fun h=>used (length ▸ h.2)
      rw [clean,ite_eq_right left,clean,ite_eq_right no]
  · have no : ¬allows y (nodeArg i j):=fun h=>active h.1
    have left : ¬allows x (nodeArg i j):=fun h=>active (read.count ▸ h.1)
    rw [clean,ite_eq_right left,clean,ite_eq_right no]

/-- The three measured families use the physical node and hidden-word orders of the book. -/
theorem argument_reads_of_nodes (site : Site) (r : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth : Birth r) (hH : ∀v,Fintype.card (r v).Hidden≤H) (hN : ∀v,Fintype.card (r v).Node≤N)
    (hA : ∀v u,(r v).arity u≤A) (hw : ∀v u,(r v).width u≤w) (short : ∀v,site.arity v≤q)
    (v : Fin site.nodes) (x : Raw)
    (population : x nodeCount=Fintype.card (r v).Node)
    (lengths : ∀u,x (nodeArity ((ordinal (birth.atom v) u).castLE (hN v)))=(r v).arity u)
    (refs : ∀u (j : Fin ((r v).arity u)),
      x (nodeArg ((ordinal (birth.atom v) u).castLE (hN v)) (j.castLE (hA v u)))=
        ((r v).operand u j).elim (fun a=>a.val+1) (fun z=>q+(ordinal (birth.hidden v) z).val+1)) :
    let book:=record site r birth hH hN hA hw short v
    ArgumentReads x (fun k=>(value book k).val) := by
  have count:=(counts_read site r birth hH hN hA hw short v).2.2
  have node (i:Fin N) (inside:i.val<Fintype.card (r v).Node) :
      ∃u,(ordinal (birth.atom v) u).castLE (hN v)=i := by
    refine ⟨(ordinal (birth.atom v)).symm ⟨i.val,inside⟩,?_⟩
    apply Fin.ext
    simp
  refine ⟨population.trans count.symm,?_,?_⟩
  · intro i inside
    obtain ⟨u,rfl⟩:=node i (count ▸ inside)
    exact (lengths u).trans (node_read site r birth hH hN hA hw short v u).2.symm
  · intro i j inside slot
    obtain ⟨u,rfl⟩:=node i (count ▸ inside)
    have size:=(node_read site r birth hH hN hA hw short v u).2
    let a:Fin ((r v).arity u):=⟨j.val,size ▸ slot⟩
    exact (refs u a).trans (arg_read site r birth hH hN hA hw short v u a).symm

end
end Hierarchy.DescentTerminalVertexFields

end OAI
