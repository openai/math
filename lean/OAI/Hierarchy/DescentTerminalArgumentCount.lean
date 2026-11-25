import OAI.Hierarchy.DescentTerminalPrivateReferences
import OAI.Hierarchy.DescentTerminalPrivateHome
import OAI.Hierarchy.DescentTerminalArgumentFields

namespace OAI
/-! # Only node counts, live arities and live operand slots affect the terminal private counters -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalChronologicalBooks DescentKernelHistory DescentTerminalRecipeRows
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w groups blocks : ℕ} (data : BlockFields q t H N A w groups blocks)
local notation "Raw" => Key H N A→ℕ


theorem private_count_from_arguments (site : Site) (r : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth : Birth r) (hH : ∀v,Fintype.card (r v).Hidden≤H) (hN : ∀v,Fintype.card (r v).Node≤N)
    (hA : ∀v u,(r v).arity u≤A) (hw : ∀v u,(r v).width u≤w) (short : ∀v,site.arity v≤q)
    (location : Fin site.nodes ↪ Fin (groups*blocks)) (occupied : ∀c,blankAt data c≠0 ↔ ∃v,location v=c)
    (issued : ∀v,let book:=record site r birth hH hN hA hw short v
      ArgumentReads (venueField (cellAt data (location v))) (fun j=>(value book j).val)) :
    privateHome data=∑v,Fintype.card (r v).UsedWord := by
  classical
  have live : Finset.univ.filter (fun c=>blankAt data c≠0)=Finset.univ.map location := by
    ext c
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map] using occupied c
  rw [privateHome_eq,←Finset.sum_filter,live,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro v _
  let book:=record site r birth hH hN hA hw short v
  let fields : Raw:=venueField (cellAt data (location v))
  have digit (ij : Fin N×Fin A) : clean fields (nodeArg ij.1 ij.2)=(value book (nodeArg ij.1 ij.2)).val := by
    apply ((issued v).clipped ij.1 ij.2).trans
    by_cases allowed : allows (fun j=>(value book j).val) (nodeArg ij.1 ij.2)
    · exact ite_eq_left allowed
    · exact (ite_eq_right allowed).trans (record_zeros site r birth hH hN hA hw short v _ allowed).symm
  change (cutFields fields q).card=_
  have same : (fun ij : Fin N×Fin A=>clean fields (nodeArg ij.1 ij.2))=
      fun ij : Fin N×Fin A=>(value book (nodeArg ij.1 ij.2)).val :=funext digit
  rw [cutFields,same]
  exact references_card site r birth hH hN hA hw short v

end
end Hierarchy.DescentTerminalVertexFields

end OAI
