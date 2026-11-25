import OAI.Hierarchy.ProbePaidStripHits
import OAI.Hierarchy.ProtocolRAMStripTreeTraversal

namespace OAI
/-! # Exact archive occupancy of the original strip broadcast tree -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip StockCommit
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Fin.CommRing Classical

variable {h d k n w Srows : ℕ} {S : PurchaseSampler} {Extra Ball : Type}
local notation "Link" => TreeLink n k
local notation "Ports" => StripPorts S h d k (TreeColumn n) (Fin n) Extra

/-- The source cell, hop and amount refer to the same physical traversal
position. Its outgoing core edge is identified by the original native
horizontal or radial port expression of the retained ball. -/
theorem stripTree_paid_bound (p : Ports) (b : Board) (a : Area) (t : Traversals)
    (m : Memory w) (pos : 0<b.coreRows) (e : Fin b.rows)
    (head : t.Reads m (fun j : Fin a.rows=>broadcastWalk p b m j.val pos))
    (atRow : Ball ↪ Fin a.rows) (place : Ball×TreeSite n k ↪ Fin Srows)
    (geom : Fin b.rows→Chord Srows) (target : Ball→Link→Fin b.coreRows)
    (term : ∀u l,((treeTerm p b l).eval m ((atRow u).val:Word w)).val=(target u l).val)
    (chord : ∀u l,geom (b.coreIndex (target u l))=reportedRole place (treeEnds n k) u l)
    (copies maxBits : ℕ) (size : maxBits<2^w) (copySize : copies<2^w)
    (bounded : ∀j : Fin a.rows,(m (a.broadcast+j.val)).val≤ maxBits)
    (full : copies*maxBits<2^w)
    (live : ∀j : Fin a.rows,0<(m (a.broadcast+j.val)).val → ∃u,atRow u=j) :
    (PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m e ≤
      (n+(n+1)*(k*2))*(copies*maxBits) := by
  let ss:=PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits
  let count:=Fintype.card Link
  let path (j : Fin a.rows):=broadcastWalk p b m j.val pos
  have length (j : Fin a.rows) : (path j).length=count := by simp [path,count,broadcastWalk]
  let loc : Fin ss.count ≃ (Σ _ : Fin a.rows,Fin count) :=
    head.enum.trans (Equiv.sigmaCongrRight (fun j=>finCongr (length j)))
  have owner (i : Fin ss.count) : (t.sourceRow.eval m (i.val:Word w)).val=(loc i).1.val :=
    head.ownerAt i
  have amount (i : Fin ss.count) : (ss.amount.eval m (i.val:Word w)).val=
      copies*(m (a.broadcast+(loc i).1.val)).val :=
    PaidWidths.paidBroadcast_bits a _ _ _ _ _ _ _ m _ (loc i).1 (owner i) size (bounded _) copySize
      ((Nat.mul_le_mul_left _ (bounded _)).trans_lt full)
  have forward (i : Fin ss.count) :
      (ss.edge.eval m (i.val:Word w)).val=
        (b.coreIndex (treeTarget p b m (loc i).1.val ((Fintype.equivFin Link).symm (loc i).2) pos)).val := by
    calc
      _ = ((path (head.enum i).1)[(head.enum i).2.val]'(head.enum i).2.isLt).val := head.edgeAt i
      _ = _ := by simp only [path, broadcastWalk, List.getElem_ofFn]; rfl
  rw [←tree_card n k]
  apply ss.strip_hits m e loc atRow place geom
    (fun _ j=>treeEnds n k ((Fintype.equivFin Link).symm j)) (copies*maxBits)
  · intro i yes
    rw [amount] at yes
    apply live
    exact Nat.pos_of_ne_zero fun hz => by simp [hz] at yes
  · intro u j found _
    let i:=loc.symm ⟨atRow u,j⟩
    let l:=(Fintype.equivFin Link).symm j
    have coded : (ss.edge.eval m (i.val:Word w)).val=(b.coreIndex (target u l)).val := by
      simpa only [i,Equiv.apply_symm_apply,treeTarget_true p b m (atRow u).val l (target u l) pos (term u l),l]
        using forward i
    have eqn : e=b.coreIndex (target u l) := Fin.ext (found.symm.trans coded)
    rw [eqn]
    exact chord u l
  · intro i
    rw [amount]
    exact Nat.mul_le_mul_left copies (bounded _)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
