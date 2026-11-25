import OAI.Hierarchy.ProbeChainBall
import OAI.Hierarchy.ProtocolRAMPurchaseRows
import OAI.Hierarchy.ProtocolRAMMarkPaths

namespace OAI
/-! # Original DFS row witnessing each retained stage chain -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage
open scoped Classical

private theorem accepted_at {n : ℕ} (ps : List (List (Fin n))) (left : Finset (Fin n))
    (p : List (Fin n)) (taken : p∈(scanPaths ps left).1) :
    ∃ i : Fin ps.length, ps.get i=p ∧
      (MarkTape.decisions ps left)[i.val]'(by simp)=true := by
  induction ps generalizing left with
  | nil => simp [scanPaths] at taken
  | cons a ps ih =>
    by_cases use : a.toFinset ⊆ left
    · simp only [scanPaths,ite_eq_left use,List.mem_cons] at taken
      rcases taken with eq|tail
      · subst p
        exact ⟨0,rfl,by simp [MarkTape.decisions,use]⟩
      · obtain ⟨i,read,bit⟩ := ih _ tail
        exact ⟨i.succ,read,by simpa [MarkTape.decisions,use] using bit⟩
    · simp only [scanPaths,ite_eq_right use] at taken
      obtain ⟨i,read,bit⟩ := ih _ taken
      exact ⟨i.succ,read,by simpa [MarkTape.decisions,use] using bit⟩

/-- Every row of the retained list can be located at an actual selected
padded DFS candidate. The entire field tuple comes from that one
candidate, even when two original branch words traverse the same path. -/
theorem reached {n D h : ℕ} (choice : Fin n → Fin D → Option (Fin n)) (left : Finset (Fin n))
    (p : List (Fin n)) (kept : p ∈ (scanPaths (PurchaseDFS.candidates choice h) left).1) :
    ∃ i : PurchaseDirectory.Index n D h,
      (MarkTape.decisions ((PurchaseDFS.layout n D h).map (PurchaseDFS.filled choice))
        (left.map Fin.castSuccEmb))[i.val]'(by simpa using i.isLt)=true ∧
      List.ofFn (PurchaseColumns.rowTile choice i) = p.map Fin.castSucc := by
  let xs := (PurchaseDFS.layout n D h).map (PurchaseDFS.filled choice)
  have actual : p.map Fin.castSucc ∈ (scanPaths xs (left.map Fin.castSuccEmb)).1 := by
    dsimp only [xs]
    rw [PurchaseDFS.scan_filled]
    exact List.mem_map_of_mem kept
  obtain ⟨j,read,flag⟩ := accepted_at xs (left.map Fin.castSuccEmb) (p.map Fin.castSucc) actual
  let i : PurchaseDirectory.Index n D h := ⟨j.val,by simpa [xs] using j.isLt⟩
  refine ⟨i,flag,(PurchaseColumns.rowTile_filled choice i).trans ?_⟩
  simpa only [xs,PurchaseDirectory.item,List.get_eq_getElem,List.getElem_map,i] using read

/-- A fixed public stage-and-sign stratum covers each geometrically named
purchased strip, using precisely the signed source row at every test axis. -/
theorem retainedRows {z d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (marked : StageAt z d → (Fin k × Bool) → Finset (Fin (2^z)))
    (path : LiveChains S π depth marked) :
    let stage := stageAt z d path.1
    let choice := ProtocolRAMPurchaseOwners.successor (advisedStage z d π path.1)
      (Fintype.equivFin stage.Group).toEmbedding (D:=S.degree) (portDigits (S.rows stage.span))
    ∃ i : PurchaseDirectory.Index (2^z) S.degree depth,
      (MarkTape.decisions ((PurchaseDFS.layout (2^z) S.degree depth).map (PurchaseDFS.filled choice))
        ((marked path.1 path.2.1).map Fin.castSuccEmb))[i.val]'(by simpa using i.isLt)=true ∧
      ∀ j : Fin (depth+1), PurchaseColumns.rowTile choice i j =
        (liveRow S π depth marked path j).castSucc := by
  let choice := ProtocolRAMPurchaseOwners.successor (advisedStage z d π path.1)
    (Fintype.equivFin (stageAt z d path.1).Group).toEmbedding (D:=S.degree)
    (portDigits (S.rows (stageAt z d path.1).span))
  let paths := (scanPaths (PurchaseDFS.candidates choice depth) (marked path.1 path.2.1)).1
  let ordinal : Fin paths.length := path.2.2
  let p := paths.get ordinal
  have found : p ∈ paths := List.get_mem ..
  obtain ⟨i,flag,rows⟩ := reached choice (marked path.1 path.2.1) p found
  refine ⟨i,flag,fun j => ?_⟩
  have val := getElem_congr rows (rfl : j.val=j.val) (by simpa using j.isLt)
  have length : p.length=depth+1 := by
    simpa only [List.length_ofFn,List.length_map] using (congrArg List.length rows).symm
  change PurchaseColumns.rowTile choice i j=(p.get (Fin.cast length.symm j)).castSucc
  rw [List.get_eq_getElem]
  simpa only [List.getElem_ofFn,List.getElem_map,Fin.val_cast,Fin.eta] using val

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
