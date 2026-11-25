import OAI.Hierarchy.ProbeLiveSlots
import OAI.Hierarchy.ProbeStageNeighborhood
import OAI.Hierarchy.ProbeBalls

namespace OAI
/-! # Every actual purchased H-chain lies in its radius-2H stage test -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ProtocolRAM
open scoped Classical BigOperators
noncomputable section

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

def liveRow (path : LiveChains S π depth marked) (j : Fin (depth+1)) :=
  liveDigit S π depth marked path.1 path.2.1 (path.2.2,j)

/-- The H consecutive purchased tile rows are actual tiles of one CT group, with a
sampler output-to-input join between each consecutive pair, including padded scans. -/
theorem liveRow_next (path : LiveChains S π depth marked) {j : ℕ} (hj : j+1<depth+1) :
    let p := advisedStage h d π path.1
    let row := liveRow S π depth marked path
    p.group (row ⟨j+1,hj⟩)=p.group (row ⟨j,by omega⟩) ∧
    p.input (row ⟨j+1,hj⟩) ∈ S.rows (stageAt h d path.1).span (p.output (row ⟨j,by omega⟩)) := by
  intro p row
  let sh := stageAt h d path.1
  let enc := (Fintype.equivFin sh.Group).toEmbedding
  let cs := ProtocolRAMPurchaseOwners.successor p enc (D:=S.degree) (portDigits (S.rows sh.span))
  apply (native_next p enc (S.rows sh.span) (S.out_degree sh.span) _ _).mp
  exact selectedEmbedding_next (ps:=PurchaseDFS.candidates cs depth) (marked:=marked path.1 path.2.1)
    (good:=fun q hq => ⟨((PurchaseDFS.mem_candidates cs).mp hq).1,((PurchaseDFS.mem_candidates cs).mp hq).2.1⟩)
    (fun x y => y∈PurchaseDFS.next cs x) (fun q hq => ((PurchaseDFS.mem_candidates cs).mp hq).2.2) path.2.2 hj

private theorem neighborhood_mono_radius {V : Type*} [DecidableEq V] (next : V → Finset V)
    (x : V) {r r' : ℕ} (le : r≤r') : neighborhood next x r ⊆ neighborhood next x r' := by
  induction le with
  | refl => exact fun _ h => h
  | step le ih => exact fun y inside => (mem_neighborhood_step next x y _).mpr ⟨y,ih inside,Or.inl rfl⟩

/-- Both endpoints of every tile lie in the tested ball of its actual first inlet.
The displayed radius is independent of the number of groups and external addresses. -/
theorem live_in_ball (path : LiveChains S π depth marked) :
    let p := advisedStage h d π path.1
    let row := liveRow S π depth marked path
    let root := Sum.inl (p.input (row 0))
    let next := Tiles.localNext p (p.group (row 0)) (S.rows (stageAt h d path.1).span)
    ∀ j : Fin (depth+1), p.group (row j)=p.group (row 0) ∧
      Sum.inl (p.input (row j)) ∈ neighborhood next root (2*(depth+1)) ∧
      Sum.inr (p.output (row j)) ∈ neighborhood next root (2*(depth+1)) := by
  intro p row root next
  let g := p.group (row 0)
  let sampler := S.rows (stageAt h d path.1).span
  have step (j : Fin (depth+1)) (grp : p.group (row j)=g) :
      Sum.inr (p.output (row j)) ∈ next (.inl (p.input (row j))) :=
    (Tiles.across p g sampler _ _).mpr (Or.inl ⟨row j,grp,rfl,rfl⟩)
  have induction' : ∀ j : ℕ, ∀ hj : j<depth+1, p.group (row ⟨j,hj⟩)=g ∧
      Sum.inl (p.input (row ⟨j,hj⟩)) ∈ neighborhood next root (2*j) := by
    intro j; induction j with
    | zero => intro hj; exact ⟨rfl,by simp [root,neighborhood]⟩
    | succ j ih =>
      intro hj
      have ⟨grp,previous⟩ := ih (by omega)
      have ⟨grp',link⟩ := liveRow_next S π depth marked path hj
      have mid := (mem_neighborhood_step next root _ (2*j)).mpr ⟨_,previous,Or.inr (step ⟨j,by omega⟩ grp)⟩
      have join := (Tiles.back p g sampler _ _).mpr (Or.inr link)
      have dest := (mem_neighborhood_step next root _ (2*j+1)).mpr ⟨_,mid,Or.inr join⟩
      exact ⟨grp'.trans grp,by simpa only [Nat.mul_succ,Nat.add_assoc] using dest⟩
  intro j
  obtain ⟨grp,near⟩ := induction' j.val j.isLt
  have nextNear := (mem_neighborhood_step next root _ (2*j.val)).mpr ⟨_,near,Or.inr (step j grp)⟩
  exact ⟨grp,neighborhood_mono_radius next root (by omega) near,neighborhood_mono_radius next root (by omega) nextNear⟩

end
end Hierarchy.ProbeStage

end OAI
