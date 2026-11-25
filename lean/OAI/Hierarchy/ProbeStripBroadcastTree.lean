import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.ProbeStrip
import OAI.Hierarchy.ProbeArbitraryPlacement
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths

namespace OAI
/-! # Original core sockets for the bounded strip broadcast -/

noncomputable section
namespace Hierarchy.AdaptiveProbe.Strip

open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Probe
open scoped Classical BigOperators

def treeRole {Extra : Type*} (n k : ℕ) : TreeLink n k → ColumnWires.Role (TreeColumn n) (Fin n) Extra k
  | .inl e => .horizontal e none
  | .inr (c,j,s) => .radius c j s

def treeEnds (n k : ℕ) (e : TreeLink n k) : DistinctPair (TreeSite n k) :=
  ColumnWires.ends (horizontal n) (isEmptyElim : Empty→DistinctPair (TreeSite n k)) (treeRole n k e)

theorem tree_role_ends {Extra : Type*} (n k : ℕ) (extra : Extra→DistinctPair (TreeSite n k)) (e : TreeLink n k) :
    ColumnWires.ends (horizontal n) extra (treeRole n k e)=treeEnds n k e := by
  rcases e with e|⟨c,j,s⟩ <;> rfl

def treeGraph {n k : ℕ} (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k))) :
    PortGraph (Fin (Fintype.card (TreeSite n k))) (TreeLink n k) :=
  ⟨fun e=>name (treeEnds n k e).left,fun e=>name (treeEnds n k e).right⟩

theorem tree_connected {n k : ℕ} (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k))) :
    BroadcastConnected (treeGraph name) := by
  intro W x edge
  let val (c : TreeColumn n) (a : ColumnLayer k) := x (name (c,a))
  have path (j : Fin (n+1)) : val (column n j) none = val (column n 0) none := by
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih => exact (edge (.inl j)).symm.trans ih
  have same (c : TreeColumn n) (a : ColumnLayer k) :
      val c a=val (column n 0) none := by
    have atCenter : val c none=val (column n 0) none := by
      have e : column n c.val=c := Subtype.ext rfl
      simpa only [e] using path c.val
    cases a with
    | none => exact atCenter
    | some a => exact (edge (.inr (c,a))).symm.trans atCenter
  intro i j
  obtain ⟨⟨c,a⟩,rfl⟩ := name.surjective i
  obtain ⟨⟨e,b⟩,rfl⟩ := name.surjective j
  exact (same c a).trans (same e b).symm

theorem tree_price {n k : ℕ} {Extra : Type*} (M : ℝ) (len : Fin n→ℝ) (quote : Extra→ℝ)
    (e : TreeLink n k) :
    ColumnWires.quote M len quote (treeRole n k e)=Sum.elim len (fun _=>M) e := by
  rcases e with e|⟨c,j,s⟩ <;> rfl

theorem tree_cost {n k : ℕ} {Extra : Type*} (M : ℝ) (len : Fin n→ℝ) (bound : ∀e,len e≤1)
    (quote : Extra→ℝ) : (∑ e : TreeLink n k,ColumnWires.quote M len quote (treeRole n k e))≤
      (Fintype.card (TreeLink n k):ℝ)*max M 1 := by
  refine (Finset.sum_le_sum (s:=Finset.univ) fun e _=> ?_).trans_eq
    (by simp : (∑ _ : TreeLink n k,max M 1)=(Fintype.card (TreeLink n k):ℝ)*max M 1)
  rw [tree_price]
  rcases e with t|a
  · exact (bound _).trans (le_max_right _ _)
  · exact le_max_left _ _

theorem tree_card (n k : ℕ) : Fintype.card (TreeLink n k) = n + (n+1)*(k*2) := by
  let e : Fin (n+1) ≃ TreeColumn n := Equiv.ofBijective (column n) ⟨(column n).injective,
    fun c=>⟨c.val,Subtype.ext rfl⟩⟩
  have hc : Fintype.card (TreeColumn n)=n+1 := (Fintype.card_congr e).symm.trans (Fintype.card_fin _)
  simp [TreeLink,Fintype.card_sum,Fintype.card_prod,hc]

/-- Every physical broadcast link adds its chosen bit width to exactly
the original canonical role chord. Sorting and reversing the endpoints
only affect the displayed orientation. -/
theorem tree_single {n k : ℕ} {Extra : Type*} (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k)))
    (extra : Extra→DistinctPair (TreeSite n k)) (e : TreeLink n k) (w : ℕ) :
    (treeGraph name).chordWidth e w =
      Finsupp.single (@DistinctPair.chord _ _ ⟨name⟩ (ColumnWires.ends (horizontal n) extra (treeRole n k e))) w := by
  rw [tree_role_ends]
  let a:=name (treeEnds n k e).left
  let b:=name (treeEnds n k e).right
  have apart : a≠b := name.injective.ne (treeEnds n k e).apart
  rcases lt_or_gt_of_ne apart with ab|ba
  · simp [PortGraph.chordWidth,treeGraph,DistinctPair.chord,show name (treeEnds n k e).left < name (treeEnds n k e).right from ab]
  · have neg : ¬ name (treeEnds n k e).left < name (treeEnds n k e).right := not_lt.mpr ba.le
    simp [PortGraph.chordWidth,treeGraph,DistinctPair.chord,neg,
      show name (treeEnds n k e).right < name (treeEnds n k e).left from ba]

theorem tree_widths {n k : ℕ} {Extra : Type*} (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k)))
    (extra : Extra→DistinctPair (TreeSite n k)) (w : ℕ) :
    (treeGraph name).chordWidths (fun _=>w)=
      ∑ e : TreeLink n k,Finsupp.single (@DistinctPair.chord _ _ ⟨name⟩
        (ColumnWires.ends (horizontal n) extra (treeRole n k e))) w :=
  Finset.sum_congr rfl (fun e _=>tree_single name extra e w)

/-- The reporter's canonical sorted socket pair is calculated from the
same two local sites on every template, even when physical order flips. -/
theorem actual_tree_chord {n k S : ℕ} {Extra : Type*} (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k)))
    (place : TreeSite n k ↪ Fin S) (extra : Extra→DistinctPair (TreeSite n k)) (e : TreeLink n k) :
    Probe.physicalChord (name.symm.toEmbedding.trans place)
      (@DistinctPair.chord _ _ ⟨name⟩ (ColumnWires.ends (horizontal n) extra (treeRole n k e))) =
      orderedEnds (place (treeEnds n k e).left) (place (treeEnds n k e).right)
        (place.injective.ne (treeEnds n k e).apart) := by
  rw [tree_role_ends]
  exact physicalChord_role name place _

end Hierarchy.AdaptiveProbe.Strip
end

end OAI
