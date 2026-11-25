import OAI.Hierarchy.BinaryTreeCrossing
import OAI.Hierarchy.BinaryTree
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Cutwidth of complete binary trees

At the median of three cuts chosen in disjoint grandchild subtrees, the
middle subtree contributes its own crossing edges. A path outside that
subtree joins the early side to the late side, contributing another edge.
-/

namespace Hierarchy.BinaryTree

open scoped Classical
noncomputable section

private def rankCut {h : ℕ} (rank : V h → ℕ) (k : ℕ) : Finset (E h) :=
  Finset.univ.filter fun e => ¬ (rank (left h e)<k ↔ rank (right h e)<k)

private theorem mem_rankCut {h k : ℕ} {rank : V h → ℕ} (e : E h) :
    e ∈ rankCut rank k ↔ ¬ (rank (left h e)<k ↔ rank (right h e)<k) := by
  simp [rankCut]

private theorem cut_sides {h k : ℕ} {rank : V h → ℕ} (nonempty : 0<(rankCut rank k).card) :
    (∃ x,rank x<k) ∧ (∃ y,k≤rank y) := by
  obtain ⟨e,he⟩ := Finset.card_pos.mp nonempty
  have diff := (mem_rankCut e).mp he
  by_cases hl : rank (left h e)<k
  · exact ⟨⟨_,hl⟩,⟨_,Nat.le_of_not_gt (fun hr=>diff ⟨fun _=>hr,fun _=>hl⟩)⟩⟩
  · have hr : rank (right h e)<k := by tauto
    exact ⟨⟨_,hr⟩,⟨_,Nat.le_of_not_gt hl⟩⟩

private theorem middle {A : Type} (f : A → ℕ) (a b c : A) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ∃ x y z : A, x≠y ∧ z≠y ∧ f x≤f y ∧ f y≤f z := by
  by_cases hab : f a≤f b
  · by_cases hbc : f b≤f c
    · exact ⟨a,b,c,ab,bc.symm,hab,hbc⟩
    · by_cases hac : f a≤f c
      · exact ⟨a,c,b,ac,bc,hac,by omega⟩
      · exact ⟨c,a,b,ac.symm,ab.symm,by omega,hab⟩
  · by_cases hac : f a≤f c
    · exact ⟨b,a,c,ab.symm,ac.symm,by omega,hac⟩
    · by_cases hbc : f b≤f c
      · exact ⟨b,c,a,bc,ac,hbc,by omega⟩
      · exact ⟨c,b,a,bc.symm,ab,by omega,by omega⟩

private theorem expand_cut {h n : ℕ} (rank : V (h+2) → ℕ)
    (lower : ∀ d : Bool × Bool, ∃ k, n+1 ≤ (rankCut (rank ∘ grandChild d) k).card) :
    ∃ k, n+2≤(rankCut rank k).card := by
  choose k good using lower
  obtain ⟨x,y,z,hxy,hzy,hlo,hhi⟩ := middle k (false,false) (false,true) (true,false)
    (by decide) (by decide) (by decide)
  obtain ⟨⟨u,hu⟩,_⟩ := cut_sides ((Nat.zero_lt_succ n).trans_le (good x))
  obtain ⟨_,⟨v,hv⟩⟩ := cut_sides ((Nat.zero_lt_succ n).trans_le (good z))
  have early : rank (grandChild x u)<k y := hu.trans_le hlo
  have late : ¬rank (grandChild z v)<k y := not_lt.mpr (hhi.trans hv)
  obtain ⟨e,he,outside⟩ := crossing_outside (fun p=>rank p<k y) hxy hzy early late
  let emb : E h ↪ E (h+2) := ⟨grandEdge y,grandEdge_injective y⟩
  let S := (rankCut (rank ∘ grandChild y) (k y)).map emb
  have subset : S ⊆ rankCut rank (k y) := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp ht
    exact (mem_rankCut _).mpr ((mem_rankCut (rank:=rank ∘ grandChild y) s).mp hs)
  have fresh : e ∉ S := by
    intro he
    obtain ⟨s,_,hs⟩ := Finset.mem_map.mp he
    exact outside ⟨s,hs⟩
  have extra : insert e S ⊆ rankCut rank (k y) :=
    Finset.insert_subset ((mem_rankCut e).mpr he) subset
  have cardinal := Finset.card_le_card extra
  simp only [Finset.card_insert_of_notMem fresh, S, Finset.card_map] at cardinal
  exact ⟨k y, (Nat.succ_le_succ (good y)).trans cardinal⟩

private theorem rankCut_odd (n : ℕ) (rank : V (2*n+1) → ℕ) (inj : Function.Injective rank) :
    ∃ k, n+1 ≤ (rankCut rank k).card := by
  induction n with
  | zero =>
    let e : E 1 := rootEdge false
    have diff : rank (left 1 e) ≠ rank (right 1 e) := fun he => left_ne_right 1 e (inj he)
    let k := max (rank (left 1 e)) (rank (right 1 e))
    have mem : e∈rankCut rank k := by
      apply (mem_rankCut e).mpr
      dsimp [k]
      omega
    exact ⟨k,Finset.card_pos.mpr ⟨e,mem⟩⟩
  | succ n ih =>
    apply expand_cut (h:=2*n+1) rank
    intro d
    exact ih (rank ∘ grandChild d) (inj.comp (grandChild_injective d))

/-- For each pair of levels above the first edge, every ordering has an
additional crossing edge at some cut. -/
theorem not_cutwidth_odd (n : ℕ) : ¬ (graph (2*n+1)).CutwidthAtMost n := by
  rintro ⟨ord,cap⟩
  obtain ⟨k,hk⟩ := rankCut_odd n (fun v=>(ord v).val) (fun _ _ h=>ord.injective (Fin.ext h))
  have bound : (rankCut (fun v=>(ord v).val) k).card≤n := cap k
  omega

private theorem rankCut_height {n h : ℕ} (depth : 2*n+1≤h) :
    ∀ rank : V h → ℕ, Function.Injective rank → ∃ k, n+1≤(rankCut rank k).card := by
  induction depth with
  | refl => exact rankCut_odd n
  | @step h prior ih =>
    intro rank inj
    have vertexInj : Function.Injective (child (h:=h) false) := by
      intro u v eqn
      have pair : (false,u) = (false,v) := Option.some.inj eqn
      exact congrArg Prod.snd pair
    let emb : E h ↪ E (h+1) := ⟨childEdge false,by
      intro u v eqn
      have pair : (false,u) = (false,v) := Sum.inr.inj eqn
      exact congrArg Prod.snd pair⟩
    obtain ⟨k,hk⟩ := ih (rank ∘ child false) (inj.comp vertexInj)
    have subset : (rankCut (rank ∘ child false) k).map emb ⊆ rankCut rank k := by
      intro t ht
      obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp ht
      exact (mem_rankCut _).mpr ((mem_rankCut (rank:=rank ∘ child false) e).mp he)
    exact ⟨k,hk.trans (by simpa only [Finset.card_map] using Finset.card_le_card subset)⟩

/-- Once the family index reaches this threshold, every vertex order has a
cut larger than the prescribed bound. -/
theorem log_cutwidth_gt {bound n : ℕ} (large : 2^(2*bound+1)≤n) :
    ¬ (graph (Nat.log 2 n)).CutwidthAtMost bound := by
  rintro ⟨ord,cap⟩
  obtain ⟨k,hk⟩ := rankCut_height (Nat.le_log_of_pow_le (by decide) large)
    (fun v=>(ord v).val) (fun _ _ he=>ord.injective (Fin.ext he))
  have boundAt : (rankCut (fun v=>(ord v).val) k).card≤bound := cap k
  omega

/-- The paper's height `⌊log₂ n⌋` gives unbounded cutwidth even after discarding
an arbitrary finite prefix of input lengths. -/
theorem log_cutwidth_unbounded (bound start : ℕ) :
    ∃ n, start≤n ∧ ¬ (graph (Nat.log 2 n)).CutwidthAtMost bound :=
  ⟨max start (2^(2*bound+1)),le_max_left _ _,log_cutwidth_gt (le_max_right _ _)⟩


end
end Hierarchy.BinaryTree

end OAI
