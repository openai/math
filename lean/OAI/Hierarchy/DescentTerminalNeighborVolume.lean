import OAI.Hierarchy.DescentTerminalNeighborGrains
import OAI.Hierarchy.DescentTerminalNeighborCalendar

namespace OAI
/-! # The sum of the actual signed cell counters measures an entire canonical host pair -/

namespace Hierarchy.DescentTerminalGrainProfiles
open DescentSixParty DescentSharedCableNames DescentCompiler DescentColonies DescentTerminalCableOrder
open scoped Classical BigOperators
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
    (hosts : V↪Fin H)
local notation "B" => Stage.source A native
local notation "atH" => hosts ∘ Prod.snd ∘ A.pos

private theorem same_group (e : W.graph.Edge) : (A.pos (W.graph.src e)).1=(A.pos (W.graph.dst e)).1 := by
  obtain ⟨u,_,eqn⟩:=Finset.mem_map.mp (A.peers e).1
  have group := congrArg Prod.fst eqn
  exact group

/-- A true pair has exactly one location (group, inherited block) for each coarse grain. -/
theorem parallel_at (lo hi:V) (g:J) (x:Block k) (z:Stage.Grain A) :
    Stage.stream A native z∈(B).parallel ((g,lo),x) ((g,hi),x) ↔
      (A.pos (W.graph.src z.1)).1=g ∧ A.block (W.graph.src z.1)=x ∧
      pairIndex W.graph atH z.1=pair (hosts lo) (hosts hi) := by
  have grp:=same_group A z.1
  have blk:=A.same z.1
  simp only [Ends.parallel,Finset.mem_filter,Finset.mem_univ,true_and,Stage.source,Equiv.symm_apply_apply,
    Stage.home,Prod.ext_iff,pairIndex,pair_iff]
  grind

theorem coarse_count (lo hi:V) :
    (∑g:J,∑x:Block k,((B).parallel ((g,lo),x) ((g,hi),x)).card)=
      ∑e:W.graph.Edge,if pairIndex W.graph atH e=pair (hosts lo) (hosts hi) then A.grainCount e else 0 := by
  let f (g:J) (x:Block k) (t:Fin (Fintype.card (Stage.Grain A))) :=
    if t∈(B).parallel ((g,lo),x) ((g,hi),x) then 1 else 0
  have count (g:J) (x:Block k) : ((B).parallel ((g,lo),x) ((g,hi),x)).card=∑u:Stage.Grain A,f g x (Stage.stream A native u) := by
    rw [(Stage.stream A native).sum_comp]
    simp [f]
  simp_rw [count]
  rw [show (∑g:J,∑x:Block k,∑u:Stage.Grain A,f g x (Stage.stream A native u))=
      ∑u:Stage.Grain A,∑g:J,∑x:Block k,f g x (Stage.stream A native u) by
    simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Block k)) (t:=Finset.univ (α:=Stage.Grain A))]
    rw [Finset.sum_comm]]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  by_cases used:pairIndex W.graph atH e=pair (hosts lo) (hosts hi)
  · have location (g : J) :
        (Finset.univ.filter fun x : Block k =>
          (A.pos (W.graph.src e)).1=g ∧ A.block (W.graph.src e)=x).card =
          if (A.pos (W.graph.src e)).1=g then 1 else 0 := by
      by_cases here : (A.pos (W.graph.src e)).1=g <;> simp [here,Finset.filter_eq]
    simp [f,parallel_at A native hosts,used,location]
  · simp [f,parallel_at A native hosts,used]

variable (S : AtomSchedule) (ready:A.StateBounds S i)

include S ready in
theorem purchased_chunks (lo hi:V) {p scale:ℕ} (hp:0<p) (whole:A.z*G.b=scale*p) :
    (∑g:J,∑x:Block k,((B).parallel ((g,lo),x) ((g,hi),x)).card)*scale=
      pairMass W.graph atH (pair (hosts lo) (hosts hi))/p := by
  rw [coarse_count A native hosts lo hi]
  have mass : pairMass W.graph atH (pair (hosts lo) (hosts hi))=
      (∑e:W.graph.Edge,if pairIndex W.graph atH e=pair (hosts lo) (hosts hi) then A.grainCount e else 0)*scale*p := by
    simp only [pairMass,Finset.sum_filter,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp [A.grainCount_fit S ready e,whole,Nat.mul_assoc]
  rw [mass,Nat.mul_div_cancel _ hp]

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
