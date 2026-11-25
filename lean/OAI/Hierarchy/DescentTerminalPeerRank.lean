import OAI.Hierarchy.DescentTerminalPeerKeySet
import OAI.Hierarchy.DescentTerminalCableSlots
import OAI.Hierarchy.DescentTerminalGraphPurchase

namespace OAI
/-! # A private operand's actual within-group ordinal from the two signed panels -/
namespace Hierarchy.DescentTerminalPeerChronology
open DescentPacking DescentSixParty DescentCompiler DescentSharedCableNames DescentOrderedWords DescentChosenRouter DescentColonies
open DescentPackedTicketChronology DescentTerminalGraphPositions DescentTerminalCableOrder Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {groups d k i Hn : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε:ℝ}
    (A : GroupStage W G price ε (Fin groups) V k)
    (hosts : V↪Fin Hn) (S : AtomSchedule) (ready : A.StateBounds S i)
    (native : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (named : SiteOrder A hosts) (sorted:SourceSorted W native)
local notation "home" => fun v : W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "serial" => DescentOrderedReset.grains W A.grainCount native
local notation "which" => pairIndex W.graph home

def keySet (one two:Fin Hn) :=
  ((Finset.univ.filter fun z:Stage.Grain A=>which z.1=pair one two).image
    (grainKey A hosts S ready native (min one.val two.val)))

include named sorted in
theorem rank (one two:Fin Hn) (z:Stage.Grain A) (hit:which z.1=pair one two) :
    ((keySet A hosts S ready native one two).filter (·<grainKey A hosts S ready native (min one.val two.val) z)).card=
      (∑e∈Finset.univ.filter (fun e=>which e=pair one two ∧ native e<native z.1),A.grainCount e)+z.2.val := by
  let code:=grainKey A hosts S ready native (min one.val two.val)
  let keep (e:W.graph.Edge):=which e=pair one two
  have atEnd (v:Stage.Grain A) (live:keep v.1) :
      (home (W.graph.src v.1)).val=min one.val two.val ∨ (home (W.graph.src v.1)).val=max one.val two.val := by
    obtain ⟨a,_⟩|⟨a,_⟩:=(pair_iff ..).1 live
    all_goals rw [a];omega
  have cmp (x y:Stage.Grain A) (hx:keep x.1) (hy:keep y.1) :
      serial x<serial y ↔ code x<code y := by
    rw [earlier_grain]
    exact grain_order A hosts S ready native named sorted (min_le_max ..) x y (atEnd x hx) (atEnd y hy)
  let selected:=Finset.univ.filter fun v:Stage.Grain A=>keep v.1
  change ((selected.image code).filter (·<code z)).card=_
  rw [Finset.filter_image,Finset.card_image_of_injOn]
  · have cut : (selected.filter fun y=>code y<code z)=Finset.univ.filter
        (fun y:Stage.Grain A=>keep y.1 ∧ (native y.1<native z.1 ∨ y.1=z.1 ∧ y.2.val<z.2.val)) := by
      ext y
      simp only [selected,Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases hy:keep y.1
      · rw [←cmp y z hy hit,earlier_grain]
      · simp [hy]
    rw [cut,Finset.card_filter,Fintype.sum_sigma,Finset.sum_filter]
    have each (e:W.graph.Edge) := count_units A.grainCount (native.trans Fin.valEmbedding) keep z.1 e z.2 hit
    calc
      _ = ∑e:W.graph.Edge, ((if keep e ∧ native e<native z.1 then A.grainCount e else 0)+(if e=z.1 then z.2.val else 0)) := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [Function.Embedding.trans_apply, Fin.valEmbedding_apply, ← Fin.lt_def] at each
        convert each e using 1
        apply Finset.sum_congr rfl
        intro u _
        by_cases he:keep e <;> simp [he]
      _ = _ := by simp [Finset.sum_add_distrib,keep]
  · intro x hx y hy eqn
    have lx:keep x.1:=(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have ly:keep y.1:=(Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    apply (serial).injective
    have a:=cmp x y lx ly
    have b:=cmp y x ly lx
    exact le_antisymm (le_of_not_gt (fun h=>(b.mp h).ne eqn.symm)) (le_of_not_gt (fun h=>(a.mp h).ne eqn))

include ready in
theorem cable_units {p scale : ℕ} (hp:0<p) (whole:A.z*G.b=scale*p) (e:W.graph.Edge) :
    poolBatchCount (W.graph.width e) p=A.grainCount e*scale := by
  have word:W.graph.width e=(A.grainCount e*scale)*p:=by rw [A.grainCount_fit S ready e,whole,Nat.mul_assoc]
  have exactWidth:=DescentTerminalGraphVolume.exact_pieces p (W.graph.width e) hp
    (word ▸ dvd_mul_left p (A.grainCount e*scale))
  exact Nat.eq_of_mul_eq_mul_right hp (exactWidth.trans word)

variable [Fintype P] (external:P↪ℕ) (nodes:W.graph.Site↪ℕ) (ops:∀v,DescentKernelHistory.Boundary W.graph v↪ℕ)

include named sorted in
theorem group_slot {p scale:ℕ} (hp:0<p) (whole:A.z*G.b=scale*p) (one two:Fin Hn)
    (g:Order.Group (order W.graph home native p external nodes ops) one) (peer:g.val=some two)
    (nm:Order.At (order W.graph home native p external nodes ops) one g) (z:Stage.Grain A) (digit:Fin scale)
    (j:Fin (poolBatchCount (W.graph.width z.1) p)) (chunk:j.val=z.2.val*scale+digit.val) (label:nm.val=.inl ⟨z.1,j⟩) :
    (Order.inGroup (order W.graph home native p external nodes ops) one g nm).val=
      ((keySet A hosts S ready native one two).filter (·<grainKey A hosts S ready native (min one.val two.val) z)).card*
        scale+digit.val := by
  let L:=order W.graph home native p external nodes ops
  have truePair : Order.between L one two (.inl ⟨z.1,j⟩) := label ▸ ⟨nm.2.1,nm.2.2.trans peer⟩
  have hit:=(between_iff W.graph p L one two z.1 j).1 truePair
  rw [cable_local_ordinal W.graph home native external nodes ops one two g peer nm z.1 j label,
    rank A hosts S ready native named sorted one two z hit,chunk,Nat.add_mul,Finset.sum_mul]
  simp only [cable_units A S ready hp whole]
  omega

end
end Hierarchy.DescentTerminalPeerChronology

end OAI
