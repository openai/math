import OAI.Hierarchy.DescentTerminalBookBoardInput
import OAI.Hierarchy.DescentTerminalHeaderGroupSlots

namespace OAI
/-! # Reindexing the measured terminal directory into the real graph's two paid row orders -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalGrainProfiles DescentSortedRoster DescentTerminalPaidHeaderEvents DescentTerminalGraphPositions DescentTerminalCableOrder
open DescentTerminalRecipeRows DescentKernelHistory Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical
noncomputable section

variable {H D b p sites A:ℕ} {P:Type} [Fintype P] {bits:P→ℕ} (N:Network b P bits)
    (home:N.Site→Fin H) (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ)
    (ops:∀v,Boundary N v↪ℕ) (R:Fin H→Fin D→Option (Fin H))
    (hp:0<p) (edges:∀e,p∣N.width e) (ports:∀z,p∣bits z) (sorted:Sorted R)
    (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧ home (N.src e)∈present R (home (N.dst e)))
local notation "L" => order N home native p ext nodes ops
local notation "physical" => groupEmbed R N home native ext nodes ops hp covers

include sorted in
theorem same_socket (v:Fin H) (j k:Fin (D+1)) (tag:Option (Fin H))
    (hj:label R v j=some tag) (hk:label R v k=some tag) : j=k := by
  have l:=label_order R sorted v j k hj hk
  have r:=label_order R sorted v k j hk hj
  exact le_antisymm (le_of_not_gt (fun h=>lt_irrefl _ (r.mp h))) (le_of_not_gt (fun h=>lt_irrefl _ (l.mp h)))

/-- Every actual full boundary operand names one entry of the graph's catalog.
All the formulas for measuring a socket use this single equality. -/
def groupPart (v:Fin H) (n : Fin (((L).site v).nodes)) (j:Fin (((L).site v).arity n)) : Order.Group L v :=
  ((L).groups v).symm ((((L).site v).arg n j).1)
def atPart (v:Fin H) (n : Fin (((L).site v).nodes)) (j:Fin (((L).site v).arity n)) :
    Order.At L v (groupPart N home native ext nodes ops v n j) :=
  ((L).inGroup v _).symm ((((L).site v).arg n j).2)
theorem at_name (v:Fin H) (n:Fin (((L).site v).nodes)) (j:Fin (((L).site v).arity n)) :
    (atPart N home native ext nodes ops v n j).val=(L).args v n j := (L).catalog_arg v n j

variable (i:Fin H) (rows:Directory (D+1) sites A)

set_option maxHeartbeats 800000 in
include edges ports sorted covers in
def aligned (chart : Order.Nodes L i ↪ Fin sites)
    (nodeOrder : ∀ u v : Order.Nodes L i, (L).nodes i u < (L).nodes i v ↔ chart u < chart v)
    (recorded:∀j,rows.pieces j=grainCount (p:=p) R N home i j)
    (venue:∀v:Order.Nodes L i,rows.venue (chart v)=some (DescentTerminalGraphRows.arity N p v.val))
    (holes:∀c : Fin sites,(∀ v : Order.Nodes L i, chart v ≠ c)→ rows.venue c=none)
    (wire : ∀(n:Fin (((L).site i).nodes)) (j:Fin (((L).site i).arity n)) (a:Fin A),j.val=a.val→
      ∃(s:Fin (D+1)) (k:ℕ),
        label R i s=some (groupPart N home native ext nodes ops i n j).val ∧
        (Order.inGroup L i _ (atPart N home native ext nodes ops i n j)).val=k ∧
        rows.address (chart (((L).nodes i).symm n)) a=some (s,k)) :
    Aligned ((L).site i) rows := by
  let into:Fin (((L).site i).nodes)↪Fin sites:=(((L).nodes i).symm.toEmbedding).trans chart
  refine ⟨physical i,into,group_ascending R N home native ext nodes ops hp sorted covers i,?_,?_,?_,?_,?_,?_⟩
  · change ∀ ⦃u v : Fin (Fintype.card (Order.Nodes L i))⦄, u < v →
      chart (((L).nodes i).symm u) < chart (((L).nodes i).symm v)
    intro u v lt
    apply (nodeOrder (((L).nodes i).symm u) (((L).nodes i).symm v)).1
    rw [((L).nodes i).apply_symm_apply u, ((L).nodes i).apply_symm_apply v]
    exact lt
  · apply Finset.ext
    intro s
    constructor
    · intro hs
      have pos : 0 < rows.pieces s := (Finset.mem_filter.mp hs).2
      rw [recorded] at pos
      obtain ⟨g,hit⟩:=positive_group R N home native ext nodes ops hp i s pos
      apply Finset.mem_map.mpr
      refine ⟨(L).groups i g, Finset.mem_univ _, ?_⟩
      exact same_socket R sorted i _ s g.val
        (by
          change label R i (groupSlot R N home native ext nodes ops hp covers i
            (((L).groups i).symm (((L).groups i) g))) = some g.val
          rw [Equiv.symm_apply_apply]
          exact socket_name R N home native ext nodes ops hp covers i g) hit
    · intro hs
      obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change 0 < rows.pieces (physical i g)
      rw [recorded]
      let u:Order.Group L i:=((L).groups i).symm g
      have size:=grain_count_at R N home native ext nodes ops hp edges ports i u _
        (socket_name R N home native ext nodes ops hp covers i u)
      change 0<grainCount (p:=p) R N home i (groupSlot R N home native ext nodes ops hp covers i u)
      rw [size]
      obtain ⟨name,used,tag⟩:=u.property
      exact Fintype.card_pos_iff.mpr ⟨⟨name,used,tag⟩⟩
  · apply Finset.ext
    intro s
    simp only [Directory.activeNodes,occupied,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    constructor
    · intro pos
      by_contra no
      have empty := holes s (fun u h => no ⟨(L).nodes i u, by
        change chart (((L).nodes i).symm (((L).nodes i) u)) = s
        rw [((L).nodes i).symm_apply_apply]
        exact h⟩)
      simp [empty] at pos
    · rintro ⟨g,rfl⟩
      change (rows.venue (chart (((L).nodes i).symm g))).isSome = true
      rw [venue]
      rfl
  · intro g
    rw [recorded]
    exact grain_count_at R N home native ext nodes ops hp edges ports i (((L).groups i).symm g) _
      (socket_name R N home native ext nodes ops hp covers i (((L).groups i).symm g))
  · intro v;exact venue (((L).nodes i).symm v)
  · intro n j a eqn
    obtain ⟨s,k,tag,offset,issued⟩:=wire n j a eqn
    have name:=socket_name R N home native ext nodes ops hp covers i (groupPart N home native ext nodes ops i n j)
    have loc:=same_socket R sorted i _ _ _ tag name
    refine issued.trans (congrArg some (Prod.ext loc ?_))
    exact offset.symm.trans (congrArg Fin.val (((L).inGroup i _).apply_symm_apply _))

/-- Smaller global graph degrees use the same four-column directory.
Unused high sockets have no purchased pieces. -/
def Directory.extend {K G V A:ℕ} (d:Directory K V A) (le:K≤G):Directory G V A where
  pieces s:=if h:s.val<K then d.pieces ⟨s.val,h⟩ else 0
  venue:=d.venue
  address n j:=(d.address n j).map (fun r=>(r.1.castLE le,r.2))

def Aligned.extend {K G V A:ℕ} {t:Site} {d:Directory K V A} (h:Aligned t d) (le:K≤G) :
    Aligned t (d.extend le) := by
  let cast : Fin K ↪ Fin G := Fin.castLEEmb le
  refine ⟨h.group.trans cast,h.node,fun a b lt=>h.groupOrder lt,h.nodeOrder,?_,h.nodeSet,?_,h.venue,?_⟩
  · have memGroups {k : ℕ} (d' : Directory k V A) (s : Fin k) : s ∈ d'.activeGroups ↔ 0 < d'.pieces s :=
      ⟨fun hs => (Finset.mem_filter.mp hs).2, fun pos => Finset.mem_filter.mpr ⟨Finset.mem_univ _,pos⟩⟩
    have small (s : Fin K) : 0 < d.pieces s ↔ ∃ g, h.group g = s := by
      have eqn := Finset.ext_iff.mp h.groupSet s
      simpa only [memGroups,Finset.mem_map,Finset.mem_univ,true_and] using eqn
    apply Finset.ext
    intro s
    rw [memGroups]
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Directory.extend]
    by_cases hs : s.val < K
    · rw [dite_eq_left hs,small]
      constructor
      · rintro ⟨g,eqn⟩
        exact ⟨g,Fin.ext (congrArg (fun z : Fin K => z.val) eqn)⟩
      · rintro ⟨g,eqn⟩
        exact ⟨g,Fin.ext (congrArg (fun z : Fin G => z.val) eqn)⟩
    · rw [dite_eq_right hs]
      constructor
      · intro pos; omega
      · rintro ⟨g,rfl⟩
        exact (hs (h.group g).isLt).elim
  · intro g
    simpa [Directory.extend,cast] using h.pieces g
  · intro v j a eqn
    simp only [Directory.extend,h.address v j a eqn,Option.map_some]
    rfl

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
