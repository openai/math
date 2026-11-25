import OAI.Hierarchy.DescentReentryCommonBlocks
import OAI.Hierarchy.DescentCommonGroups

namespace OAI
/-! # High and low surviving digits as the next group and physical block -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentHostDirectory DescentColonies StarKeys
open scoped Classical
noncomputable section
variable {F P J : Type} [Field F] [Fintype J] [DecidableEq J] {d k : ℕ} {bits : P→ℕ}
    {A : MarkedWorld F d P bits} {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T

def radix (a b : ℕ) := (finCongr (Nat.pow_add 2 a b)).trans finProdFinEquiv.symm
theorem radix_high (a b : ℕ) (x : Block (a+b)) : ((radix a b x).1).val=x.val/2^b := rfl
theorem radix_low (a b : ℕ) (x : Block (a+b)) : ((radix a b x).2).val=x.val%2^b := rfl
theorem radix_join (a b : ℕ) (c : Block a) (i : Block b) :
    ((radix a b).symm (c,i)).val=i.val+2^b*c.val := rfl

variable (digits : Block T.commonDepth ≃ J×Block k)
def groupPosition (v : (W).graph.Site) : J×↥(commonNames Z T) := ((digits (blockId Z T v)).1,placed Z T v)
def groupBlock (v : (W).graph.Site) : Block k := (digits (blockId Z T v)).2

omit [Fintype J] [DecidableEq J] in
theorem group_coordinates : Function.Injective (fun u : (W).graph.Site=>(groupPosition Z T digits u,groupBlock Z T digits u)) := by
  intro u v eqn
  let coords := (J × ↥(commonNames Z T)) × Block k
  exact place_unique Z T (congrArg (fun t : coords => t.1.2) eqn)
    (digits.injective (Prod.ext (congrArg (fun t : coords => t.1.1) eqn)
      (congrArg (fun t : coords => t.2) eqn)))

omit [Fintype J] [DecidableEq J] in
theorem group_fiber (v : (W).graph.Site) (j : J) (y : ↥(commonNames Z T)) (i : Block k) :
    groupPosition Z T digits v=(j,y) ∧ groupBlock Z T digits v=i ↔
    placed Z T v=y ∧ blockId Z T v=digits.symm (j,i) := by
  constructor
  · rintro ⟨p,lo⟩
    refine ⟨congrArg (fun t : J × ↥(commonNames Z T) => t.2) p,digits.injective ?_⟩
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (congrArg (fun t : J × ↥(commonNames Z T) => t.1) p) lo
  · rintro ⟨p,addr⟩
    simp [groupPosition,groupBlock,p,addr]

omit [Fintype J] in
theorem group_mass (load : (W).graph.Site→ℕ) (v : J×↥(commonNames Z T)) (i : Block k) :
    blockMass (W).graph (groupPosition Z T digits) (groupBlock Z T digits) load v i =
      blockMass (W).graph (placed Z T) (blockId Z T) load v.2 (digits.symm (v.1,i)) := by
  rcases v with ⟨j,v⟩
  unfold blockMass
  apply Finset.sum_congr rfl
  intro u _
  have fiber := group_fiber Z T digits u j v i
  by_cases found : placed Z T u = v ∧ blockId Z T u = digits.symm (j,i)
  · rw [ite_eq_left (fiber.mpr found),ite_eq_left found]
  · rw [ite_eq_right (fun hit => found (fiber.mp hit)),ite_eq_right found]

omit [Fintype J] [DecidableEq J] in
theorem group_peers (e : (W).graph.Edge) :
    groupPosition Z T digits ((W).graph.dst e)∈groupedNear (emittedNear Z T) (groupPosition Z T digits ((W).graph.src e)) ∧
    groupPosition Z T digits ((W).graph.src e)∈groupedNear (emittedNear Z T) (groupPosition Z T digits ((W).graph.dst e)) := by
  have same := congrArg (fun x=>(digits x).1) (block_edges Z T e)
  have fwd := emitted_edges Z T e
  have rev := (emitted_symmetric Z T _ _).mp fwd
  exact ⟨Finset.mem_map.mpr ⟨_,fwd,Prod.ext same rfl⟩,
    Finset.mem_map.mpr ⟨_,rev,Prod.ext same.symm rfl⟩⟩

omit [Fintype J] [DecidableEq J] in
theorem group_same (e : (W).graph.Edge) :
    groupBlock Z T digits ((W).graph.src e)=groupBlock Z T digits ((W).graph.dst e) :=
  congrArg (fun x=>(digits x).2) (block_edges Z T e)

omit [Fintype J] [DecidableEq J] in
theorem group_hub (v : J×↥(commonNames Z T)) (tag : commonTag Z T v.2=true) (i : Block k) :
    ∃u,groupPosition Z T digits u=v ∧ groupBlock Z T digits u=i := by
  obtain ⟨j,v⟩ := v
  obtain ⟨u,placed,old⟩ := hub_present Z T v tag (digits.symm (j,i))
  exact ⟨u,(group_fiber Z T digits u j v i).mpr ⟨placed,old⟩⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
