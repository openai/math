import OAI.Computability.BorderVNP.CellProfileGenerator
import OAI.Computability.BorderVNP.CellPrefixCost

/-!
# Private execution budget of the profile checker

The estimates count the encoded lengths of the stack scans, including temporary
addresses. The number of loop iterations is separate from the length of the public
loop body. Only bits of the actual selector, cable ranges and auxiliary bank are read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix CellMacro

/-- Bounds on the actual physical wires read by this one profile. All count flags
are in the stated rectangular slabs. Route terms can be out of range on malformed
metadata, so their syntactic flag reads are bounded explicitly as well. -/
structure ReadBound (base off copies : ℕ) (s : CellSparse.Port) (w terms : ℕ) (routes : List Route)
    (A : ℕ) : Prop where
  /-- Reads of all original selector bits. -/
  selector : ∀ i < copies, ∀ k < w, off+s.atBit i k ≤ A
  /-- Reads in the auxiliary slabs initialized by the profile. -/
  flags : ∀ t < terms, ∀ i ≤ copies, ∀ k ≤ copies, address (termBase base copies t) copies i k ≤ A
  /-- Actual reads in each fixed route body, including rejected records. -/
  lanes : ∀ r ∈ routes, ∀ i < copies, ∀ k ≤ copies, ∀ j < r.lanes,
    off+r.original.atBit i j ≤ A ∧ off+r.compact.atBit k j ≤ A ∧
      address (termBase base copies r.term) copies i k ≤ A

private theorem wordIs_nodes (as : List NatExpr) (j : ℕ) : (wordIs as j).nodes = 10*as.length+1 := by
  induction as generalizing j with
  | nil => rfl
  | cons a as ih =>
    simp only [wordIs,Term.nodes,Term.nodes_equal,List.length_cons]
    rw [ih]; omega

private theorem wordIs_bounded (as : List NatExpr) (j : ℕ) (e : List ℕ) (A : ℕ)
    (h : ∀ a ∈ as, a.eval e ≤ A) : (wordIs as j).Bounded e A := by
  induction as generalizing j with
  | nil => trivial
  | cons a as ih =>
    refine ⟨?_, ih _ (fun x hx => h _ (.tail _ hx))⟩
    rw [Term.bounded_equal]
    exact ⟨h _ List.mem_cons_self,trivial⟩

@[simp] theorem selectTerm_nodes (off : ℕ) (s : CellSparse.Port) (w t : ℕ) (i : NatExpr) :
    (selectTerm off s w t i).nodes = 10*w+1 := by simp [selectTerm,wordIs_nodes]

/-- The match term reads only the declared selector lanes. -/
theorem selectTerm_bounded (off : ℕ) (s : CellSparse.Port) (w t : ℕ) (i : NatExpr) (e : List ℕ)
    (A : ℕ) (h : ∀ k < w, off+s.atBit (i.eval e) k ≤ A) : (selectTerm off s w t i).Bounded e A := by
  apply wordIs_bounded
  intro a ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  exact h k (List.mem_range.mp hk)

/-- A bound for the number of nodes in every expression guarded by a profile record. -/
def maxNodes (w terms : ℕ) := (40*w+40)*(terms+1)

/-- The selector-range guard for each copy reads a disjunction of the allowed codes. -/
theorem rangeGen_work_le (off copies : ℕ) (s : CellSparse.Port) (w terms : ℕ) (e : List ℕ) (A : ℕ)
    (h : ∀ i < copies, ∀ k < w, off+s.atBit i k ≤ A) :
    work (rangeGen off copies s w terms) e ≤ copies*guardCost A (maxNodes w terms) := by
  apply work_loop_le
  intro i hi
  apply Term.work_guard_le
  · apply Term.bounded_any
    intro v hv
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hv
    apply selectTerm_bounded
    exact h i hi
  · rw [Term.nodes_any, List.length_map, List.length_range]
    have hh := sum_map_le ((List.range terms).map fun t => selectTerm off s w t (.index 0)) Term.nodes
      (10*w+1) (fun v hv => by obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv; simp)
    simp only [List.length_map,List.length_range] at hh
    unfold maxNodes
    nlinarith

/-- One term's rectangular prefix table and its final histogram comparison. -/
theorem termGen_work_le (base off copies : ℕ) (s : CellSparse.Port) (w terms t adv : ℕ) (e : List ℕ)
    (A : ℕ) (hs : ∀ i < copies, ∀ k < w, off+s.atBit i k ≤ A)
    (hf : ∀ i ≤ copies, ∀ k ≤ copies, address (termBase base copies t) copies i k ≤ A) :
    work (termGen base off copies s w t adv) e ≤ ((copies+1)*(copies+1)+1)*guardCost A (maxNodes w terms) := by
  rw [termGen,work_seq]
  have h := generator_work_le (termBase base copies t) copies copies A (maxNodes w terms)
    (selectTerm off s w t) e (fun i hi => selectTerm_bounded _ _ _ _ _ _ _ (hs i hi))
    (by rw [selectTerm_nodes]; unfold maxNodes; nlinarith) hf
  have hz : work ((if adv ≤ copies then flagTerm (termBase base copies t) copies (.lit copies) (.lit adv)
      else .lit false).guard) e ≤ guardCost A (maxNodes w terms) := by
    split <;> rename_i ha <;> apply Term.work_guard_le
    · exact hf copies le_rfl adv ha
    · simp [maxNodes]; nlinarith
    · trivial
    · simp [Term.nodes,maxNodes]; nlinarith
  rw [Nat.succ_mul]
  omega

/-- Rank-mediated lane comparisons use one guard per copy, count candidate and lane. -/
theorem routeGen_work_le (base off copies : ℕ) (s : CellSparse.Port) (w terms : ℕ) (r : Route)
    (e : List ℕ) (A : ℕ) (hs : ∀ i < copies, ∀ k < w, off+s.atBit i k ≤ A)
    (hf : ∀ i < copies, ∀ k ≤ copies, ∀ j < r.lanes, off+r.original.atBit i j ≤ A ∧
      off+r.compact.atBit k j ≤ A ∧ address (termBase base copies r.term) copies i k ≤ A) :
    work (routeGen base off copies s w terms r) e ≤
      (1+copies*(copies+1)*r.lanes)*guardCost A (maxNodes w terms) := by
  let C := guardCost A (maxNodes w terms)
  rw [routeGen, work_seq]
  have hg : work (Term.lit (decide (r.term < terms))).guard e ≤ C :=
    Term.work_guard_le _ _ trivial (by simp [Term.nodes,maxNodes]; nlinarith)
  have hloop := work_loop_le (.lit copies) _ e ((copies+1)*(r.lanes*C)) (fun i hi =>
    work_loop_le (.lit (copies+1)) _ (i::e) (r.lanes*C) (fun k hk =>
      work_loop_le (.lit r.lanes) _ (k::i::e) C (fun j hj =>
        show work (laneTest base off copies s w r).guard (j::k::i::e) ≤ C from by
          change k < copies+1 at hk
          obtain ⟨ha,hb,hc⟩ := hf i hi k (by omega) j hj
          apply Term.work_guard_le
          · simp only [laneTest,Term.implies,Term.Bounded,Term.bounded_equal,bounded_flagTerm,
              portExpr,NatExpr.eval,Port.eval_expr,List.getD_cons_zero,List.getD_cons_succ]
            exact ⟨⟨selectTerm_bounded off s w r.term (.index 2) (j::k::i::e) A (hs i hi),hc⟩,ha,hb⟩
          · simp only [laneTest,Term.implies,Term.nodes,Term.nodes_equal,selectTerm_nodes,nodes_flagTerm]
            unfold maxNodes; nlinarith)))
  change work _ e ≤ copies*((copies+1)*(r.lanes*C)) at hloop
  change _ + _ ≤ (1+copies*(copies+1)*r.lanes)*C
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc]
  omega

/-- Uniform private clock bound for one whole profile. The read span `A` includes
the named ports and the guessed count tables. -/
theorem profileGen_budget_le (base off copies : ℕ) (s : CellSparse.Port) (w : ℕ) (hist : List ℕ)
    (routes : List Route) (e : List ℕ) (A L : ℕ) (hA : ReadBound base off copies s w hist.length routes A)
    (hL : ∀ r ∈ routes, r.lanes ≤ L) :
    budget ((profileGen base off copies s w hist routes).expand e) ≤
      5*(copies + hist.length*((copies+1)*(copies+1)+1) + routes.length*(1+copies*(copies+1)*L))*
        guardCost A (maxNodes w hist.length)+2 := by
  let C := guardCost A (maxNodes w hist.length)
  have hx := rangeGen_work_le off copies s w hist.length e A hA.selector
  have ht := sum_map_le hist.zipIdx (fun p => work (termGen base off copies s w p.2 p.1) e)
    (((copies+1)*(copies+1)+1)*C) (fun p hp => by
      have hh := List.mem_zipIdx_iff_getElem?.mp hp
      obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp hh
      exact termGen_work_le base off copies s w hist.length p.2 p.1 e A hA.selector (hA.flags p.2 hi))
  have hr := sum_map_le routes (fun r => work (routeGen base off copies s w hist.length r) e)
    ((1+copies*(copies+1)*L)*C) (fun r h => (routeGen_work_le base off copies s w hist.length r e A
      hA.selector (hA.lanes r h)).trans (Nat.mul_le_mul_right C (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (hL r h)) 1)))
  have hb := budget_le ((profileGen base off copies s w hist routes).expand e)
  change _ ≤ 5*work (profileGen base off copies s w hist routes) e+2 at hb
  simp only [profileGen,work_seq,work_sequence,List.map_map,Function.comp_def] at hb
  simp only [List.length_zipIdx] at ht
  change _ ≤ copies*C at hx
  change _ ≤ 5*(copies+hist.length*((copies+1)*(copies+1)+1)+routes.length*(1+copies*(copies+1)*L))*C+2
  apply hb.trans
  rw [Nat.mul_assoc, Nat.add_mul, Nat.add_mul, Nat.mul_assoc hist.length, Nat.mul_assoc routes.length]
  omega

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
