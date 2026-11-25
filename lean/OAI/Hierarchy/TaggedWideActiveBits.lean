import OAI.Hierarchy.TaggedWidePassSites
import OAI.Hierarchy.ProbeBroadcastReadout

namespace OAI
/-! # Active ballot bits in a site-disjoint pass use the low original chord digits -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

variable {S n : ℕ}

theorem vacant_width (g : Widths S) (s : Fin S) (empty : Subsingleton (State g s))
    (p : (portGraph S).Port s) : g p.val.1=0 := by
  by_contra h
  have two : 1<2^(g p.val.1) := Nat.one_lt_two_pow (Nat.pos_of_ne_zero h).ne'
  let zero : State g s := fun _=>⟨0,Nat.two_pow_pos _⟩
  let one : State g s := Function.update zero p ⟨1,two⟩
  have eqn : zero p=one p := congrFun (empty.elim zero one) p
  have values := congrArg Fin.val eqn
  simp [zero,one] at values

/-- At a retained repair's party the active block is the only one with any
incident digits. The exposed low digit is consequently the physical digit
of its original chord, independent of the number of candidate rows. -/
theorem active_digit (rest : Widths S) (g : Fin n → Widths S) (j : Fin n) (s : Fin S)
    (away : ∀i,i≠j → Subsingleton (State (g i) s))
    (z : State (rest+∑i,g i) s) (p : (portGraph S).Port s) (b : Fin (g j p.val.1)) :
    ((blockPortState g s ((splitPortState rest (∑i,g i) s z).2) j p).val).testBit b.val=
      (z p).val.testBit b.val := by
  let : Nonempty (Fin S) := ⟨s⟩
  let e := p.val.1
  have none : (∑i : Fin j,g (Fin.castLE j.is_lt.le i) e)=0 :=
    Finset.sum_eq_zero fun i _=>vacant_width _ s (away _ (by
      intro h
      have eqn := congrArg Fin.val h
      have bound := i.isLt
      simp only [Fin.val_castLE] at eqn
      omega)) p
  have room : g j e ≤ (∑i,g i) e := by
    simpa only [Finsupp.finsetSum_apply] using (Finset.single_le_sum (f:=fun i=>g i e)
      (fun i _=>Nat.zero_le _) (Finset.mem_univ j))
  calc
    _ = (((splitPortState rest (∑i,g i) s z).2 p).val).testBit (b.val+∑i : Fin j,g (Fin.castLE j.is_lt.le i) e) :=
      blockWireIndex_testBit g e _ j b
    _ = _ := by
      rw [none,Nat.add_zero]
      exact Probe.split_selector_bit rest (∑i,g i) s z p (b.castLE room)

end Hierarchy.WireTelescope.PassMatrix

end
end OAI
