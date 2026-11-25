import OAI.Hierarchy.TaggedWidePortPartition
import OAI.Hierarchy.TaggedWideOverlap
import OAI.Hierarchy.ProbeBroadcastReadout
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # Fixed role pairs compare precisely the passive factor of the signed pass -/
noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open LinearAlgebra.SpectralBooks ChordGraph ThreeFlat Routing
open scoped Classical BigOperators

variable {P I J : Type*} {W : ℕ}

def Parts.view {t : P→ℕ} (o : Parts P I W t) (low : P→ℕ) (i : I) : Slice :=
  ⟨o.base i,o.width i,(o.owner i).elim 0 low⟩

variable (pass old new : P→ℕ) (l : Parts P I W fun p=>pass p+old p) (r : Parts P J W fun p=>pass p+new p)
    (x : I → Bits W) (y : J → Bits W)
    (a b : P→ℕ → Bool)
    (source : ∀i p,l.owner i=some p→∀u : Fin (l.width i),x i (u.castLE (l.within i))=a p (l.base i+u.val))
    (target : ∀i p,r.owner i=some p→∀u : Fin (r.width i),y i (u.castLE (r.within i))=b p (r.base i+u.val))

include source target in
theorem passive_iff :
    (∀i j t (u : Fin (l.width i)) (v : Fin (r.width j)),∀p,l.owner i=some p → r.owner j=some p→
      l.base i+u.val=t+old p → r.base j+v.val=t+new p → x i (u.castLE (l.within i))=y j (v.castLE (r.within j))) ↔
    ∀p (t : Fin (pass p)),a p (t.val+old p)=b p (t.val+new p) := by
  constructor
  · intro eqn p t
    obtain ⟨i,hi,u,hu⟩ := l.covers p ⟨t.val+old p,Nat.add_lt_add_right t.isLt _⟩
    obtain ⟨j,hj,v,hv⟩ := r.covers p ⟨t.val+new p,Nat.add_lt_add_right t.isLt _⟩
    have res := eqn i j t.val u v p hi hj hu hv
    simpa only [source i p hi,target j p hj,hu,hv] using res
  · intro eqn i j t u v p hi hj hu hv
    have fit := l.top i p hi
    have low := u.isLt
    have used : t<pass p := by omega
    simpa only [source i p hi,target j p hj,hu,hv] using eqn p ⟨t,used⟩

/-- Reading the high passive fields of the actual native aggregate is
equivalent to equality in ChordGraph.State. The ordering of the active
sublanes is independent on the two sides. -/
theorem passive_state {S : ℕ} (s : Fin S) (rest before after : Widths S)
    (u : State (rest+before) s) (v : State (rest+after) s) :
    (∀(p : (portGraph S).Port s) (t : Fin (rest p.val.1)),
      (u p).val.testBit (t.val+before p.val.1)=(v p).val.testBit (t.val+after p.val.1)) ↔
    (splitPortState rest before s u).1=(splitPortState rest after s v).1 := by
  let : Nonempty (Fin S) := ⟨s⟩
  constructor
  · intro heard
    funext p
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases small : j<rest p.val.1
    · have positions : (u p).val.testBit (before p.val.1+j)=(v p).val.testBit (after p.val.1+j) := by
        simpa only [Nat.add_comm (before p.val.1) j,Nat.add_comm (after p.val.1) j] using heard p ⟨j,small⟩
      exact (Probe.split_payload_bit rest before s u p j).trans
        (positions.trans (Probe.split_payload_bit rest after s v p j).symm)
    · have l := ((splitPortState rest before s u).1 p).isLt
      have r := ((splitPortState rest after s v).1 p).isLt
      have beyond : rest p.val.1 ≤ j := Nat.le_of_not_gt small
      rw [Nat.testBit_eq_false_of_lt (l.trans_le (Nat.pow_le_pow_right (by decide) beyond)),
          Nat.testBit_eq_false_of_lt (r.trans_le (Nat.pow_le_pow_right (by decide) beyond))]
  · intro eqn p j
    have bit := congrArg (fun f=>((f p).val).testBit j.val) eqn
    have positions := (Probe.split_payload_bit rest before s u p j.val).symm.trans
      (bit.trans (Probe.split_payload_bit rest after s v p j.val))
    simpa only [Nat.add_comm (before p.val.1) j.val,Nat.add_comm (after p.val.1) j.val] using positions

end Hierarchy.Tagged.PassiveWindow

end
end OAI
