import OAI.Computability.NearSquareRoot.PhysicalWalshFrontBranch
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontClock
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSelector
import OAI.Computability.NearSquareRoot.PhysicalWalshXorInterior
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeConjugate

/-! # The canonical front XOR at all recursion depths

An inspection of the compact descriptor selects the elementary sweep on short
slots and the three-slot packed program once the recorded table reserve fits.
The complete arithmetic records are parked during this inspection.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh

/-- Both geometric implementations act on the same ordered physical lane.
One program handles every valid shape, with an input-dependent scan clock
and the fixed-degree arena of the recursive node. -/
theorem runs {ρ : ℝ} (lower : 1/2 < ρ) (upper : ρ ≤ 1) (a W : ℕ) (arity : 4 ≤ a) :
    ∃ D e : ℕ, ∀ d, e ≤ d →
      Route.FlatRun (W:=W) a (nodeScan a W d (FrontClock.extra (a+1) W ρ D))
        (nodeArena a W d) (xor a (Interior.axes a arity)) := by
  obtain ⟨D,packedDegree,packed⟩ := Interior.large lower upper a W arity
  obtain ⟨shortDegree,short⟩ := ElementarySweep.flatRuns a W
  obtain ⟨tagDegree,tag⟩ := selector a W D
  refine ⟨D,max packedDegree (max shortDegree tagDegree),fun d hd => ?_⟩
  have dp := (le_max_left ..).trans hd
  have ds := (le_max_left ..).trans ((le_max_right ..).trans hd)
  have dt := (le_max_right ..).trans ((le_max_right ..).trans hd)
  let g := Interior.axes a arity
  let P (x : XorInput W) := XorThreshold.cutoff D (Header.scale (a+1) x.shape) ≤ Interior.L (a+1) x.shape
  let T (x : XorInput W) := nodeScan a W d (FrontClock.extra (a+1) W ρ D) x.shape
  let S (x : XorInput W) := nodeArena a W d x.shape
  let q (x : XorInput W) := send (Header.wire (a+1) x.shape,laneFlat (a+1) W x.shape x.row)
  let r (x : XorInput W) := send (laneFlat (a+1) W x.shape (PhysicalWalshNode.xor a g x.shape x.row))
  let small := {x : XorInput W // ¬ P x}
  let large := {x : XorInput W // P x}
  have ne : g.1 ≠ g.2 := by intro h; have hv := congrArg Fin.val h; change 2=1 at hv; omega
  have sm : BoundedTask (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun x : small => q x.val) (r ∘ Subtype.val) := by
    have run := ((short d ds) g ne).on (fun x : small => x.val)
    apply run.conform _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro x
    have lo : ElementarySchedule.slotWidth (a+1) x.val.shape < XorThreshold.cutoff D (Header.scale (a+1) x.val.shape) :=
      Nat.lt_of_not_ge x.property
    simp only [T,Function.comp_apply,nodeScan,FrontClock.extra,ite_eq_left lo]
  have lg : BoundedTask (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun x : large => q x.val) (r ∘ Subtype.val) := by
    apply packed.mono
    · intro x
      have hi : ¬ ElementarySchedule.slotWidth (a+1) x.val.shape < XorThreshold.cutoff D (Header.scale (a+1) x.val.shape) :=
        Nat.not_lt.mpr x.property
      change allowance _ _ _ + Interior.extra _ _ _ _ ≤ nodeArena a W d _ + FrontClock.extra _ _ _ _ _
      rw [FrontClock.extra,ite_eq_right hi]
      exact Nat.add_le_add_right ((allowance_mono dp _).trans (le_max_left ..)) _
    · intro x
      exact (allowance_mono dp _).trans (le_max_left ..)
  obtain ⟨c,hc⟩ := sm
  obtain ⟨b,hb⟩ := lg
  have branch : BoundedTask T S (fun x => .fork (.atom (decide (P x))) (q x)) r :=
    ⟨decodeBit c b,chooseNamed P hc hb⟩
  have tagRun : BoundedTask T S q (fun x => .fork (.atom (decide (P x))) (q x)) :=
    (tag d dt).mono (fun _ => (le_max_left ..).trans (Nat.le_add_right ..)) (fun _ => le_max_left ..)
  change BoundedTask T S q r
  exact (tagRun.compose branch).bound 2 1 (fun x => by simp only [Nat.two_mul]; omega) (fun _ => by simp)

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
