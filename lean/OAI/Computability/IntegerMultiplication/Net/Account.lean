import OAI.Computability.IntegerMultiplication.Net.Beat
import OAI.Computability.IntegerMultiplication.Net.Itinerary

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif.Beat
open Finset Place
variable {T C : Type} (z : Loom T C) (j : S) (p : Sub T) [DecidableEq T] (b : Bool)
theorem trail_eq (w : Local T C) :
    ((plans z j b).child p).trail w =
    [r0 z j p w, r1 z j p w, r2 z j p w, r3 z j p w, r4 z j p w, r5 z j p w,
        r6 z j p w, r7 z j p w, climax j p w] := by
  unfold Circuit.trail
  rw [show (fun e : Hop (Local T C) (Place T) => e.label w) =
    (fun l : Local T C → Place T => l w) ∘ Hop.label from rfl,
    ← List.map_map, flight]
  rfl

theorem start_eq (w : Local T C) : ((plans z j b).child p).init w = st j p w := rfl

-- simplify tactic used below
local macro "beat_simp" : tactic =>
  `(tactic| simp only [st, r0, r1, r2, r3, r4, r5, r6, r7, climax, repr])

theorem simple : ((plans z j b).child p).smooth (road (fun x y => z.near x y = true)) := by
  intro w
  rw [trail_eq, start_eq]
  rcases w with x|y|⟨u,v⟩|i
  all_goals
    beat_simp
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  · exact ⟨.still _, .still _, .entry .., .growX .., .still _, .still _, .still _, .still _, .finishX ..⟩
  · exact ⟨.still _, .fromY .., .still _, .still _, .still _, .growY .., .still _, .still _, .still _⟩
  · cases e : z.near u v
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨.still _, .still _, .still _, .still _, .still _, .still _, .still _, .still _, .skip⟩
    simp only [ite_true]
    exact ⟨.sideStart .., .still _, .side0 _ _ _ _ e, .still _, .still _, .core _ _ _ _ e, .still _, .sideDone .., .finishQ ..⟩
  exact ⟨.still _, .centerStart .., .still _, .centerGo .., .centerDrop .., .still _, .centerGo .., .still _, .finishQ ..⟩

-- accounting
def stageBill (h : ℤ) : Local T C → ℤ :=
  fun w => charge h (climax j p w) - charge h (st j p w) +
    repr (fun _ => if j.val=0 then 1 else 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 2*h) w

-- telescope for potential with 2 elementary lemmas
omit [DecidableEq T] in
theorem allow_rise (h : ℤ) (x y : Place T) (e : charge h x ≤ charge h y)
    (hok : isOp x = false) :
    allowance h x y = charge h y - charge h x := by simp [allowance, hok, abs_of_nonneg (sub_nonneg.mpr e)]

private theorem powers (h : ℤ) (hh : 2 ≤ h) (j : S) :
    1 ≤ h^j.val ∧ h^(j.val+1) ≤ h^3 ∧ h^j.val + h - 1 ≤ h^(j.val+1) := by
  have hp : 1 ≤ h^j.val := one_le_pow₀ (by omega)
  refine ⟨hp, pow_le_pow_right₀ (by omega) (show j.val+1 ≤ 3 by omega), ?_⟩
  rw [pow_succ]
  nlinarith

theorem detailed (h : ℤ) (hh : 2 ≤ h) (w : Local T C) :
    ((plans z j b).child p).cost (fun _ => allowance h) w = stageBill (C:=C) j p h w := by
  have ⟨hp,hb,hc⟩ := powers h hh j
  have hq : 1 ≤ h^3 := one_le_pow₀ (by omega)
  rw [Circuit.via, start_eq, trail_eq]
  unfold stageBill
  rcases w with x|y|⟨u,v⟩|i
  all_goals
    beat_simp
  · simp only [Circuit.toll, stay_allowance]
    unfold allowance
    cases e : (decide (j.val=0))
    · have e := of_decide_eq_false e
      simp [xEntry, charge, isOp, e] -- abs
      simp (disch := omega) only [abs_of_nonneg]
      linarith
    · have e := of_decide_eq_true e
      simp [xEntry, charge, isOp, e]
      simp (disch := omega) only [abs_of_nonneg]
      linarith
  · simp [Circuit.toll, allowance, charge, isOp]
    simp (disch := omega) only [abs_of_nonneg]; omega
  · cases e : z.near u v
    · simp [Circuit.toll, allowance, charge, isOp, abs_of_nonneg (show 0 ≤ h^3 by omega)]
    simp [Circuit.toll, allowance, charge, isOp]
    simp (disch := omega) only [abs_of_nonneg]; omega
  simp [Circuit.toll, allowance, charge, isOp]
  simp (disch := omega) only [abs_of_nonneg]; omega
end Net.Motif.Beat

end IntegerMultiplication
end Computability
end OAI
