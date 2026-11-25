import OAI.Hierarchy.ProbeFeed

namespace OAI
/-! # Undelivered integer stock on the public injection and release meshes -/
namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe

/-- The permanent saved RAM word is the whole original reserve. Only its
undelivered prefix complement is still held at calendar boundary `j`. -/
def held (steps bits j : ℕ) := bits-delivered steps bits (min j steps)

theorem held_step (steps bits j : ℕ) :
    held steps bits j=held steps bits (j+1)+(if j<steps then slice steps bits j else 0) := by
  by_cases live : j<steps
  · have last : delivered steps bits steps=bits := by
      have pos : 0<steps := by omega
      simp [delivered,pos.ne']
    have bound : delivered steps bits (j+1)≤bits :=
      (delivered_monotone steps bits (show j+1≤ steps by omega)).trans_eq last
    have order : delivered steps bits j ≤ delivered steps bits (j+1) :=
      delivered_monotone steps bits (Nat.le_succ j)
    simp only [held,Nat.min_eq_left (Nat.le_of_lt live),Nat.min_eq_left (show j+1≤ steps by omega),
      ite_eq_left live,slice]
    exact (Nat.sub_add_sub_cancel bound order).symm
  · have late : steps≤j := Nat.le_of_not_gt live
    simp [held,late,Nat.min_eq_right (late.trans (Nat.le_succ j)),live]

theorem held_start (steps bits : ℕ) : held steps bits 0=bits := by simp [held,delivered]

theorem held_finish (steps bits : ℕ) (hsteps : 0<steps) : held steps bits steps=0 := by
  simp [held,delivered,hsteps.ne']

end Hierarchy.ProtocolRAM.Calendar

end OAI
