import OAI.Hierarchy.ProtocolRAMCalendarMesh
import OAI.Hierarchy.ProtocolRAMPrices
import Mathlib.Tactic

namespace OAI
/-! # Exact clocks for the injection, cooling and conditional reserve meshes -/

namespace Hierarchy.ProtocolRAM.Calendar
noncomputable section

/-- Payload injection holds time at one. The following cooling intervals
decrease it linearly to the prescribed endpoint. -/
def outerTime (c : Mesh) (finish : ℝ) (p : ℕ) : ℝ :=
  1-((p-c.inject:ℕ):ℝ)*(1-finish)/(c.cool:ℝ)

def reserveTime (c : Mesh) (finish : ℝ) (p j : ℕ) : ℝ :=
  outerTime c finish p/2 + (j:ℝ)*(outerTime c finish p/(2*c.reserveSteps))

def time (c : Mesh) (finish : ℝ) : Attempt→ℝ
  | .outer p _ => outerTime c finish p
  | .inner p _ j _ => reserveTime c finish p j

theorem injection_time (c : Mesh) (finish : ℝ) {p : ℕ} (inject : p≤c.inject) :
    outerTime c finish p=1 := by simp [outerTime,Nat.sub_eq_zero_of_le inject]

theorem cooling_end (c : Mesh) (finish : ℝ) (nonempty : 0<c.cool) :
    outerTime c finish (c.inject+c.cool)=finish := by
  have h : (c.cool:ℝ)≠0 := by exact_mod_cast nonempty.ne'
  simp only [outerTime,Nat.add_sub_cancel_left]
  field_simp [h]; ring

theorem cooling_increment (c : Mesh) (finish : ℝ) {p : ℕ} (past : c.inject≤p) :
    outerTime c finish (p+1)=outerTime c finish p-(1-finish)/(c.cool:ℝ) := by
  have eqn : p+1-c.inject=(p-c.inject)+1 := by omega
  simp only [outerTime,eqn,Nat.cast_add,Nat.cast_one]
  ring

theorem reserve_starts (c : Mesh) (finish : ℝ) (p : ℕ) :
    reserveTime c finish p 0=outerTime c finish p/2 := by simp [reserveTime]

theorem reserve_increment (c : Mesh) (finish : ℝ) (p j : ℕ) :
    reserveTime c finish p (j+1)=reserveTime c finish p j+outerTime c finish p/(2*c.reserveSteps) := by
  simp only [reserveTime,Nat.cast_add,Nat.cast_one]
  ring

theorem reserve_ends (c : Mesh) (finish : ℝ) (p : ℕ) (nonempty : 0<c.reserveSteps) :
    reserveTime c finish p c.reserveSteps=outerTime c finish p := by
  have h : (c.reserveSteps:ℝ)≠0 := by exact_mod_cast nonempty.ne'
  unfold reserveTime
  field_simp [h]; ring

/-- The lookup table fed to the signed stratum scanner evaluates the actual
stock at the time of the present chronological attempt. -/
def deadline (c : Mesh) (finish : ℝ) (base : PhasePrice) (a : Attempt) : PhasePrice :=
  {base with time:=time c finish a}

@[simp] theorem deadline_time (c : Mesh) (s : ℝ) (base : PhasePrice) (a : Attempt) :
    (deadline c s base a).time=time c s a := rfl


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
