import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.Hierarchy.ProtocolRAMFrozenSeries

namespace OAI
/-! # Successive native publication regions for the authentic site and bank data -/

namespace Hierarchy.ProtocolRAM.WindowSeries
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open PhysicalProcedure
open scoped BigOperators

variable {W m : ℕ}

/-- Every phase gets the same public stride. Taking the sum of the concrete local
window sizes gives enough room at every row and costs a fixed calendar factor. -/
def width (needs : Fin (m+1)→ℕ) := ∑j,needs j
def start (floor : ℕ) (needs : Fin (m+1)→ℕ) (j : Fin (m+1)) := floor+j.val*width needs
def finish (floor : ℕ) (needs : Fin (m+1)→ℕ) := floor+(m+1)*width needs

theorem before (floor : ℕ) (needs : Fin (m+1)→ℕ) {i j : Fin (m+1)} (lt : i<j) :
    start floor needs i+needs i ≤ start floor needs j := by
  have part : needs i ≤ width needs := Finset.single_le_sum (fun z _=>Nat.zero_le (needs z)) (Finset.mem_univ i)
  have ord : i.val+1 ≤ j.val := lt
  have step := Nat.mul_le_mul_right (width needs) ord
  simp only [Nat.add_mul,one_mul] at step
  dsimp [start]
  omega

theorem within (floor : ℕ) (needs : Fin (m+1)→ℕ) (j : Fin (m+1)) :
    start floor needs j+needs j ≤ finish floor needs := by
  have part : needs j ≤ width needs := Finset.single_le_sum (fun z _=>Nat.zero_le (needs z)) (Finset.mem_univ j)
  have ord : j.val+1 ≤ m+1 := j.isLt
  have step := Nat.mul_le_mul_right (width needs) ord
  simp only [Nat.add_mul,one_mul] at step
  dsimp [start,finish]
  rw [Nat.add_mul,one_mul]
  omega

theorem bound (floor k n : ℕ) (needs : Fin (m+1)→ℕ) (work : ∀j,needs j ≤ k*n) :
    finish floor needs ≤ floor+((m+1)*(m+1)*k)*n := by
  have price : width needs ≤ (m+1)*(k*n) := by
    simpa [width] using (Finset.sum_le_sum (s:=Finset.univ) (fun (j : Fin (m+1)) _=>work j))
  dsimp [finish]
  simpa only [Nat.mul_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_left (m+1) price) floor

/-- The side condition to run a native pass only reads the original rows below
the base. Earlier format observations survive all later genuine writes. -/
theorem run (floor : ℕ) (needs : Fin (m+1)→ℕ) (phase : Fin (m+1) → Procedure W)
    (ticks : Fin (m+1)→ℕ) (m₀ : Memory W)
    (board : Fin (m+1)→ℕ → Prop) (cell : Fin (m+1)→ℕ → Word W → Prop)
    (inside : ∀j u,board j u → u<start floor needs j+needs j)
    (perform : ∀j s,(∀u<floor,s u=m₀ u)→∃t,(phase j).Exec s t (ticks j) ∧
      (∀u,board j u → cell j u (t u)) ∧ ∀u<start floor needs j,t u=s u) :
    ∃out,(ProcedureBank.program m phase).Exec m₀ out (∑j,ticks j) ∧
      (∀j u,board j u → cell j u (out u)) ∧ ∀u<floor,out u=m₀ u := by
  let ready (s : Memory W) := ∀u<floor,s u=m₀ u
  obtain ⟨out,ran,_,fields,safe⟩ := ProtocolRAMFrozenSeries.run_observed m phase m₀ ready
    (fun u=>u<floor) board cell ticks (fun _ _=>rfl) (by
      intro j s ok
      obtain ⟨t,exec,reads,frame⟩ := perform j s ok
      have first : floor ≤ start floor needs j := Nat.le_add_right _ _
      exact ⟨t,exec,fun u hu=>(frame u (hu.trans_le first)).trans (ok u hu),reads,
        fun u hu=>frame u (hu.trans_le first),fun i lt u seen=>frame u ((inside i u seen).trans_le (before floor needs lt))⟩)
  exact ⟨out,ran,fields,safe⟩

end Hierarchy.ProtocolRAM.WindowSeries

end OAI
