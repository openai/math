import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.TaggedWideOriginalMount
import OAI.Hierarchy.TaggedWideProgramGates

namespace OAI
/-! # Both original RAM programs on their shared mounted header and paid read frontier -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideControlJoin ThreeFlat.RAM PhysicalProcedure Filter
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits : ℕ) {m : ℕ} (l : WideCPU.Layout m)
local notation "d" => 2^v.W
local notation "W" => wordBits h d copies
local notation "progs" => v.widePrograms h width bits l
local notation "times" => v.wideProgramTicks h width bits l
local notation "U" => l.pruneScratch+l.pruneRows+1
local notation "flag" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh

/-- This is the row extent of the larger of the two executions, including all
initial words and every observed paid output, even unused cells. -/
def wideGateRows (size : ℕ) := size+max (times.1+3+1) (times.2+3+U)

variable (N size : ℕ)
theorem wideGateRoom_of_rows (first : text progs.1≤N) (paid : text progs.2≤N)
    (enough : v.wideGateRows h width bits l size≤2^(2*h))
    (tall : max (N+3) (2*(rounds d+1)+3+rounds d*stride d copies)≤h) :
    v.GateRoom h width bits l size := by
  have wide : 2*h≤W := by rw [wordBits_linear]; omega
  have cap : 2^(2*h)≤2^W := Nat.pow_le_pow_right (by decide) wide
  have more : 2^W≤2^(W+1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ W)
  have rows : size+max (times.1+3+1) (times.2+3+U)≤2^W := enough.trans cap
  have ends : max (times.1+3+1) (times.2+3+U)≤2^W := (Nat.le_add_left ..).trans rows
  have firstEnd := (max_le_iff.mp ends).1
  have paidEnd := (max_le_iff.mp ends).2
  have feeHeight : N+3≤h := (le_max_left ..).trans tall
  have roomHeight : h≤W+1 := by omega
  have labels : N+3≤2^(W+1) :=
    (feeHeight.trans roomHeight).trans (Nat.lt_two_pow_self (n:=W+1)).le
  have txt₀ : progs.1.labels≤N := by unfold text at first; omega
  have txt₁ : progs.2.labels≤N := by unfold text at paid; omega
  exact ⟨by rw [wordBits_linear]; omega, (Nat.le_add_right ..).trans rows,
    (Nat.le_add_left ..).trans paidEnd, (Nat.add_le_add_right txt₀ 3).trans labels,
    (Nat.add_le_add_right txt₁ 3).trans labels, firstEnd.trans more, paidEnd.trans more⟩

/-- The two actual native CPU gates have exactly the same procedure, initial
words, clocks and address pins as the corresponding charged mounted gates. -/
theorem wide_mounted_pair (first : text progs.1≤N) (paid : text progs.2≤N)
    (cheap₀ : CheapCode progs.1) (cheap₁ : CheapCode progs.2)
    (enough : v.wideGateRows h width bits l size≤2^(2*h))
    (tall : max (N+3) (2*(rounds d+1)+3+rounds d*stride d copies)≤h) :
    let room:=v.wideGateRoom_of_rows h width bits l N size first paid enough tall
    ∃ a b : Mounted h N,
      (v.wideGates h width bits l size room)=(a.gate,b.gate) ∧
      a.rows=size+(times.1+3+1) ∧ b.rows=size+(times.2+3+U) := by
  let room:=v.wideGateRoom_of_rows h width bits l N size first paid enough tall
  have firstRows : size+(times.1+3+1)≤2^(2*h):=
    (Nat.add_le_add_left (le_max_left ..) size).trans enough
  have paidRows : size+(times.2+3+U)≤2^(2*h):=
    (Nat.add_le_add_left (le_max_right ..) size).trans enough
  let gate₀:=Mounted.original h d N size (times.1+3) 1 progs.1 (flag:Word W) 0
    (fun _=>(flag:Word W)) first cheap₀ firstRows tall
  let gate₁:=Mounted.original h d N size (times.2+3) U progs.2 ((l.pruneScratch+l.pruneRows):Word W) 0
    (Gate.denseAddr room.upper) paid cheap₁ paidRows tall
  exact ⟨gate₀,gate₁,rfl,rfl,rfl⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
