import OAI.Hierarchy.TaggedWideFullGates
import OAI.Hierarchy.TaggedWideMountedPair

namespace OAI
/-! # Mounting and pricing the enlarged dense paid trace on the parent circuit -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideControlJoin ThreeFlat.RAM PhysicalProcedure Filter
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (x : WideParent κ A) (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u)
  (δ ξ : ℝ) (unitCost : ℕ)
attribute [local irreducible] CheapCode widePrograms wideProgramTicks

section
variable (h width bits : ℕ) {j : ℕ} (layout : WideCPU.Layout j)
local notation "wbits" => wordBits h (2^v.W) copies
variable (suffix : Procedure (Native.wordBits h (2^v.W) Native.copies)) (bill endPos size N : ℕ)
local notation "baseProg" => v.widePrograms h width bits layout
local notation "baseTicks" => v.wideProgramTicks h width bits layout
local notation "keep" => layout.pruneScratch + layout.pruneRows
local notation "priorTop" => keep + 1
local notation "chartEnd" => max priorTop endPos
local notation "firstFuel" => (baseTicks).1 + 3
local notation "paidFuel" => (baseTicks).2 + bill + 3
local notation "flag" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh

set_option maxHeartbeats 1000000 in
private theorem appended_mounted_originals
    (firstCode : text (baseProg).1 ≤ N) (paidCode : text ((baseProg).2.seq suffix) ≤ N)
    (firstCheap : CheapCode (baseProg).1) (paidCheap : CheapCode ((baseProg).2.seq suffix))
    (enough : size + max (firstFuel + 1) (paidFuel + chartEnd) ≤ 2^(2*h))
    (tall : max (N+3) (2*(rounds (2^v.W)+1)+3+rounds (2^v.W)*stride (2^v.W) copies) ≤ h) :
    ∃ (lim : v.AppendedRoom h width bits layout suffix bill endPos size) (a b : Mounted h N),
      v.appendedGates h width bits layout suffix bill endPos size lim = (a.gate,b.gate) ∧
      a.rows = size+(firstFuel+1) ∧ b.rows = size+(paidFuel+chartEnd) := by
  have textOld : text (baseProg).2 ≤ N := by
    rw [text_seq] at paidCode
    exact (Nat.le_add_right ..).trans paidCode
  have oldRows : v.wideGateRows h width bits layout size ≤
      size + max (firstFuel+1) (paidFuel+chartEnd) := by
    apply Nat.add_le_add_left
    apply max_le_max_left
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.le_add_right _ bill) 3) (le_max_left ..)
  let prior := v.wideGateRoom_of_rows h width bits layout N size firstCode textOld (oldRows.trans enough) tall
  have wider : 2*h ≤ wbits := by rw [wordBits_linear]; omega
  have fits := enough.trans (Nat.pow_le_pow_right (by decide : 0<2) wider)
  have ends : max (firstFuel+1) (paidFuel+chartEnd) ≤ 2^wbits := (Nat.le_add_left ..).trans fits
  have paid := (max_le_iff.mp ends).2
  have feeHeight : N+3 ≤ h := (le_max_left ..).trans tall
  have labelCount : ((baseProg).2.seq suffix).labels ≤ N := by unfold text at paidCode; omega
  have heightRoom : h ≤ wbits+1 := by omega
  have textRoom := ((Nat.add_le_add_right labelCount 3).trans feeHeight).trans
    (heightRoom.trans (Nat.lt_two_pow_self (n:=wbits+1)).le)
  let lim : v.AppendedRoom h width bits layout suffix bill endPos size :=
    ⟨prior,(Nat.le_add_left ..).trans paid,textRoom,
      paid.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ wbits))⟩
  let a := Mounted.original h (2^v.W) N size firstFuel 1 (baseProg).1 (flag:Word wbits) 0
    (fun _ => (flag:Word wbits)) firstCode @firstCheap
    ((Nat.add_le_add_left (le_max_left ..) size).trans enough) tall
  let b := Mounted.original h (2^v.W) N size paidFuel chartEnd ((baseProg).2.seq suffix) (keep:Word wbits) 0
    (Gate.denseAddr lim.upper) paidCode @paidCheap
    ((Nat.add_le_add_left (le_max_right ..) size).trans enough) tall
  exact ⟨lim,a,b,rfl,rfl,rfl⟩
end

local notation "G" => v.wideDated x.h x.w ell unitCost
local notation "L" => v.wideInstalledLayout x m ell short u δ ξ unitCost G
local notation "S" => v.wideInstalledSize x m ell unitCost G
local notation "R" => v.wideInstalledRoot x
local notation "W" => wordBits x.h (2^v.W) copies
local notation "U" => (L).pruneScratch+(L).pruneRows+1
local notation "U'" => v.wideFullEnd x m ell short u δ ξ unitCost
local notation "old" => v.widePrograms x.h x.w v.maxBits L
local notation "oldTime" => v.wideProgramTicks x.h x.w v.maxBits L
local notation "full" => v.wideFullPrograms x m ell short u δ ξ unitCost
local notation "tt" => v.wideFullTicks x m ell short u δ ξ unitCost
local notation "C" => v.wideCorrectedSpillProgram x.h x.w ell unitCost v.maxBits R S ((G).romEnd R) ((G).workEnd S) U
local notation "fee" => v.wideCorrectedSpillTicks x.h x.w ell unitCost v.maxBits R S ((G).romEnd R) ((G).workEnd S) U
local notation "stop" => v.wideCorrectedSpillEnd x.h x.w ell unitCost v.maxBits R S ((G).romEnd R) ((G).workEnd S) U

def wideFullRows := S+max ((tt).1+3+1) ((tt).2+3+U')
local notation "rows" => v.wideFullRows x m ell short δ ξ unitCost (u:=u)

attribute [local irreducible] wideCorrectedSpillProgram wideCorrectedSpillTicks wideCorrectedSpillEnd
  wideInstalledLayout wideInstalledSize wideDated

set_option maxHeartbeats 4000000 in
/-- Fit the genuinely enlarged paid gate on the same finite signed input; its return
address remains the pruning flag and its observation list covers every spill shelf. -/
theorem wide_full_mounted_pair (N : ℕ) (code₀ : text (full).1≤N) (code₁ : text (full).2≤N)
    (cheap₀ : CheapCode (full).1) (cheap₁ : CheapCode (full).2)
    (enough : rows≤2^(2*x.h))
    (tall : max (N+3) (2*(rounds (2^v.W)+1)+3+rounds (2^v.W)*stride (2^v.W) copies)≤x.h) :
    ∃ (lim : v.FullGateRoom x m ell short u δ ξ unitCost) (a b : Mounted x.h N),
      v.wideFullGates x m ell short u δ ξ unitCost lim=(a.gate,b.gate) ∧
      a.rows=S+((tt).1+3+1) ∧ b.rows=S+((tt).2+3+U') := by
  exact appended_mounted_originals (v:=v) (h:=x.h) (width:=x.w) (bits:=v.maxBits)
    (layout:=L) (suffix:=C) (bill:=fee) (endPos:=stop) (size:=S) (N:=N)
    code₀ code₁ @cheap₀ @cheap₁ enough tall

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
