import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorSwap
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryPrefix

/-! # Charging a named compact-agenda prelude and its elementary bit passes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileElementaryRelease
open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode

/-- The volume of all records against which the per-bit scan is charged. -/
def area (A : ℕ) (s : Shape) := (count A s+1)*(s.w+1)

theorem area_le (a d : ℕ) (s : Shape) : area (a+1) s ≤ allowance (a+1) d s :=
  (Nat.mul_le_mul_left _ (show s.w+1 ≤ grow (a+1) s.level+s.w+1 by omega)).trans (Nat.le_add_right ..)

theorem power_le (a d : ℕ) (s : Shape) : (Header.scale (a+1) s+1)^d ≤ allowance (a+1) d s :=
  Nat.le_add_left ..

theorem laneSize (a W : ℕ) (s : Shape) (x : Data s) : size (laneFlat (a+1) W s x) ≤ 9*area (a+1) s := by
  rw [laneFlat, ← List.map_map,Padding.marks_size,List.length_map,List.length_range]
  have h := Nat.mul_le_mul_right (PhysicalWalshNode.inner (a+1) s) (max_le s.pref_pos (Nat.div_le_self s.pref W))
  change groups W s*PhysicalWalshNode.inner (a+1) s ≤ count (a+1) s at h
  calc
    _ ≤ count (a+1) s*(4*(s.w+1)+4)+1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
    _ ≤ _ := by unfold area; ring_nf; omega

open private charge_prefix from OAI.Computability.NearSquareRoot.PhysicalWalshElementaryPrefix

/-- The polynomial ticket setup is shared across the row. Scanning the row
once for each selected bit contributes exactly the elementary prefix charge. -/
theorem walker_charge {a d e f C J N m S : ℕ} (s : Shape) (cut : Shape → ℕ)
    (hc : cut s ≤ ElementarySchedule.slotWidth (a+1) s)
    (ht : m ≤ J*(Header.scale (a+1) s+1)^f) (rows : N ≤ count (a+1) s)
    (work : S = C*(m+1)^e + (N+1)*(s.w+1)) (hd : f*e+1 ≤ d) :
    let K := C*(J+1)^e
    (cut s+1)*(S+1)+1 ≤ (K+3)*(allowance (a+1) d s+ElementarySweep.prefixExtra (a+1) cut s+1) ∧
    S+1 ≤ (K+2)*(allowance (a+1) d s+1) := by
  intro K
  let H := Header.scale (a+1) s+1
  have pos : 1 ≤ H^f := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have mBound : m+1 ≤ (J+1)*H^f := by rw [Nat.succ_mul]; change m ≤ J*H^f at ht; omega
  have poly := Nat.mul_le_mul_left C (Nat.pow_le_pow_left mBound e)
  rw [mul_pow,← pow_mul,← Nat.mul_assoc] at poly
  have vol := Nat.mul_le_mul_right (s.w+1) (Nat.succ_le_succ rows)
  have bound : S ≤ K*H^(f*e) + area (a+1) s := work.le.trans (Nat.add_le_add poly vol)
  have smaller := allowance_mono (A:=a+1) hd s
  have powfit : H^(f*e) ≤ allowance (a+1) d s :=
    (Nat.pow_le_pow_right (Nat.succ_pos _) (show f*e ≤ d by omega)).trans (power_le a d s)
  have fits := Nat.mul_le_mul_left K (powfit.trans (Nat.le_succ _))
  change K*H^(f*e) ≤ K*(allowance (a+1) d s+1) at fits
  have ar := area_le a d s
  constructor
  · calc
      _ ≤ (cut s+1)*(K*H^(f*e)+area (a+1) s+1)+1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.succ_le_succ bound)) _
      _ ≤ (K+3)*(allowance (a+1) (f*e+1) s+ElementarySweep.prefixExtra (a+1) cut s+1) :=
        charge_prefix a (f*e) K cut s hc
      _ ≤ _ := by gcongr
  · rw [Nat.add_mul]; omega

/-- Compile only the current header while the input row remains parked. -/
theorem prepare {a W d e : ℕ} (hd : 1 ≤ d) (de : d ≤ e) (cmd : Cmd)
    (tickets : Shape → List ElementarySchedule.Words)
    (compact : ∃ C : ℕ, ∀ s env p, Fits env cmd (pile 0 (send (Header.wire (a+1) s)) p)
      (pile 0 (send (tickets s)) p) (C*(Header.scale (a+1) s+1)^d)) :
    let A := fun t : XorInput W => allowance (a+1) e t.shape
    EffectiveBoundedTask.Runs (KernelEffectiveFamily.leftCmd cmd) A A
      (fun t => send (Header.wire (a+1) t.shape,laneFlat (a+1) W t.shape t.row))
      (fun t => send (tickets t.shape,laneFlat (a+1) W t.shape t.row)) := by
  intro A
  let p (t : XorInput W) := (Header.scale (a+1) t.shape+1)^d
  let query (t : XorInput W) := send (Header.wire (a+1) t.shape)
  let reply (t : XorInput W) := send (tickets t.shape)
  obtain ⟨C,hc⟩ := compact
  have first : EffectiveBoundedTask.Runs cmd p (fun t => (query t).count + p t) query reply := by
    apply EffectiveBoundedTask.Runs.of_time
    exact ⟨C,fun t env park => (hc t.shape env park).mono (Nat.mul_le_mul_left C (Nat.le_succ _))⟩
  have paired := AgendaOps.left first (fun t => send (laneFlat (a+1) W t.shape t.row))
  apply paired.bound 1 11
  all_goals intro t
  all_goals have px : p t ≤ A t := (power_le a d t.shape).trans (allowance_mono de t.shape)
  · omega
  · have h : Header.scale (a+1) t.shape+1 ≤ p t := by
      simpa only [pow_one] using (Nat.pow_le_pow_right (Nat.succ_pos (Header.scale (a+1) t.shape)) hd)
    have row := (laneSize a W t.shape t.row).trans (Nat.mul_le_mul_left 9 (area_le a e t.shape))
    change size (laneFlat (a+1) W t.shape t.row) ≤ 9*A t at row
    change Header.scale (a+1) t.shape + p t + size (laneFlat (a+1) W t.shape t.row) + 1 ≤ 11*(A t+1)
    omega

end PhysicalWalshCompileElementaryRelease

end NearSquareRoot
end Computability
end OAI
