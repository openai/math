import OAI.Computability.NearSquareRoot.PhysicalWalshElementarySweep
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryStages
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeConjugate

/-! # A computably truncated aligned XOR

Any physical descriptor program returning a cut at most the slot width can
restrict the sweep to those low positions. Its cut-dependent clock and arena
are common to all source and destination pairs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ElementarySweep

open IntegerMultiplication Code Space Staff PhysicalWalsh
open ElementarySchedule (slotWidth)

def prefixExtra (A : ℕ) (cut : Shape → ℕ) (s : Shape) := (cut s+1)*((count A s+1)*(s.w+1))

private theorem charge_prefix (a e C : ℕ) (cut : Shape → ℕ) (s : Shape) (small : cut s ≤ slotWidth (a+1) s) :
    let A := a+1
    let k := Header.scale A s+1
    let L := cut s+1
    let V := (count A s+1)*(s.w+1)
    L*(C*k^e+V+1)+1 ≤ (C+3)*(allowance A (e+1) s+L*V+1) := by
  intro A k L V
  have le : L ≤ k := Nat.succ_le_succ (small.trans (slotWidth_le_scale a s))
  have hk : 1 ≤ k := Nat.succ_pos _
  have top : k ≤ k^(e+1) := by simpa only [pow_one] using (Nat.pow_le_pow_right hk (show 1 ≤ e+1 by omega))
  have cap : k^(e+1) ≤ allowance A (e+1) s := Nat.le_add_left ..
  have hpow : L*(C*k^e) ≤ C*k^(e+1) := calc
    _ ≤ k*(C*k^e) := Nat.mul_le_mul_right _ le
    _ = _ := by rw [pow_succ]; ring
  have hC := Nat.mul_le_mul_left C cap
  have enough := Nat.mul_le_mul_left C (show allowance A (e+1) s ≤ allowance A (e+1) s + L*V+1 by omega)
  rw [Nat.mul_add L _ 1, Nat.mul_add L _ V, Nat.mul_one, Nat.add_mul C 3]
  omega

theorem onePrefix (a W : ℕ) (src dst : Fin (a+1)) (ne : src ≠ dst)
    (cut : Shape → ℕ) (known : Realizes (Header.regime (a+1)) cut) (cap : ∀ s, cut s ≤ slotWidth (a+1) s) :
    ∃ d : ℕ, Route.FlatRun (W:=W) a
      (fun s => allowance (a+1) d s + prefixExtra (a+1) cut s) (allowance (a+1) d)
      (fun s x => x ∘ address src dst s (cut s)) := by
  let state (t : XorInput W) (j : ℕ) : Data t.shape := t.row ∘ address src dst t.shape j
  obtain ⟨e,C,run⟩ := sweepPrefix src dst W ne (ElementaryIndex.rewire src dst) cut known cap state
    (fun t j n => congrArg t.row (address_step src dst ne t.shape (j.castLE (cap _)) n))
  let S (t : XorInput W) := allowance (a+1) (e+1) t.shape
  let T (t : XorInput W) := S t + prefixExtra (a+1) cut t.shape
  have prog := run.bound (time' := T) (space' := S) (C+3) (C+2)
    (fun t => charge_prefix a e C cut t.shape (cap _)) (fun t => by
      let u := t.shape
      have pow : (Header.scale (a+1) u+1)^e ≤ S t :=
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ e)).trans (Nat.le_add_left ..)
      have vol : (count (a+1) u+1)*(u.w+1) ≤ S t :=
        (Nat.mul_le_mul_left _ (show u.w+1 ≤ grow (a+1) u.level+u.w+1 by omega)).trans (Nat.le_add_right ..)
      change C*(Header.scale (a+1) u+1)^e + (count (a+1) u+1)*(u.w+1)+1 ≤ (C+2)*(S t+1)
      rw [Nat.add_mul C 2]
      have h : C*(Header.scale (a+1) u+1)^e ≤ C*(S t+1) := Nat.mul_le_mul_left C (pow.trans (Nat.le_succ _))
      omega)
  have start (t : XorInput W) : state t 0 = t.row := by funext n; simp [state]
  refine ⟨e+1,?_⟩
  simpa only [start,T,S,Route.FlatRun] using prog

/-- A single degree dominates every gate pair in the finite control. The
shared meter can therefore link the three directional XORs of a low-slot swap. -/
theorem prefixRun (a W : ℕ) (cut : Shape → ℕ) (known : Realizes (Header.regime (a+1)) cut)
    (cap : ∀ s, cut s ≤ slotWidth (a+1) s) : ∃ D : ℕ, ∀ d, D ≤ d → ∀ src dst : Fin (a+1), src ≠ dst →
    Route.FlatRun (W:=W) a (nodeScan a W d (prefixExtra (a+1) cut)) (nodeArena a W d)
      (fun s x => x ∘ address src dst s (cut s)) := by
  classical
  let G := {g : Fin (a+1) × Fin (a+1) // g.1 ≠ g.2}
  choose deg op using (fun g : G => onePrefix a W g.val.1 g.val.2 g.property cut known cap)
  refine ⟨Finset.univ.sup deg,fun d hd src dst ne => ?_⟩
  let i : G := ⟨(src,dst),ne⟩
  have am (t : XorInput W) : allowance (a+1) (deg i) t.shape ≤ nodeArena a W d t.shape :=
    (allowance_mono ((Finset.le_sup (f:=deg) (Finset.mem_univ i)).trans hd) t.shape).trans (le_max_left ..)
  exact (op i).mono (fun t => Nat.add_le_add_right (am t) _) am

end PhysicalWalshNode.ElementarySweep

end NearSquareRoot
end Computability
end OAI
