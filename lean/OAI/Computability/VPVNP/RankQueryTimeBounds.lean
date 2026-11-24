import OAI.Computability.VPVNP.RankQueryExecution

/-!
# A uniform singly exponential clock for the physical rank scan

The bidegree rectangle has at most six times the cube of the common input
bound. Within each cell the logarithmic Schur recursion gives a singly
exponential number of steps. Loading the root, checking the resulting scalar,
and moving the cursor add polynomial overhead in the word widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

/-- One bound on the six physical size parameters suffices for the complete
rank query over a rectangular matrix, including every index update. -/
theorem rankTime_le_exp (n m B w v e s : ℕ) (hn : n ≤ 2^s) (hm : m ≤ 2^s) (hB : B ≤ 2^s)
    (hw : w ≤ 2^s) (hv : v ≤ 2^s) (he : e ≤ 2^s) :
    rankTime n m B w v e ≤ 2^((4*s+10)*(4*s+7) + 5*s + 20) := by
  let A := 2^s
  let Z := (n+m)*n
  let H := 2^((4*s+10)*(4*s+7))
  have hA : 1 ≤ A := Nat.two_pow_pos _
  have hH : 1 ≤ H := Nat.two_pow_pos _
  have hA₂ : A ≤ A^2 := by simpa [pow_two] using Nat.mul_le_mul_left A hA
  change n ≤ A at hn
  change m ≤ A at hm
  change B ≤ A at hB
  change w ≤ A at hw
  change v ≤ A at hv
  change e ≤ A at he
  have hz : Z ≤ 2*A^2 := calc
    (n+m)*n ≤ (2*A)*A := Nat.mul_le_mul (by omega) hn
    _ = _ := by ring
  have hsize : 2^(2*s+1) = 2*A^2 := by dsimp [A]; rw [Nat.mul_comm 2 s, pow_succ, pow_mul]; ring
  have hrec := rootQueryClock_le n n Z B w v e (2*s+1) (by rw [hsize]; omega)
    (by rw [hsize]; omega) (by rwa [hsize])
  rw [show 2*(2*s+1)+8 = 4*s+10 by omega, show 2*(2*s+1)+5 = 4*s+7 by omega] at hrec
  change rootQueryClock n n Z B w v e ≤ loadClock w + (H*Engine.stepBudget B w v e+1) at hrec
  have hev : e*v ≤ A^2 := by simpa only [pow_two] using Nat.mul_le_mul he hv
  have hmax : max 1 (max w (e*v)) ≤ A^2 := by omega
  have hstep : Engine.stepBudget B w v e ≤ 224*A^2 := by unfold Engine.stepBudget; omega
  have hload : loadClock w ≤ 43*A^2 := by unfold loadClock; omega
  have hsq : (w+1)^2 ≤ 4*A^2 := calc
    _ ≤ (2*A)^2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by ring
  have hcheck : checkClock w v e ≤ 29242*A^2 := by
    unfold checkClock
    rw [Registers.clock_eq]
    omega
  have hsmall : A^2 ≤ H*A^2 := by simpa using Nat.mul_le_mul_right (A^2) hH
  have hbig := Nat.mul_le_mul_left H hstep
  rw [show H*(224*A^2) = 224*(H*A^2) by ring] at hbig
  have hcell : rootQueryClock n n Z B w v e + checkClock w v e + 1 ≤ 65536*(H*A^2) := by omega
  have hrect : (n+1)*(Z+1) ≤ 6*A^3 := calc
    _ ≤ (2*A)*(3*A^2) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring
  have hproduct := Nat.mul_le_mul hrect hcell
  rw [show 6*A^3*(65536*(H*A^2)) = 393216*(H*A^5) by ring] at hproduct
  have hpos : 0 < H*A^5 := Nat.mul_pos hH (Nat.pow_pos hA)
  change (n+1)*(Z+1)*(rootQueryClock n n Z B w v e+checkClock w v e+1)+2 ≤ _
  rw [show 2^((4*s+10)*(4*s+7)+5*s+20) = 1048576*(H*A^5) by
    dsimp only [A,H]; rw [Nat.mul_comm 5 s, pow_add, pow_add, pow_mul]; ring]
  omega

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
