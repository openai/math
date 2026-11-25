import OAI.Hierarchy.TaggedSortLiftStage
import OAI.Hierarchy.DescentSortLiftHeight
import Mathlib.Tactic

namespace OAI
/-! # Charging the actual short-sort blocks of the flattened Leighton stages -/

noncomputable section
namespace Hierarchy.Tagged.SortLift

open scoped BigOperators Classical
variable {n levels layers H ℓ : ℕ}

/-- A stage partitions its physical input wires bijectively into its actual sort blocks. -/
theorem Stage.total_length (st : Stage n) : ∑ b,st.length b=n := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr st.input

theorem Stage.blocks_mul_le (st : Stage n) (half : ∀ b,H≤2*st.length b) :
    st.blocks*H≤2*n := by
  calc
    st.blocks*H = ∑ _ : Fin st.blocks,H := by simp
    _ ≤ ∑ b,2*st.length b := Finset.sum_le_sum (fun b _=>half b)
    _ = 2*n := by rw [← Finset.mul_sum,st.total_length]

def leafCalls (stages : Fin layers→Stage n) := ∑ i,(stages i).blocks

/-- Counts occupied sort blocks at the base, allowing each physical boundary block to
pay for one full homogeneous sort of H inputs. -/
theorem leaf_volume (stages : Fin layers→Stage n) (half : ∀ i b,H≤2*(stages i).length b) :
    leafCalls stages*H≤2*layers*n := by
  unfold leafCalls
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ _ : Fin layers,2*n := Finset.sum_le_sum (fun i _=>(stages i).blocks_mul_le (half i))
    _ = 2*layers*n := by simp; ring

/-- Direct charge for an arbitrary actual dyadic array. Its physical size may
exceed the square of the local width; only the installed depth and leaf widths enter. -/
theorem physical_volume (b h e : ℕ) (stages : Fin layers→Stage (2^e))
    (half : ∀ i j,2^b≤2*(stages i).length j) (rounds : layers≤4^7) :
    leafCalls stages*2^b+2^h ≤ (2*4^7+1)*(2^e+2^h) := by
  have bound := (leaf_volume stages half).trans <|
    Nat.mul_le_mul_right (2^e) (Nat.mul_le_mul_left 2 rounds)
  calc
    leafCalls stages*2^b+2^h ≤ (2*4^7)*(2^e+2^h)+(2^e+2^h) :=
      Nat.add_le_add (bound.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))) (Nat.le_add_left _ _)
    _ = _ := by ring

/-- The real field-major terminal implementation permits one unfinished block of
homogeneous calls per slice, represented here by the single +H in a batch. -/
theorem homogeneous_volume (stages : Fin layers→Stage n) (half : ∀ i b,H≤2*(stages i).length b)
    (rounds : layers≤4^levels) (extent : n≤2*(ℓ+H)) :
    leafCalls stages*H+H≤(4*4^levels+1)*(ℓ+H) := by
  have bound := (leaf_volume stages half).trans <|
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 rounds) extent
  calc
    leafCalls stages*H+H ≤ (2*4^levels)*(2*(ℓ+H))+(ℓ+H) := Nat.add_le_add bound (by omega)
    _ = _ := by ring

private theorem padded_room (ℓ H : ℕ) (pos : 0 < H) : ℓ≤((ℓ+H-1)/H)*H := by
  have small := Nat.mod_lt (ℓ+H-1) pos
  have eqn :=  Nat.mod_add_div (ℓ+H-1) H
  rw [Nat.mul_comm H] at eqn
  omega

theorem leaf_count (stages : Fin layers→Stage n) (half : ∀ i b,H≤2*(stages i).length b)
    (rounds : layers≤4^levels) (extent : n≤2*(ℓ+H)) (pos : 0 < H) :
    leafCalls stages≤(4*4^levels)*(1+(ℓ+H-1)/H) := by
  have total := leaf_volume stages half
  have cap := padded_room ℓ H pos
  have bigger : n≤2*((1+(ℓ+H-1)/H)*H) := extent.trans (Nat.mul_le_mul_left 2 (by
    rw [Nat.add_mul,one_mul];omega))
  have product := total.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 rounds) bigger)
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc
    leafCalls stages*H ≤ (2*4^levels)*(2*((1+(ℓ+H-1)/H)*H)) := product
    _ = _ := by ring

/-- The final homogeneous slicing bank uses height h, whereas its base-level short
sorts use height b. The single end charge therefore contributes 2^h words per slice. -/
theorem height_volume (b h : ℕ) (small : b ≤ h) (stages : Fin layers→Stage n)
    (half : ∀ i j,2^b≤2*(stages i).length j)
    (rounds : layers≤4^levels) (extent : n≤2*(ℓ+2^b)) :
    leafCalls stages*2^b+2^h≤(4*4^levels+1)*(ℓ+2^h) := by
  have hcap : 2^b≤2^h := Nat.pow_le_pow_right (by decide) small
  have full : n≤2*(ℓ+2^h) := extent.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hcap ℓ))
  have bound := (leaf_volume stages half).trans <|
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 rounds) full
  calc
    leafCalls stages*2^b+2^h ≤ (2*4^levels)*(2*(ℓ+2^h))+(ℓ+2^h) := Nat.add_le_add bound (by omega)
    _ = _ := by ring

/-- Direct version for the physical global pool, which may contain more than
the square of the local number of pins. The installed stage count supplies its depth. -/
theorem terminal_budget_any (b h ℓ : ℕ) (small : b ≤ h)
    (stages : Fin layers→Stage (2^(DescentSortLiftHeight.pad b ℓ)))
    (half : ∀ i j,2^b≤2*(stages i).length j) (rounds : layers≤4^7) :
    leafCalls stages≤65536*(1+(ℓ+2^b-1)/2^b) ∧
    leafCalls stages*2^b+2^h≤65537*(ℓ+2^h) := by
  have extent := (DescentSortLiftHeight.pad_volume b ℓ).2.2.1
  exact ⟨leaf_count stages half rounds extent (Nat.two_pow_pos b),height_volume b h small stages half rounds extent⟩

/-- For the canonical dyadic rounding of an arbitrary length, the constant-volume
bound is uniform over every flattened physical plan with at most seven lifts. -/
theorem terminal_budget (b h ℓ : ℕ) (small : b ≤ h) (_fits : ℓ≤(2^b)^2)
    (stages : Fin layers→Stage (2^(DescentSortLiftHeight.pad b ℓ)))
    (half : ∀ i j,2^b≤2*(stages i).length j)
    (rounds : layers≤4^7) :
    leafCalls stages≤65536*(1+(ℓ+2^b-1)/2^b) ∧
    leafCalls stages*2^b+2^h≤65537*(ℓ+2^h) := by
  exact terminal_budget_any b h ℓ small stages half rounds

/-- List form matching the chronological `SortLift.run` interface. Membership
assumptions are the same ones preserved by parallel stage refinement. -/
theorem terminal_list_budget (b h ℓ : ℕ) (small : b ≤ h) (fits : ℓ≤(2^b)^2)
    (ss : List (Stage (2^(DescentSortLiftHeight.pad b ℓ))))
    (half : ∀ st∈ss,∀j,2^b≤2*st.length j) (rounds : ss.length≤4^7) :
    leafCalls ss.get≤65536*(1+(ℓ+2^b-1)/2^b) ∧
    leafCalls ss.get*2^b+2^h≤65537*(ℓ+2^h) :=
  terminal_budget b h ℓ small fits ss.get (fun i=>half (ss.get i) (List.get_mem ss i)) rounds

/-- Uniform padded expansion of one actual level has k source columns, k
dealt columns, k aligned blocks, and k+1 shifted blocks. -/
def fourCalls (a : ℕ) := 4*2^a+1

theorem fourCalls_le (a : ℕ) : fourCalls a≤5*2^a := by
  unfold fourCalls
  have := Nat.two_pow_pos a
  omega

def paddedCalls (old : ℕ→ℕ) : ℕ→ℕ
  | 0=>1
  | t+1=>paddedCalls old t*fourCalls (old (t+1)-old t)

/-- The products of the power-of-two column counts telescope, including shortened
final height jumps whenever the requested capacity lies strictly between two levels. -/
theorem paddedCalls_le (old : ℕ→ℕ) (inc : Monotone old) (d : ℕ) :
    paddedCalls old d≤5^d*2^(old d-old 0) := by
  induction d with
  | zero=>simp [paddedCalls]
  | succ d ih=>
    have increasing : old d ≤ old (d+1) := inc (Nat.le_succ d)
    have bottom : old 0 ≤ old d := inc (Nat.zero_le d)
    have sum : old (d+1)-old 0=(old d-old 0)+(old (d+1)-old d) :=
      (Nat.sub_add_sub_cancel increasing bottom).symm.trans (Nat.add_comm ..)
    have bound := Nat.mul_le_mul ih (fourCalls_le (old (d+1)-old d))
    calc
      paddedCalls old (d+1) ≤ (5^d*2^(old d-old 0))*(5*2^(old (d+1)-old d)) := bound
      _ = 5^(d+1)*2^(old (d+1)-old 0) := by rw [sum,pow_succ 5,pow_add 2];ring


end Hierarchy.Tagged.SortLift

end
end OAI
