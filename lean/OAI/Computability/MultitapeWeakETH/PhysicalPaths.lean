import OAI.Computability.MultitapeWeakETH.NativeScale
import OAI.Computability.VPVNP.CompressorWorkspaceCore
import OAI.Computability.VPVNP.CompressorBlockClock

/-! # Length of a complete descriptor history on a binary input tape -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords BurstRAM DyadicBudget Filter Algorithms.SubexponentialSAT
open scoped Classical
noncomputable section

private theorem choices_length {w : ℕ} (es : List (Event w)) : (choiceBits es).length ≤ es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [choiceBits] <;> omega

/-- Include call boundaries and the end marker. This encoding supports
empty choice tapes even when consecutive deterministic calls occur. -/
def pathCode (bits : List (List Bool)) := Encoding.encodeList id bits

theorem pathCode_injective : Function.Injective pathCode := Encoding.encodeList_injective Function.injective_id

private theorem paths_length {w small : ℕ} (logs : List (Report w))
    (clock : ∀ r ∈ logs, r.events.length < small) :
    (pathCode (branchPaths logs)).length ≤ (2*small+2)*RAMBuckets.cost Report.probes logs+1 := by
  induction logs with
  | nil => simp [pathCode,branchPaths,RAMBuckets.cost]
  | cons r rs ih =>
    have tail := ih fun q h => clock q (List.mem_cons_of_mem _ h)
    have len := (choices_length r.events).trans (clock r List.mem_cons_self).le
    change (Encoding.encodeList id (choiceBits r.events :: branchPaths rs)).length ≤ _
    rw [Encoding.length_encodeList_cons,RAMBuckets.cost,Nat.mul_add,Nat.mul_add,Nat.mul_one]
    change 2*(choiceBits r.events).length+2+(pathCode (branchPaths rs)).length ≤ _
    omega

/-- Source-level clock and total charged probes control the entire binary
input needed to replay the native history, independently of word addresses. -/
theorem core_path_length {w cap small : ℕ} {A : BlockPlanner.Script} {pub : Fin 11 → Word w}
    {st : Option (Word w)} {m : Memory w}
    {s : BranchSegments.Segment (OnlineWorkspace.program A.plan pub) cap st m}
    (source : OnlineWorkspace.Core A pub s small) :
    (pathCode s.bits).length ≤ (2*small+2)*RAMBuckets.cost Report.probes source.logs+1 := by
  rw [← ((runSegment_iff ..).mp source.run).2.2]
  exact paths_length source.logs source.ticks

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

open private source_shape from OAI.Computability.MultitapeWeakETH.NativeScale

/-- Framing the native calls preserves the power saving of the sparse
grid. The constant per position is fixed before the volume is chosen. -/
theorem path_budget (rate : ℕ) :
    let b := 4*stepSize B
    ∀ᶠ N : ℕ in atTop,
      let s := index b N
      (2*BlockClock.small B 1 (scale B s)+2)*
        (s*(S.steps+1)*(rate*(source B s).positions)+4)+1 ≤ ⌊(N:ℝ)^(1-1/(2*b:ℝ))⌋₊ := by
  intro b
  let K := stepSize B
  have kp : 0 < K := step_pos B
  obtain ⟨C,clock⟩ := BlockClock.rate B 1
  let overhead (s : ℕ) := (2*(C*(16*(K*s)+1)^4)+2)*(s*(S.steps+1)*(rate*(8*(K*s)+4))+4)+1
  have u : PolynomiallyBounded (fun s => K*s) := (PolynomiallyBounded.const K).mul .id
  have left := (PolynomiallyBounded.const 2).mul ((PolynomiallyBounded.const C).mul
    ((((PolynomiallyBounded.const 16).mul u).add (.const 1)).pow 4))
  have right := (PolynomiallyBounded.id.mul (.const (S.steps+1))).mul
    ((PolynomiallyBounded.const rate).mul (((PolynomiallyBounded.const 8).mul u).add (.const 4)))
  have poly : PolynomiallyBounded overhead := (((left.add (.const 2)).mul (right.add (.const 4))).add (.const 1))
  obtain ⟨c,d,bound⟩ := poly.exists_global_bound
  filter_upwards [eventually_grid_saving (b:=b) (by dsimp [b]; have := step_pos B; omega) (c:ℝ)
    (by positivity) d] with N save
  let s := index b N
  let p := 2^(3*(K*s))
  have hp : 1 ≤ p := Nat.two_pow_pos _
  have cp := clock (scale B s)
  rw [scale,Nat.log2_two_pow] at cp
  have sized := (source_shape B s).1
  change (source B s).positions=(8*(K*s)+4)*p at sized
  have expo : p ≤ 2^((b-1)*s) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [show 3*(K*s)=3*K*s by ring]
    exact Nat.mul_le_mul_right _ (by change 3*K ≤ 4*K-1; omega)
  apply Nat.le_floor
  refine le_trans ?_ save
  exact_mod_cast (calc
    (2*BlockClock.small B 1 (scale B s)+2)*(s*(S.steps+1)*(rate*(source B s).positions)+4)+1
      ≤ (2*(C*(16*(K*s)+1)^4)+2)*(s*(S.steps+1)*(rate*((8*(K*s)+4)*p))+4)+1 := by rw [sized]; gcongr; exact cp
    _ ≤ overhead s*p := by dsimp [overhead]; nlinarith [Nat.mul_le_mul_left (4*(2*(C*(16*(K*s)+1)^4)+2)+1) hp]
    _ ≤ (c*(s+1)^d)*2^((b-1)*s) := Nat.mul_le_mul (bound s) expo)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
