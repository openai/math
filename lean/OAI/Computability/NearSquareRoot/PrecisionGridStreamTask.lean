import OAI.Computability.NearSquareRoot.PrecisionGridPass
import OAI.Computability.NearSquareRoot.PrecisionGridPassSpace
import OAI.Computability.NearSquareRoot.PrecisionGridDigits
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Uniform taped construction of global phase coefficients -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code

/-- Prefix records for the first `j` local phase tables. -/
def prefixAfter {w : ℕ} (f : ℕ) (t : ℕ → List (Dusk.Grain w)) (seed : Dusk.Grain w) :
    ℕ → List (Dusk.Grain w)
  | 0 => [seed]
  | j+1 => extendTable f (prefixAfter f t seed j) (t j)

theorem prefixAfter_foldl {w : ℕ} (f : ℕ) (t : ℕ → List (Dusk.Grain w)) (seed : Dusk.Grain w)
    (j : ℕ) : prefixAfter f t seed j = ((List.range j).map t).foldl (extendTable f) [seed] := by
  induction j with
  | zero => rfl
  | succ j ih => simp [prefixAfter, ih, List.range_succ, List.foldl_append]

private theorem prefixCount_growth {w : ℕ} (f : ℕ) (t : ℕ → List (Dusk.Grain w))
    (seed : Dusk.Grain w) (d : ℕ) (ht : ∀ j < d, 2 ≤ (t j).length) :
    ∀ j < d, 2 * (prefixAfter f t seed j).length ≤ (prefixAfter f t seed (j+1)).length := by
  intro j hj
  rw [prefixAfter, extendTable_length, Nat.mul_comm 2]
  exact Nat.mul_le_mul_left _ (ht j hj)

private theorem prefixCount_pos {w : ℕ} (f : ℕ) (t : ℕ → List (Dusk.Grain w))
    (seed : Dusk.Grain w) (d : ℕ) (ht : ∀ j < d, 2 ≤ (t j).length) :
    ∀ j ≤ d, 0 < (prefixAfter f t seed j).length := by
  intro j hj
  induction j with
  | zero => simp [prefixAfter]
  | succ j ih =>
    rw [prefixAfter, extendTable_length]
    exact Nat.mul_pos (ih (by omega)) ((by decide : 0 < 2).trans_le (ht j (by omega)))

private theorem prefixCount_total (R : ℕ → ℕ) (d : ℕ)
    (grow : ∀ j < d, 2 * R j ≤ R (j+1)) :
    ∑ j ∈ Finset.range d, R (j+1) ≤ 2 * R d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs := ih (fun j hj => grow j (by omega))
    have ht := grow d (by omega)
    rw [Finset.sum_range_succ]
    omega

private theorem forest_index_count (g : ℕ → Tree) (d : ℕ) :
    (Task.forest g (List.range d)).count = (∑ j ∈ Finset.range d, ((g j).count + 1)) + 1 := by
  rw [Task.forest_count]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.length_append, costSum_cat, Finset.sum_range_succ]
    simp only [List.length_singleton, costSum_cons, costSum_nil]
    omega

/-- The full sequence of table-extension passes uses one framed register
program. The bound is proportional to the final record count times the
per-record multiply clock, regardless of the varying number of tables.
The input forest includes every supplied local table and its precision rulers. -/
theorem prefixAfter_bounded {I : Type} (w f d : I → ℕ) (t : (i : I) → ℕ → List (Dusk.Grain (w i)))
    (seed : (i : I) → Dusk.Grain (w i)) (hf : ∀ i, f i ≤ w i+1)
    (ht : ∀ i j, j < d i → 2 ≤ (t i j).length) :
    Space.BoundedTask (fun i => (prefixAfter (f i) (t i) (seed i) (d i)).length * GridTask.recordCost (w i))
      (fun i => (prefixAfter (f i) (t i) (seed i) (d i)).length * (w i+1) + GridTask.recordCost (w i))
      (fun i => .fork
        (send ((List.range (d i)).map fun j => tableWords (f i) (t i j)))
        (send (prefixWords [seed i])))
      (fun i => send (prefixWords (prefixAfter (f i) (t i) (seed i) (d i)))) := by
  let s i j := prefixAfter (f i) (t i) (seed i) j
  let c i := GridTask.recordCost (w i)
  let a i j := (s i (j+1)).length * c i
  let X := (i : I) × Fin (d i)
  let x (v : X) := s v.1 v.2.val
  let y (v : X) := t v.1 v.2.val
  have hx (v : X) : x v ≠ [] := List.length_pos_iff.mp
    (prefixCount_pos _ _ _ _ (ht v.1) _ v.2.isLt.le)
  have hy (v : X) : y v ≠ [] := List.length_pos_iff.mp ((by decide : 0 < 2).trans_le
    (ht v.1 v.2.val v.2.isLt))
  have step := extendTable_bounded (fun v : X => w v.1) (fun v => f v.1) x y
    (fun v => hf v.1) hx hy
  let table i j := send (tableWords (f i) (t i j))
  let state i j := send (prefixWords (s i j))
  let unit i := w i + 1
  let scratch i j := (s i (j+1)).length * unit i + c i
  let volume i := 30 * ((s i (d i)).length * unit i + c i + 1)
  have hb {i : I} (j : ℕ) (hj : j < d i) :
      (table i j).count + 1 ≤ 14 * ((s i (j+1)).length * unit i) := by
    have H := tableWords_size (t i j) (hf i)
    have pre := prefixCount_pos (f i) (t i) (seed i) _ (ht i) j hj.le
    have out : (s i (j+1)).length = (s i j).length * (t i j).length := extendTable_length ..
    have hle : (t i j).length ≤ (s i (j+1)).length := by
      rw [out, Nat.mul_comm]
      exact Nat.le_mul_of_pos_right _ pre
    have m := Nat.mul_le_mul_right (12*(w i+1)) hle
    have hp := Nat.mul_pos (prefixCount_pos (f i) (t i) (seed i) _ (ht i) (j+1) (by omega))
      (Nat.succ_pos (w i))
    change size (tableWords (f i) (t i j)) + 1 ≤ 14 * ((s i (j+1)).length * (w i+1))
    change 0 < (s i (j+1)).length * (w i+1) at hp
    nlinarith only [H,m,hp]
  have old {i : I} (j : ℕ) (hj : j ≤ d i) : (s i j).length ≤ (s i (d i)).length := by
    have hg := prefixCount_growth (f i) (t i) (seed i) _ (ht i)
    have hmono (n : ℕ) (hn : n ≤ d i) (hjn : j ≤ n) : (s i j).length ≤ (s i n).length := by
      induction n with
      | zero => have : j = 0 := by omega
                simp [this]
      | succ n ih =>
        rcases eq_or_lt_of_le hjn with rfl | lt
        · rfl
        · have H := ih (by omega) (by omega)
          have tt := hg n (by omega)
          change 2*(s i n).length ≤ (s i (n+1)).length at tt
          omega
    exact hmono _ le_rfl hj
  have passes := Space.BoundedTask.indexedPasses d table state a scratch volume
    (step.conform (by intro v; simp [a,s,x,y,prefixAfter,c])
      (by intro v; simp [scratch,s,x,y,prefixAfter,c,unit]) (fun _ => rfl) (fun _ => rfl))
    (fun i => by
      have sumBound := Finset.sum_le_sum (s := Finset.range (d i))
        (fun j hj => hb (i := i) j (Finset.mem_range.mp hj))
      have grow := prefixCount_total (fun j => (s i j).length) (d i) (prefixCount_growth _ _ _ _ (ht i))
      rw [← Finset.mul_sum, ← Finset.sum_mul] at sumBound
      have hn := Nat.mul_le_mul_left 14 (Nat.mul_le_mul_right (unit i) grow)
      rw [Nat.mul_assoc] at hn
      rw [forest_index_count]
      dsimp only [volume]
      omega)
    (fun i j hj => by
      have h := prefixWords_size (s i j)
      have m := Nat.mul_le_mul_right (12*(w i+1)) (old j hj)
      change size (prefixWords (s i j)) ≤ _
      dsimp only [volume,unit]
      nlinarith only [h,m,Nat.zero_le (c i),Nat.zero_le ((s i (d i)).length * (w i+1))])
    (fun i j hj => by
      have m := Nat.mul_le_mul_right (unit i) (old (j+1) (by omega : j+1 ≤ d i))
      dsimp only [volume,scratch]
      omega)
  have eqin (i : I) :
      Task.forest (table i) (List.range (d i)) =
      send ((List.range (d i)).map fun j => tableWords (f i) (t i j)) := by
    rw [← Task.forest_send, Task.forest_map]
  have run := passes.conform (fun _ => rfl) (fun _ => rfl)
    (fun i => congrArg (fun z => Tree.fork z (state i 0)) (eqin i)) (fun _ => rfl)
  apply run.bound 32 32
  swap
  · intro i
    change volume i + 1 ≤ 32 * ((s i (d i)).length * unit i + c i + 1)
    dsimp only [volume]
    omega
  intro i
  have hw : w i+1 ≤ c i := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hc : 0 < c i := by omega
  have cost j (hj : j < d i) :
      a i j + (table i j).count + 1 ≤ 16 * ((s i (j+1)).length * c i) := by
    have h := hb (i := i) j hj
    have m := Nat.mul_le_mul_right (s i (j+1)).length hw
    rw [Nat.mul_comm, Nat.mul_comm (c i)] at m
    change (s i (j+1)).length * unit i ≤ (s i (j+1)).length * c i at m
    dsimp only [a]
    omega
  have Hsum := Finset.sum_le_sum (s := Finset.range (d i))
    (fun j hj => cost j (Finset.mem_range.mp hj))
  have Hgrowth := prefixCount_total (fun j => (s i j).length) (d i)
    (prefixCount_growth _ _ _ _ (ht i))
  rw [← Finset.mul_sum, ← Finset.sum_mul] at Hsum
  have hn := Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right (c i) Hgrowth)
  change (∑ j ∈ Finset.range (d i), (a i j + (table i j).count + 1)) + 1 + 1 ≤
    32 * ((s i (d i)).length * c i + 1)
  rw [Nat.mul_assoc] at hn
  omega

/-- The encoded output of all passes, indexed by the number of completed
tables. This function uses the same fixed-point multiplier as the tape task. -/
noncomputable def phaseStreamRecords {α : Type*} (k : ℕ) (t : ℕ → List α)
    (store : α → Record (guardedK k)) (d : ℕ) : List (Record (guardedK k)) :=
  prefixAfter (w := componentBits (guardedK k)) (fractionBits (guardedK k)) (fun j => (t j).map store)
    (digitRecord (guardedK k) 1) d

private theorem phaseStreamRecords_foldl {α : Type*} (k : ℕ) (t : ℕ → List α)
    (store : α → Record (guardedK k)) (d : ℕ) :
    phaseStreamRecords k t store d = ((List.range d).map t).foldl
      (PhaseStream.extend (fun p x => multiply _ p (store x))) [digitRecord _ 1] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change extendTable (w := componentBits (guardedK k)) _ (phaseStreamRecords k t store d) ((t d).map store) = _
    rw [ih,List.range_succ,List.map_append,List.foldl_append]
    simp [extendTable, PhaseStream.extend, multiply, List.map_map, Function.comp_def]

/-- The number of coefficients written equals the product of the local table
lengths, including a single coefficient when the descriptor has no tables. -/
theorem phaseStreamRecords_count {α : Type*} (k : ℕ) (t : ℕ → List α)
    (store : α → Record (guardedK k)) (d : ℕ) :
    (phaseStreamRecords k t store d).length =
      ((List.range d).map (fun j => (t j).length)).prod := by
  rw [phaseStreamRecords_foldl, PhaseStream.final_length]
  simp [List.map_map, Function.comp_def]

/-- The same phase coefficients meet the numerical error and resource bounds.
The framed program copies the supplied local tables. Its peak space includes
all resident records plus the workspace of one short multiplication. -/
theorem physicalPhaseStream {I α : Type} (k d : I → ℕ) (t : I → ℕ → List α)
    (store : (i : I) → α → Record (guardedK (k i))) (ideal : I → α → ℂ)
    (hd : ∀ i, d i ≤ k i) (ht : ∀ i j, j < d i → 2 ≤ (t i j).length)
    (hunit : ∀ i j, j < d i → ∀ a ∈ t i j, ‖ideal i a‖ = 1)
    (herr : ∀ i j, j < d i → ∀ a ∈ t i j,
      ‖value _ (store i a) - ideal i a‖ ≤ 1 / (2 : ℝ) ^ (70 * guardedK (k i))) :
    let r i := phaseStreamRecords (k i) (t i) (store i) (d i)
    let clock i := (r i).length * GridTask.recordCost (k i)
    let input i := Tree.fork
      (send ((List.range (d i)).map (fun j =>
        tableWords (fractionBits (guardedK (k i))) ((t i j).map (store i)))))
      (send (prefixWords [digitRecord (guardedK (k i)) 1]))
    let output i := send (prefixWords (r i))
    let peak i := (r i).length * (k i + 1) + GridTask.recordCost (k i)
    (Space.BoundedTask clock peak input output ∧ PhysicalWalsh.TapeTask clock peak input output) ∧
    ∀ i, List.Forall₂ (fun v z => ‖value _ v - z‖ ≤ 1 / (2 : ℝ) ^ (70 * k i)) (r i)
      ((PhaseStream.addresses ((List.range (d i)).map (t i))).map (fun xs => (xs.map (ideal i)).prod)) := by
  dsimp only
  constructor
  · have run := prefixAfter_bounded (fun i => componentBits (guardedK (k i)))
      (fun i => fractionBits (guardedK (k i))) d (fun i j => (t i j).map (store i))
      (fun i => digitRecord (guardedK (k i)) 1)
      (fun i => by unfold componentBits fractionBits; omega)
      (fun i j hj => by simpa using ht i j hj)
    obtain ⟨C,hC⟩ := GridTask.recordCost_scale 300
    refine (fun frame => ⟨frame, frame.release⟩) (run.bound (C+1) (C+301) ?_ ?_)
    · intro i
      have hbound : componentBits (guardedK (k i)) ≤ 300 * (k i + 1) := by
        unfold componentBits guardedK
        omega
      have hs := hC (k i) _ hbound
      let N := (phaseStreamRecords (k i) (t i) (store i) (d i)).length
      change N * GridTask.recordCost (componentBits (guardedK (k i))) + 1 ≤
        (C+1) * (N * GridTask.recordCost (k i) + 1)
      nlinarith only [Nat.mul_le_mul_left N hs, Nat.zero_le (N * GridTask.recordCost (k i)), Nat.zero_le C]
    · intro i
      let wi := componentBits (guardedK (k i))
      let N := (phaseStreamRecords (k i) (t i) (store i) (d i)).length
      have hw : wi+1 ≤ 300*(k i+1) := by dsimp [wi,componentBits,guardedK]; omega
      have hc := hC (k i) wi (le_trans (Nat.le_succ _) hw)
      change N*(wi+1) + GridTask.recordCost wi + 1 ≤
        (C+301) * (N*(k i+1) + GridTask.recordCost (k i) + 1)
      nlinarith only [hc, Nat.mul_le_mul_left N hw, Nat.zero_le C,
        Nat.zero_le (C*(N*(k i+1))), Nat.zero_le (GridTask.recordCost (k i)), Nat.zero_le (N*(k i+1))]
  · intro i
    rw [phaseStreamRecords_foldl]
    apply phase_stream_error _ _ _ _ _ (value_seed _)
    · simpa using hd i
    · intro tab htab a ha
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp htab
      exact hunit i j (List.mem_range.mp hj) a ha
    · intro tab htab a ha
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp htab
      exact herr i j (List.mem_range.mp hj) a ha

/-- On the full padded box the per-invocation scratch fits within a single
array. This gives an absolute linear-space bound for the entire prefix
construction from the bound expressed in `physicalPhaseStream`. -/
theorem phasePeak_on_box (k : ℕ) :
    2^k * (k+1) + GridTask.recordCost k ≤ 2 * (2^k * (k+1)) := by
  have hk : k+1 ≤ 2^k := Nat.lt_two_pow_self
  have hlog : Nat.clog 2 (k+1) ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr hk
  have hc : Nat.clog 2 (k+1)+1 ≤ 2^k := by omega
  have h := Nat.mul_le_mul_right (k+1) hc
  dsimp [GridTask.recordCost]
  rw [Nat.mul_comm (Nat.clog 2 (k+1)+1)] at h
  omega

end FixedPoint

end NearSquareRoot
end Computability
end OAI
