import OAI.Computability.IntegerMultiplication.Strip.Narrow
import OAI.Computability.IntegerMultiplication.Strip.Relay
import OAI.Computability.NearSquareRoot.InterchangeBatchIndices

/-!
# Physical batching by the leading radix digit of an interchange

The input is flat in prefix, digit, suffix order. A row is flat in prefix,
batch, suffix order. P192's sequential stack programs carve out suffix blocks
and transpose a fixed digit index, with no random reads of the stream. The
incomplete final batch reuses earlier digits in that fibre. The reverse scan
copies only the genuine slots.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BatchRows
open IntegerMultiplication.Code IntegerMultiplication.Strip

variable {I : Type} {P T : I → Type} (p : (i : I) → Series (P i)) (t : (i : I) → Series (T i))
variable {w : I → ℝ} {input : I → Tree}

/-- Prefix and suffix counts are read from prepared rulers. The charge includes
copying the rulers and all cells of a prefix/suffix square. The finite radix,
batch count and row count are fixed parameters of the program. -/
structure Geometry (w : I → ℝ) (input : I → Tree) : Prop where
  first : Carries w input (fun i => send (tally (p i).count))
  last : Carries w input (fun i => send (tally (t i).count))
  area : ∃ E : ℕ, ∀ i, ((p i).count + 1 : ℝ) * ((t i).count + 1) ≤ E * w i

/-- A lexicographic stream with a fixed-width middle index. -/
def layout (digits : ℕ) (i : I) : Series ((P i × Fin digits) × T i) :=
  ((p i).cart (Series.natural digits)).cart (t i)

abbrev Value (P T : I → Type) (k : ℕ) := (i : I) → (P i × Fin k) × T i → Tree

private def times (k : ℕ) (s : Tally) : Tally :=
  match k with
  | 0 => []
  | k + 1 => s ++ times k s

private theorem times_easy (k : ℕ) : Easy (times k) := by
  induction k with
  | zero => exact Easy.const []
  | succ k ih => exact (Easy.identity.pair ih).compose Easy.append

private theorem times_tally (k n : ℕ) : times k (tally n) = tally (n * k) := by
  induction k with
  | zero => simp [times, tally]
  | succ k ih => simp only [times, ih, Dims.mergeTally, Nat.mul_succ, Nat.add_comm]

/-- Expose the suffix blocks for a single fixed digit, keeping prefix order. -/
private theorem extract {k : ℕ} (g : Geometry p t w input) (v : Value P T k)
    (source : Carries w input (stackRun (layout p t k) v)) (d : Fin k) :
    Carries w input (stackRun p (fun i x => stripe (t i) fun z => v i ((x,d),z))) := by
  let digits := Series.natural k
  let pd i := (p i).cart digits
  let tail i (a : P i × Fin k) := stripe (t i) fun z => v i (a,z)
  have hpd : Carries w input (fun i => send (tally (pd i).count)) := by
    have h := g.first.chain (Carries.func g.first.budget g.first.out (times k) (times_easy k))
    simpa only [pd, digits, Series.count_cart, Series.count_natural, times_tally] using h
  obtain ⟨E, hE⟩ := g.area
  have product (i : I) : ((pd i).count + 1 : ℝ) * ((t i).count + 1) ≤
      ((k + 1)*E : ℕ) * w i := by
    simp only [pd, digits, Series.count_cart, Series.count_natural, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ((k:ℝ)+1) * (((p i).count+1) * ((t i).count+1)) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [Nat.cast_nonneg (α := ℝ) (p i).count, Nat.cast_nonneg (α := ℝ) k]
      _ ≤ ((k:ℝ)+1) * (E * w i) :=
        mul_le_mul_of_nonneg_left (hE i) (by positivity)
      _ = _ := by ring
  have blocks : Carries w input (stackRun pd tail) :=
    carve pd t v source (hpd.twice g.last) ⟨_, product⟩
  have dr := fixture g.first.small g.first.budget (send (tally digits.count))
  have product' (i : I) : ((p i).count + 1 : ℝ) * (digits.count + 1) ≤
      ((k+1)*E : ℕ) * w i := by
    simp only [digits, Series.count_natural, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have he : ((p i).count + 1 : ℝ) ≤ ((p i).count + 1) * ((t i).count+1) := by
      exact le_mul_of_one_le_right (by positivity) (by simp)
    rw [mul_comm ((p i).count + 1 : ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (he.trans (hE i)) (by positivity)
  have matrix := carve p (fun _ => digits) tail blocks (g.first.twice dr) ⟨_,product'⟩
  let col i (d : Fin k) (x : P i) := tail i (x,d)
  exact finite_cell digits (fun i j => stripe (p i) (col i j)) (unlay digits p col matrix) d

/-- Assemble a flat stream from its suffix blocks by a fixed table on the middle digit. -/
private theorem assemble {k : ℕ} (g : Geometry p t w input) (v : Value P T k)
    (columns : ∀ d : Fin k, Carries w input
      (stackRun p fun i x => stripe (t i) fun z => v i ((x,d),z))) :
    Carries w input (stackRun (layout p t k) v) := by
  let digits := Series.natural k
  let col i (d : Fin k) (x : P i) := stripe (t i) fun z => v i ((x,d),z)
  have outer := finite_series digits (fun i d => stripe (p i) (col i d))
    g.first.small g.first.budget columns
  have matrix := lay digits p col outer (seeds p g.first)
  have block := flatten p (fun _ => digits) (fun i a => col i a.2 a.1) matrix
  exact flatten (fun i => (p i).cart digits) t v block

/-- The padded record at row `u`, batch `g`, uses the corresponding input digit. -/
def padded {b W : ℕ} (hb : 0 < b) (v : Value P T b) (u : Fin W) : Value P T (groups b W) :=
  fun i a => v i ((a.1.1, select hb u a.1.2),a.2)

/-- All `W` independent rows are produced by one sequential stack program. -/
theorem split {b W : ℕ} (hb : 0 < b) (g : Geometry p t w input) (v : Value P T b)
    (source : Carries w input (stackRun (layout p t b) v)) :
    Carries w input (fun i => stripe (Series.natural W) fun u =>
      stripe (layout p t (groups b W) i) (padded hb v u i)) := by
  apply finite_series _ _ g.first.small g.first.budget
  intro u
  apply assemble p t g
  intro j
  exact extract p t g v source (select hb u j)

/-- Keep one genuine slot for each input digit, after an arbitrary operation
on the individual rows. -/
def gather {b W : ℕ} (hW : 0 < W) (v : Fin W → Value P T (groups b W)) : Value P T b :=
  fun i a => v (row hW a.1.2) i ((a.1.1, group hW a.1.2), a.2)

/-- Discard the padding and merge into prefix, digit, suffix order. -/
theorem merge {b W : ℕ} (hW : 0 < W) (g : Geometry p t w input)
    (v : Fin W → Value P T (groups b W))
    (rows : Carries w input (fun i => stripe (Series.natural W) fun u =>
      stripe (layout p t (groups b W) i) (v u i))) :
    Carries w input (stackRun (layout p t b) (gather hW v)) := by
  apply assemble p t g
  intro d
  let u := row hW d
  let j := group hW d
  have hr := finite_cell (Series.natural W)
    (fun i u => stripe (layout p t (groups b W) i) (v u i)) rows u
  exact extract p t g (v u) hr j

@[simp] theorem gather_padded {b W : ℕ} (hb : 0 < b) (hW : 0 < W) (v : Value P T b) :
    gather hW (padded (W := W) hb v) = v := by
  funext i a
  simp [gather, padded]

/-- Measuring cells on the actual flat streams gives the space shrinkage used
for a smaller recursive call, including the padded last batch. -/
theorem row_layout_volume {b W : ℕ} (hW : 0 < W) (hWb : W ≤ b) (i : I) :
    W * (layout p t (groups b W) i).count ≤ 2 * (layout p t b i).count := by
  simpa only [layout, Series.count_cart, Series.count_natural] using
    row_volume_le hW hWb (p i).count (t i).count

variable {r : Regime I} {n l : I → ℕ}

/-- A descriptor which supplies the two stationary dimensions pays for both
rulers at the same exponent as the data and the prefix/suffix area. -/
private theorem geometry_of_stations {data : I → Tree} (hp : Station r p) (ht : Station r t)
    (cells : ∀ i, (p i).count * (t i).count ≤ n i)
    (header : Rip r n l input r.header) (source : Rip r n l input data) :
    ∃ k, Geometry p t (mass r n l k) input ∧ Carries (mass r n l k) input data := by
  obtain ⟨a, ha⟩ := header.chain (hp.supply (fun i =>
    (Nat.le_mul_of_pos_right _ (ht.1 i)).trans (cells i)))
  obtain ⟨b, hb⟩ := header.chain (ht.supply (fun i =>
    (Nat.le_mul_of_pos_left _ (hp.1 i)).trans (cells i)))
  obtain ⟨c, hc⟩ := source
  let k := a + b + c
  refine ⟨k, ⟨ha.larger (mass_le (by dsimp [k]; omega)),
    hb.larger (mass_le (by dsimp [k]; omega)), ⟨4, fun i => ?_⟩⟩,
    hc.larger (mass_le (by dsimp [k]; omega))⟩
  have core : ((p i).count+1) * ((t i).count+1) ≤ 4 * n i := calc
    _ ≤ (2 * (p i).count) * (2 * (t i).count) := Nat.mul_le_mul (by have := hp.1 i; omega)
        (by have := ht.1 i; omega)
    _ = 4 * ((p i).count * (t i).count) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 (cells i)
  have hm : (n i : ℝ) ≤ mass r n l k i := by
    apply le_mul_of_one_le_right (by positivity)
    exact (one_le_pow₀ (by simp : (1:ℝ) ≤ r.scale i + 1)).trans
      (le_add_of_nonneg_left (Nat.cast_nonneg _))
  exact (show ((p i).count+1:ℝ) * ((t i).count+1) ≤ 4 * (n i) by exact_mod_cast core).trans
    (mul_le_mul_of_nonneg_left hm (by norm_num))

/-- Descriptor-driven splitter in P192's record and width accounting. -/
theorem split_rip {b W : ℕ} (hb : 0 < b) (hp : Station r p) (ht : Station r t)
    (cells : ∀ i, (p i).count * (t i).count ≤ n i) (header : Rip r n l input r.header)
    (v : Value P T b) (source : Rip r n l input (stackRun (layout p t b) v)) :
    Rip r n l input (fun i => stripe (Series.natural W) fun u =>
      stripe (layout p t (groups b W) i) (padded hb v u i)) := by
  obtain ⟨k,g,hr⟩ := geometry_of_stations p t hp ht cells header source
  exact ⟨k, split p t hb g v hr⟩

/-- Descriptor-driven inverse gathering arbitrary processed rows in P192's
record and width accounting. -/
theorem merge_rip {b W : ℕ} (hW : 0 < W) (hp : Station r p) (ht : Station r t)
    (cells : ∀ i, (p i).count * (t i).count ≤ n i) (header : Rip r n l input r.header)
    (v : Fin W → Value P T (groups b W))
    (rows : Rip r n l input (fun i => stripe (Series.natural W) fun u =>
      stripe (layout p t (groups b W) i) (v u i))) :
    Rip r n l input (stackRun (layout p t b) (gather hW v)) := by
  obtain ⟨k,g,hr⟩ := geometry_of_stations p t hp ht cells header rows
  exact ⟨k, merge p t hW g v hr⟩

end BatchRows

end NearSquareRoot
end Computability
end OAI
