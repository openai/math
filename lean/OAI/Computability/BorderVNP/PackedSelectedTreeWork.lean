import OAI.Computability.BorderVNP.PackedSelectedEpochOffset
import OAI.Computability.BorderVNP.PackedResources

/-! # Summing the measured public combining work over the true copy tree

All possible count words at each node are charged together with that node's
Boolean gates. The number of nodes at a height cancels the child factors
already included in the occupied and padded rows at that height.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Shortening PublicCapacity Packing Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The common geometric factor used by the inner clause of the history compiler. -/
def receiptFactor (fan bins A p : ℕ) := (fan+bins+3)*A*63^p

/-- Convert the literal selected-node resource estimate to the physical
rectangle and processor address length of that same public stage. -/
theorem receipt_rowWork {r n start t : ℕ} {j : Fin S.rounds} {den cut : ℕ}
    (ranges : Ranges S r n start t j den cut) (A p cost : ℕ) :
    let shape := before S start t j
    let k := S.fanIn
    let vol := CoverScale.sites (Cube D) (stageLevel S start t (j.val+1))
    let V := CoverScale.sites (Cube D) start
    let L := logWidth r n
    let seeds := seedCount S start t j
    cost ≤ (k*shape.sites+2*(k*shape.edges)+k*(vol+1)+seeds+1)*A*
      (Nat.clog 2 (2^(60*L)+vol+2)+1)^p →
    cost ≤ rowWork (receiptFactor k (bins S) A p) V L p (shape.parallel k) := by
  intro shape k vol V L seeds hc
  have ht : vol ≤ V := ranges.tiles
  have hs : seeds ≤ V*bins S := by
    have hb := Finset.le_sup (f := fun i => Fintype.card (S.source.pattern i).bins.Bin) (Finset.mem_univ j)
    change Fintype.card (S.source.pattern j).bins.Bin ≤ bins S at hb
    simpa only [seeds,seedCount,dite_eq_left j.isLt,CoverScale.sites,vol] using Nat.mul_le_mul ht hb
  let rows := (shape.parallel k).volume V
  have hrow : k*shape.sites+2*(k*shape.edges)+k*(vol+1)+seeds+1 ≤ (k+bins S+3)*rows := by
    change k*shape.sites+2*(k*shape.edges)+k*(vol+1)+seeds+1 ≤ (k+bins S+3)*(k*shape.sites+k*shape.edges+V+1)
    have hvol := Nat.mul_le_mul_left k (Nat.succ_le_succ ht)
    nlinarith only [hs,hvol,Nat.zero_le (k*(k*shape.sites+k*shape.edges)),Nat.zero_le (bins S*(k*shape.sites+k*shape.edges+1))]
  have log : Nat.clog 2 (2^(60*L)+vol+2)+1 ≤ 63*L := ranges.words.2.2.2.2.2.2.2.2.2.2
  calc
    cost ≤ _ := hc
    _ ≤ ((k+bins S+3)*rows)*A*(63*L)^p :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hrow) (Nat.pow_le_pow_left log _)
    _ = _ := by dsimp only [rowWork,receiptFactor,rows]; rw [mul_pow]; ring

/-- Number of selected nodes at each static level times their actual
resource counts, summed over the entire rooted physical history. -/
def treeWork (fan rounds T : ℕ) (cost : Fin T → Fin rounds → ℕ) :=
  ∑ tj : Fin T × Fin rounds, fan^(rounds*T-(rounds*tj.1.val+tj.2.val+1))*cost tj.1 tj.2

/-- The true number of visited copies multiplies the attained row rectangle.
Its fan-in powers cancel exactly against the powers in that rectangle. -/
theorem treeWork_le (start T C L p : ℕ)
    (seeds : ∀ t j, seedCount S start t j ≤ CoverScale.sites (Cube D) start*bins S)
    (cost : Fin T → Fin S.rounds → ℕ)
    (measured : ∀ t j, cost t j ≤ rowWork C (CoverScale.sites (Cube D) start) L p
      ((before S start t j).parallel S.fanIn)) :
    treeWork S.fanIn S.rounds T cost ≤
      (T*S.rounds*((epochRowFactor S)^T*(bottom (D := D) start).volume (CoverScale.sites (Cube D) start)))*(C*L^p) := by
  let V := CoverScale.sites (Cube D) start
  let mult (tj : Fin T × Fin S.rounds) := S.fanIn^(S.rounds*T-(S.rounds*tj.1.val+tj.2.val+1))
  let rows (tj : Fin T × Fin S.rounds) := ((before S start tj.1 tj.2).parallel S.fanIn).volume V
  have hrow := tree_volume e S.positiveFanIn S.rounds (interiors S) V (bins S) (seedCount S start)
    seeds (bottom (D := D) start) T
  change (∑ tj : Fin T × Fin S.rounds, mult tj * rows tj) ≤
    T*S.rounds*((epochRowFactor S)^T*(bottom (D := D) start).volume V) at hrow
  change (∑ tj : Fin T × Fin S.rounds, mult tj*cost tj.1 tj.2) ≤ _
  calc
    _ ≤ ∑ tj : Fin T × Fin S.rounds, mult tj * rows tj * (C*L^p) :=
      Finset.sum_le_sum fun tj _ => (Nat.mul_le_mul_left _ (measured tj.1 tj.2)).trans_eq (by unfold rowWork; dsimp only [rows]; ring)
    _ = (∑ tj : Fin T × Fin S.rounds, mult tj * rows tj) * (C*L^p) := by rw [Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hrow

/-- All measured selected combining gates, child guards and guessed bits
together fit below the exponent 0.915, uniformly in the number of processors. -/
theorem eventually_treeWork {a x : ℕ} (s : EpochScales S a x) (C p : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      let T := epochs s.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      (∀ t j, seedCount S start t j ≤ V*bins S) →
      ∀ cost : Fin T → Fin S.rounds → ℕ,
        (∀ t j, cost t j ≤ rowWork C V (logWidth r n) p ((before S start t j).parallel S.fanIn)) →
        (treeWork S.fanIn S.rounds T cost:ℝ) < r*(n:ℝ)^(915/1000:ℝ) := by
  let dirs := Fintype.card (DeckGrid.Direction (Fintype.card (Cube D)))
  let G := epochRowFactor S
  have hG : 1 ≤ G := epochFactor_pos e S.positiveFanIn S.rounds (interiors S) (bins S)
  have τ : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have α : 0 ≤ (s.α:ℝ) := by exact_mod_cast s.alpha_pos.le
  have hteams := s.rate (epochCopies_pos S) (epochGrowth_bounds S x).2.1
  have hrow := s.rate hG (epochGrowth_bounds S x).2.2.2.2.1
  obtain ⟨ω,hω,work⟩ := eventually_sparse_resources_below s.alpha_small τ s.tau_small (epochCopies_pos S)
    (hteams.trans (by linarith)) (by exact_mod_cast hG : 1 ≤ (G:ℝ)) hrow p (915/1000:ℝ)
    (by linarith [s.alpha_small,s.tau_small])
  let A : ℝ := S.rounds*(dirs+3)*C
  refine ⟨ω,hω,?_⟩
  filter_upwards [work 1 (by norm_num),work A (by dsimp [A]; positivity),eventually_offsets S s,eventually_ge_atTop 1]
    with n growth charge offset hn
  intro r hr hrmax T start V seeds cost measured
  have htree := treeWork_le S start T C (logWidth r n) p seeds cost measured
  have ht : (treeWork S.fanIn S.rounds T cost:ℝ) ≤
      ((T:ℝ)*S.rounds*((G:ℝ)^T*((bottom (D := D) start).volume V:ℝ)))*(C*(logWidth r n:ℝ)^p) := by
    exact_mod_cast htree
  have hw : 1 ≤ width n (s.α:ℝ) := Nat.le_floor (by
    simpa using Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ)) α)
  have g : (G:ℝ)^T ≤ (n:ℝ)^(1/100:ℝ) := by
    have gh := (growth r hr hrmax).2.1
    have hwidth : 1 ≤ (width n (s.α:ℝ):ℝ) := by exact_mod_cast hw
    calc
      _ ≤ (G:ℝ)^T*(width n (s.α:ℝ):ℝ) := le_mul_of_one_le_right (by positivity) hwidth
      _ ≤ (width n (1/100):ℝ) := by simpa only [one_mul] using gh
      _ ≤ _ := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have team : 1 ≤ (teams s.α s.τ (epochCopies S) n:ℝ) := by
    have tpos : 1 ≤ teams s.α s.τ (epochCopies S) n := Nat.mul_pos hw (Nat.one_le_pow T _ (epochCopies_pos S))
    exact_mod_cast tpos
  have init : ((bottom (D := D) start).volume V:ℝ) ≤ (dirs+3:ℝ)*(r*(n:ℝ)^(9/10:ℝ)) := by
    have size : ((bottom (D := D) start).volume V:ℝ) ≤ (dirs+3:ℝ)*V := by
      exact_mod_cast grid_volume (Fintype.card_pos : 1 ≤ V) dirs
    exact size.trans (mul_le_mul_of_nonneg_left (offset r hr).2 (by positivity))
  calc
    _ ≤ _ := ht
    _ ≤ (T:ℝ)*S.rounds*((n:ℝ)^(1/100:ℝ)*((dirs+3)*(r*(n:ℝ)^(9/10:ℝ))))*(C*(logWidth r n:ℝ)^p) := by gcongr
    _ ≤ A*T*(teams s.α s.τ (epochCopies S) n:ℝ)*(r*(n:ℝ)^(9/10:ℝ))*(n:ℝ)^(1/100:ℝ)*(logWidth r n:ℝ)^p := by
      dsimp only [A]
      calc
        _ = ((S.rounds:ℝ)*(dirs+3)*C*T*1)*(r*(n:ℝ)^(9/10:ℝ))*(n:ℝ)^(1/100:ℝ)*(logWidth r n:ℝ)^p := by ring
        _ ≤ _ := by gcongr
    _ < _ := (charge r hr hrmax).2.2

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
