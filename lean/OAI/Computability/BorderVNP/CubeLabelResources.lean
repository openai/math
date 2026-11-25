import OAI.Computability.BorderVNP.CubeLabelDirectoryProgram
import OAI.Computability.BorderVNP.CubeLabelTraffic

/-! # A common word envelope for initialization and all public label trials -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial Cube.MeanChoice TeamScales Filter

/-- Aggregate compressed widths before self-cables are absorbed. -/
def inputWidth (l : Layout) (m : ℕ → ℕ) := sumWidth (Cable.width ∘ cableAt l m) l.cableCount +
  sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount

/-- Dropping absorbed self-cables only decreases the volume used by the chooser. -/
theorem totalWidth_le_inputWidth (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) :
    totalWidth (fromTables l m ep) ≤ inputWidth l m := by
  rw [totalWidth_tables]
  exact Nat.add_le_add_right (sumWidth_le le_rfl fun _ _ => by
    simp only [Function.comp_apply, liveWidth]; split <;> omega) _

/-- A single polynomial bound covers the number of bins, each incident sum, and
the entire accumulated trial score, also for empty source arrays. -/
def wordEnvelope (Z volume : ℕ) := 4*(volume+1)^2*(Z+1)^6

/-- Numerical capacities required by the row and cache proof. -/
theorem wordCaps (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (w : ℕ)
    (cap : wordEnvelope l.labels (inputWidth l m) < 2^w) :
    l.labels^2+l.labels < 2^w ∧
    sumWidth (Cable.width ∘ cableAt l m) l.cableCount*l.labels^2 < 2^w ∧
    sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount*l.labels^2 < 2^w ∧
    totalWidth (fromTables l m ep)*l.labels^2 < 2^w ∧
    2*l.labels^6*(totalWidth (fromTables l m ep))^2 < 2^w := by
  let D := inputWidth l m
  let Z := l.labels
  have hz : Z^2 ≤ (Z+1)^6 := (Nat.pow_le_pow_left (Nat.le_succ Z) 2).trans
    (Nat.pow_le_pow_right (by omega) (by decide))
  have hd : D ≤ (D+1)^2 := (Nat.le_succ D).trans (Nat.le_self_pow (by decide) _)
  have hC : sumWidth (Cable.width ∘ cableAt l m) l.cableCount ≤ D := Nat.le_add_right ..
  have hD : sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount ≤ D := Nat.le_add_left ..
  have hL : totalWidth (fromTables l m ep) ≤ D := totalWidth_le_inputWidth l m ep
  have hscaled : D*Z^2 < 2^w := calc
    _ ≤ (D+1)^2*(Z+1)^6 := Nat.mul_le_mul hd hz
    _ ≤ 4*(D+1)^2*(Z+1)^6 := by gcongr; exact Nat.le_mul_of_pos_left _ (by decide)
    _ < _ := cap
  refine ⟨?_,(Nat.mul_le_mul_right _ hC).trans_lt hscaled,
    (Nat.mul_le_mul_right _ hD).trans_lt hscaled,(Nat.mul_le_mul_right _ hL).trans_lt hscaled,?_⟩
  · have base : Z^2+Z ≤ (Z+1)^2 := by nlinarith
    have hs : (Z+1)^2 ≤ (Z+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
    exact ((base.trans hs).trans (Nat.le_mul_of_pos_left _ (by positivity : 0 < 4*(D+1)^2))).trans_lt cap
  · have bound : 2*Z^6*(totalWidth (fromTables l m ep))^2 ≤ 4*(D+1)^2*(Z+1)^6 := calc
      _ ≤ 4*(Z+1)^6*(D+1)^2 := by gcongr <;> omega
      _ = _ := by ring
    exact bound.trans_lt cap

/-- The common envelope also covers the constructor's raw, unscaled and
single-label-scaled input volumes. -/
theorem Fits.of_envelope (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (w : ℕ)
    (hz : 0 < l.labels) (addresses : l.dataMean+l.labels ≤ 2^w)
    (cap : wordEnvelope l.labels (inputWidth l m) < 2^w) : Fits l w m := by
  obtain ⟨_,cab,dat,_,_⟩ := wordCaps l m ep w cap
  have pos : 0 < l.labels^2 := pow_pos hz 2
  refine ⟨addresses,(Nat.le_mul_of_pos_right _ pos).trans_lt cab,
    (Nat.le_mul_of_pos_right _ pos).trans_lt dat,?_⟩
  exact (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)).trans_lt dat

/-- For the paper's alphabet and traffic volume, the complete word envelope and all
polynomial base addresses fit one team word, uniformly in the number of processors. -/
theorem eventually_envelope {α ξ : ℝ} (hα : 0 < α) (a : ℕ) (small : α*a < 1/10^6)
    (hξ : 0 ≤ ξ) (B d : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ r R w base volume : ℕ, 1 ≤ r → R ≤ n →
    logWidth r n^2 ≤ w → base ≤ (2*n*r)^d → volume ≤ B*(exterior ξ r n*R+1) →
    base + wordEnvelope (labelCount α a n) volume < 2^w := by
  filter_upwards [eventually_label_word hα a small hξ (4*(B+1)^2) d] with n bound
  intro r R w base volume hr hR hw hb hv
  let W := exterior ξ r n * R
  have hvol : volume+1 ≤ (B+1)*(W+1) := by change volume ≤ B*(W+1) at hv; rw [Nat.add_mul]; omega
  apply lt_of_le_of_lt _ (bound r R w base hr hR hw hb)
  apply Nat.add_le_add_left
  unfold wordEnvelope
  rw [show 4*(B+1)^2*(W+1)^2 = 4*((B+1)*(W+1))^2 by ring]
  gcongr

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
