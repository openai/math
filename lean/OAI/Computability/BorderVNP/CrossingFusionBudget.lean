import OAI.Computability.BorderVNP.CrossingFusionFlags
import OAI.Computability.BorderVNP.CrossingFusionStageFrames
import OAI.Computability.VPVNP.PolynomialBounds

/-! # Uniform sizes of the Boolean blocks in an iterated crossing

One envelope bounds the word lengths, cutoffs, and both resources of every
local signed checker. The resulting gate bounds are independent of the
orientations and of the chosen side.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

variable {m d : ℕ} {w : WireStates (leastEnergy m) (2^m)} {left : Bool} {b : Fin d → Bool}

/-- Common bound on the scalar resource of any stage, expressed in the alphabet size. -/
def checkerCap (q : ℕ) : ℕ := (q+2)^420

/-- An envelope for all blocks before combining their Boolean outputs. -/
def blockCap (B : ℕ) : ℕ := 256*(B+1)^5

/-- The polynomial for local resource bounds has absolute degree and coefficient. -/
theorem checkerCap_polynomial : VPVNP.PolynomiallyBounded checkerCap :=
  (VPVNP.PolynomiallyBounded.id.add (.const 2)).pow 420

/-- The local resource envelope is closed under the shared word and state checks. -/
theorem blockCap_polynomial : VPVNP.PolynomiallyBounded blockCap :=
  (VPVNP.PolynomiallyBounded.const 256).mul (VPVNP.PolynomiallyBounded.succ.pow 5)

set_option exponentiation.threshold 512 in
private theorem square_le_cap (q : ℕ) : (q+2)^2 ≤ checkerCap q :=
  @Nat.pow_le_pow_right (q+2) (Nat.zero_lt_succ _) 2 420 (by decide)

/-- All the parameters used in the fusion blocks, in the case of the paper's
polynomial local checkers. -/
theorem checkerCap_dimensions {m d p : ℕ} (hd : d ≤ m) (hp : p ≤ 2^m)
    (hH : 2*leastEnergy m ≤ 2^m) :
    let q := 2^m; let B := checkerCap q
    d ≤ B ∧ p ≤ B ∧ m ≤ B ∧ q ≤ B ∧ 2*leastEnergy m ≤ B ∧
    Nat.clog 2 (2*leastEnergy m) ≤ B ∧ d*leastEnergy m ≤ B := by
  let q := 2^m
  have hm : m ≤ q := Nat.lt_two_pow_self.le
  have hq : q ≤ checkerCap q := by
    refine (Nat.le_add_right q 2).trans ?_
    simpa only [checkerCap, pow_one] using Nat.pow_le_pow_right
      (show 0 < q+2 by omega) (by decide : 1≤420)
  have hlog : Nat.clog 2 (2*leastEnergy m) ≤ 2*leastEnergy m :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  refine ⟨(hd.trans hm).trans hq, hp.trans hq, hm.trans hq, hq, hH.trans hq,
    hlog.trans (hH.trans hq), ?_⟩
  calc
    _ ≤ q*q := Nat.mul_le_mul (hd.trans hm) (by omega)
    _ ≤ (q+2)^2 := by rw [pow_two]; gcongr <;> omega
    _ ≤ checkerCap q := square_le_cap q

/-- Count the physical input bits, including one shared mask per stage boundary. -/
theorem raw_card_le (f : Checkers w left b) (B : ℕ) (hd : d ≤ B) (hm : m ≤ B)
    (hlog : Nat.clog 2 (2*leastEnergy m) ≤ B) (hE : d*leastEnergy m ≤ B)
    (hg : ∀ i, (f i).guesses ≤ B) : Fintype.card (Raw f) ≤ blockCap B := by
  have hstates : ∑ i : Fin (d+1), i.val*leastEnergy m ≤ (d+1)*B := by
    apply le_trans (Finset.sum_le_sum (g := fun _ => B) (fun i _ =>
      (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ i.isLt)).trans hE))
    simp
  have hgs : ∑ i : Fin d, (f i).guesses ≤ d*B := by
    apply le_trans (Finset.sum_le_sum (g := fun _ => B) (fun i _ => hg i))
    simp
  simp only [Raw, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin]
  calc
    _ ≤ d*m + (d*Nat.clog 2 (2*leastEnergy m) + ((d+1)*B + d*B)) := by gcongr
    _ ≤ B*B + (B*B + ((B+1)*B + B*B)) := by gcongr
    _ ≤ blockCap B := by unfold blockCap; ring_nf; omega

/-- Gate bound for one local checker after reading the shared query bits. -/
theorem stage_size_le (f : Checkers w left b) (i : Fin d) (B : ℕ)
    (hq : 2^m ≤ B) (hm : m ≤ B) (hH : 2*leastEnergy m ≤ B)
    (hlog : Nat.clog 2 (2*leastEnergy m) ≤ B) (hE : d*leastEnergy m ≤ B)
    (hs : (f i).frame.size ≤ B) (hg : (f i).guesses ≤ B) :
    (stageFrame f i).size ≤ blockCap B := by
  have h₁ : i.val*leastEnergy m ≤ B :=
    (Nat.mul_le_mul_right _ i.isLt.le).trans hE
  have h₂ : i.val*leastEnergy m + leastEnergy m ≤ B := by
    rw [← Nat.succ_mul]
    exact (Nat.mul_le_mul_right _ i.isLt).trans hE
  calc
    _ ≤ _ := stageFrame_size f i
    _ ≤ B+(B+B+B+B+B)*(3*(B+B)+2) := by gcongr
    _ ≤ blockCap B := by unfold blockCap; ring_nf; omega

/-- Gate bound for one mask validity check. -/
theorem state_size_le (f : Checkers w left b) (i : Fin (d+1)) (B : ℕ)
    (hE : d*leastEnergy m ≤ B) : (stateFrame f i).size ≤ blockCap B := by
  have hi : i.val*leastEnergy m ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ i.isLt)).trans hE
  rw [stateFrame_size]
  calc
    _ ≤ _ := StateIndex.validFrame_size _
    _ ≤ (B+(2*B+1)*(B+2))*(1+B*(4*B+17)) := by gcongr
    _ ≤ blockCap B := by unfold blockCap; ring_nf; omega

/-- Gate bound for the final ranking and all terminal and bridge one-hot flags. -/
theorem flags_size_le {M E p : ℕ} (addr : CutBit d M (stateCountAt E) ↪ Fin p × Fin m)
    (B : ℕ) (hd : d ≤ B) (hp : p ≤ B) (hm : m ≤ B) (hq : 2^m ≤ B)
    (hM : M ≤ B) (hlog : Nat.clog 2 M ≤ B) (hE : E ≤ B) :
    (FusionFlags.frame addr).size ≤ blockCap B := by
  calc
    _ ≤ _ := FusionFlags.frame_size addr
    _ ≤ (B+(2*B+1)*(B+2))*(1+B*(4*B+17)) +
      ((B+B)*B+B*B) + ((B+B)*B+1)*(B*3+2+B*(B*(B*3+3)+3)+2) := by gcongr
    _ ≤ blockCap B := by unfold blockCap; ring_nf; omega

/-- Resource allowance for the complete gate frame, including its final acceptance
and output-selection layer. -/
def fullCap (B : ℕ) : ℕ := 1024*(B+2)^7

/-- Source length at which the signed universal family has room for the weighted
Boolean transcript of any crossing orientation. -/
def sourceCap (q : ℕ) : ℕ := 100000000000 * (fullCap (checkerCap q) + 1)^6

/-- The orientation-independent source length is an absolute polynomial in the alphabet size. -/
theorem sourceCap_polynomial : VPVNP.PolynomiallyBounded sourceCap := by
  have h : VPVNP.PolynomiallyBounded fullCap :=
    (VPVNP.PolynomiallyBounded.const 1024).mul ((VPVNP.PolynomiallyBounded.id.add (.const 2)).pow 7)
  exact (VPVNP.PolynomiallyBounded.const 100000000000).mul
    (((h.comp checkerCap_polynomial).add (.const 1)).pow 6)

/-- The gate allowance for one block fits the complete-frame allowance. -/
theorem blockCap_le_fullCap (B : ℕ) : blockCap B ≤ fullCap B := by
  unfold blockCap fullCap
  ring_nf
  omega

/-- The output slots consist of the signed flags and the external one-hot bits. -/
theorem output_count_le_fullCap {B d p q : ℕ} (hd : d ≤ B) (hp : p ≤ B) (hq : q ≤ B) :
    d+(d+p)*q ≤ fullCap B := by
  calc
    _ ≤ B+(B+B)*B := by gcongr
    _ ≤ _ := by unfold fullCap; ring_nf; omega

/-- Sum the actual stage lists and include the cost of the final layer that reads
the shared status and output wires. -/
theorem total_size_le_fullCap {B d p q flags size : ℕ} (stage : Fin d → ℕ)
    (state : Fin (d+1) → ℕ) (hd : d ≤ B) (hp : p ≤ B) (hq : q ≤ B)
    (hf : flags ≤ blockCap B) (hg : ∀ i, stage i ≤ blockCap B)
    (hs : ∀ i, state i ≤ blockCap B)
    (hall : size ≤ flags + (1 + ∑ i, stage i) + (1 + ∑ i, state i) +
      (1+d+(d+p)*q) * (30*(d+2))) : size ≤ fullCap B := by
  have hstage : ∑ i, stage i ≤ d*blockCap B := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => blockCap B) (fun i _ => hg i)
  have hstate : ∑ i, state i ≤ (d+1)*blockCap B := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => blockCap B) (fun i _ => hs i)
  refine hall.trans ?_
  calc
    _ ≤ blockCap B + (1 + d*blockCap B) + (1 + (d+1)*blockCap B) +
      (1+d+(d+p)*q) * (30*(d+2)) := by gcongr
    _ ≤ blockCap B + (1 + B*blockCap B) + (1 + (B+1)*blockCap B) +
      (1+B+(B+B)*B) * (30*(B+2)) := by gcongr
    _ ≤ fullCap B := by unfold blockCap fullCap; ring_nf; omega

/-- The three resource premises of the weighted-frame projection, uniformly over
the crossing's orientation and side. The input is the physical shared-bit layout. -/
theorem side_resources {p size : ℕ} (f : Checkers w left b)
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m)
    (hd : d ≤ m) (hp : p ≤ 2^m) (hH : 2*leastEnergy m ≤ 2^m)
    (locals : ∀ i, (f i).guesses ≤ checkerCap (2^m) ∧ (f i).frame.size ≤ checkerCap (2^m))
    (hall : size ≤ (FusionFlags.frame addr).size +
      (1 + ∑ i, (stageFrame f i).size) + (1 + ∑ i, (stateFrame f i).size) +
      (1+d+(d+p)*2^m) * (30*(d+2))) :
    let B := fullCap (checkerCap (2^m))
    Fintype.card (Raw f) ≤ B ∧ d+(d+p)*2^m ≤ B ∧ size ≤ B := by
  obtain ⟨hd', hp', hm', hq', hH', hlog, hE⟩ := checkerCap_dimensions hd hp hH
  refine ⟨(raw_card_le f _ hd' hm' hlog hE (fun i => (locals i).1)).trans
    (blockCap_le_fullCap _), output_count_le_fullCap hd' hp' hq', ?_⟩
  apply total_size_le_fullCap _ _ hd' hp' hq' _ _ _ hall
  · exact flags_size_le addr _ hd' hp' hm' hq' hH' hlog hE
  · exact fun i => stage_size_le f i _ hq' hm' hH' hlog hE (locals i).2 (locals i).1
  · exact fun i => state_size_le f i _ hE

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
