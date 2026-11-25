import OAI.Hierarchy.ProbeCoreFootprint
import OAI.Hierarchy.TaggedShorterStageDirectory

namespace OAI
/-! # Row and address counts for the public core catalogue -/

noncomputable section
namespace Hierarchy.TaggedShorterSupergroups
open ProbeStage
/-- One fixed physical directory for all dyadic widths and all selectors. -/
def stageDir (h W roles pad : ℕ) (padding : 2*roles≤2^pad) :
    Directory (reserved h W roles) (2^superAddress W pad h) :=
  (purchase_stages h W roles pad padding).choose

end Hierarchy.TaggedShorterSupergroups

namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open ProbeStage CoreBoard TaggedShorterSupergroups
open scoped Classical BigOperators
/-- The fixed-format coefficient for the public core row count. -/
def coreFactor (S : PurchaseSampler) (d k : ℕ) :=
  let n := 18*(d-1)+1
  let cap := 4^(rounds d+1)
  let stages := 1+2*k
  let cols := 2+2*n*cap
  cols*(2*k+4*k*k+stages)+(n*cap*S.degree+n)*stages

theorem rows_linear (S : PurchaseSampler) (h W k : ℕ) :
    Fintype.card (Edges S h (2^W) k)≤ coreFactor S (2^W) k * 2^h :=
  edge_count S (2^W) k (Nat.two_pow_pos _) h

/-- The fixed dyadic stage height fits in a linear range of cells at every
input height, including the central stage's bounded remainder. -/
theorem packed_height (W pad h : ℕ) :
    2^superAddress W pad h≤2^(9*2^W+18*(2^W-1)+2+pad)*2^h := by
  let d := 2^W
  have dd : 1≤ d := Nat.two_pow_pos _
  have digitBound : 9*digit h d ≤ h := calc
    9*digit h d ≤ (9*d)*digit h d := Nat.mul_le_mul_right _ (by omega)
    _ ≤ h := by simpa [digit,Nat.mul_comm] using Nat.div_mul_le_self h (9*d)
  have power : 2^(9*digit h d)≤2^h := Nat.pow_le_pow_right (by decide) digitBound
  unfold superAddress
  rw [pow_add,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ power

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
