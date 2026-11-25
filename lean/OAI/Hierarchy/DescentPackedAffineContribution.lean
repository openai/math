import OAI.Hierarchy.DescentPackedSplitContribution
import OAI.Hierarchy.DescentGroupedAffineScore
import OAI.Hierarchy.DescentWinningRows
import OAI.Hierarchy.DescentColonyScorePermutation
import OAI.Hierarchy.DescentColonyMultipliers

namespace OAI
/-! # Affine imbalance of a physical packed site record

The record contains the complete depth flags and the bounded counts of the
outgoing blocks. One presence bit separates inactive vector lanes from every
possible live record. For each affine candidate, summing the decoded local
contributions gives its actual score on the selected dyadic slabs.
-/
namespace Hierarchy.DescentAffineColors.PackedContribution
open DescentColonies DescentGL DescentBinaryField DescentSIMDLookup WinningSlabs PackedSplit
open scoped BigOperators Classical
open scoped Fin.CommRing
noncomputable section
variable {G H k b : ℕ}

def width (k b : ℕ) := 1+(k*2^k+b*2^k)

private def pair (k b : ℕ) : Cell (k*2^k) × Cell (b*2^k) ≃ Cell (k*2^k+b*2^k) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 (k*2^k) (b*2^k)).symm)

def encode (flags : Flags k) (outgoing : Block k→Cell b) : Cell (width k b) :=
  present (pair k b (encodeFlags flags,DescentSIMDLookup.encode b (2^k) outgoing))

theorem encode_ne_zero (flags : Flags k) (outgoing : Block k→Cell b) : encode flags outgoing≠0 :=
  present_ne_zero _

private def masked (flags : Flags k) (outgoing : Block k→Cell b) (q : Fin (keys k).length) (x : Block k) :=
  let nm := keyName k q.val
  if depth flags x=nm.1 ∧ group nm.1 x=nm.2 then (outgoing x).val else 0

def contribution (flags : Flags k) (outgoing : Block k→Cell b) (j : Candidate k) :=
  ∑ q : Fin (keys k).length, difference (side (masked flags outgoing q) j true) (side (masked flags outgoing q) j false)

def value (j : Candidate k) (c : Cell (width k b)) : ℕ :=
  if c=0 then 0 else
    let z := (pair k b).symm (strip c)
    contribution (decodeFlags z.1) ((DescentSIMDLookup.encode b (2^k)).symm z.2) j

@[simp] theorem value_zero (j : Candidate k) : value (b:=b) j 0=0 := by simp [value]

@[simp] theorem value_encode (flags : Flags k) (outgoing : Block k→Cell b) (j : Candidate k) :
    value j (encode flags outgoing)=contribution flags outgoing j := by
  rw [value,ite_eq_right (encode_ne_zero flags outgoing)]
  simp [encode]

theorem sum_rows (rows : Fin G→Scan.Buffer (Fin H) k) (outgoing : Fin G→Fin H→Block k→Cell b)
    (j : Candidate k) :
    (∑ v,∑ g,value j (encode (actualFlags (rows g) v) (outgoing g v)))=
      score (worldValue rows (fun g v x=>(outgoing g v x).val)) j := by
  have row (g : Fin G) (v : Fin H) (q : Fin (keys k).length) :
      masked (actualFlags (rows g) v) (outgoing g v) q =
        worldValue rows (fun i u x=>(outgoing i u x).val) ((directory G H k) ((g,v),q)) := by
    funext x
    simp only [worldValue,Equiv.symm_apply_apply,masked,filtered,member,depth_actualFlags]
  rw [Finset.sum_comm]
  unfold score
  rw [←(directory G H k).sum_comp]
  simp only [Fintype.sum_prod_type,value_encode,contribution,row]

private def words (b : ℕ) (f : Block k→ℕ) (x : Block k) : Cell b :=
  ⟨f x % 2^b,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The actual physical cell compiled from the winning retained flags and
outgoing-count tape, before evaluating any affine candidate. -/
def actual (b : ℕ) (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (g : Fin G) (v : Fin H) : Cell (width k b) :=
  encode (actualFlags (Selected.winningRows inc W D cap a μ g) v) (words b (Selected.winningAmounts amt a μ g v))

private theorem amounts_fit (a : Bits k) (μ : Nonzero k) (amt : Fin G→Fin H→Block k→ℕ)
    (room : ∀ g v x,amt g v x<2^b) (g : Fin G) (v : Fin H) (x : Block k) :
    Selected.winningAmounts amt a μ g v x<2^b := by
  unfold Selected.winningAmounts multiplierLoad
  split
  · exact Nat.two_pow_pos _
  · apply room

/-- Summing the single-site lookups in physical site-major order reproduces
all interval contributions of the affine estimator, including empty slabs. -/
theorem sum_value (b : ℕ) (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (j : Candidate k) (room : ∀ g v x,amt g v x<2^b) :
    (∑v,∑g,value j (actual b inc W amt D cap a μ g v))=
      score (GroupedScan.groupedSlabs inc W amt D cap a μ) j := by
  let rows := Selected.winningRows inc W D cap a μ
  let counts := Selected.winningAmounts amt a μ
  have val (g v x) : (words b (counts g v) x).val=counts g v x :=
    Nat.mod_eq_of_lt (amounts_fit a μ amt room g v x)
  simpa only [actual,rows,counts,GroupedScan.groupedSlabs,val] using
    sum_rows rows (fun g v=>words b (counts g v)) j

theorem score_le_rearranged_mass (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (j : Candidate k) :
    score (GroupedScan.groupedSlabs inc W amt D cap a μ) j ≤
      ∑g,∑v,∑x,Selected.winningAmounts amt a μ g v x :=
  (score_le _ j).trans_eq (RosterPaint.mass ..)

/-- For the genuine binary-field multiplier every block has one preimage.
The public sum bound can therefore be charged to the original outgoing mass. -/
theorem score_le_mass (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (hk : 0<k) (μ : Nonzero k) (j : Candidate k) :
    score (GroupedScan.groupedSlabs inc W amt D cap (modulus hk) μ) j ≤ ∑g,∑v,∑x,amt g v x := by
  have perm (g : Fin G) (v : Fin H) :
      (∑x,Selected.winningAmounts amt (modulus hk) μ g v x)=∑x,amt g v x := by
    unfold Selected.winningAmounts
    simp only [multiplierLoad_pullback _ _ _ _ (multiplier_native hk μ)]
    exact Equiv.sum_comp (rearrange (multiplier hk μ)).symm (amt g v)
  simpa only [perm] using score_le_rearranged_mass inc W amt D cap (modulus hk) μ j

end
end Hierarchy.DescentAffineColors.PackedContribution

end OAI
