import OAI.Computability.MultitapeWeakETH.FieldColumns
import OAI.LinearAlgebra.MatrixMultiplication.Duality.EntropyHelpers
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity

/-! # Charging only the low input coordinates at the original sites -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open MatrixMultiplication MatrixMultiplication.Foundation Finset
open scoped Classical BigOperators
noncomputable section
variable {n b L : ℕ} (G : Network n b)

local instance (v : Fin G.vertices) : Fintype (G.localBits G.input v) := by
  unfold Network.localBits
  infer_instance

def Varying (L : ℕ) (v : Fin G.vertices) :=
  {i : G.localBits G.input v // n-1-i.val.val < L}

instance (v : Fin G.vertices) : Fintype (Varying G L v) := by
  unfold Varying Network.localBits
  infer_instance

private theorem bit_site (v : Fin G.vertices) (i : G.localBits G.input v) (hb : 0 < b) :
    G.input (Network.blockIndex hb i.val) = v := by
  obtain ⟨j,hj,hv⟩ := i.property
  exact (congrArg G.input (Fin.ext hj.symm)).trans hv

theorem varying_card (hb : 0 < b) (v : Fin G.vertices) :
    Fintype.card (Varying G L v) ≤ b := by
  let pos (i : Varying G L v) := n-1-i.val.val.val
  let rem (i : Varying G L v) : Fin b := ⟨pos i%b,Nat.mod_lt _ hb⟩
  have inj : Function.Injective rem := by
    intro i j h
    have same := G.input.injective ((bit_site G v i.val hb).trans (bit_site G v j.val hb).symm)
    have div : pos i / b = pos j / b := congrArg Fin.val same
    have mod : pos i % b = pos j % b := congrArg Fin.val h
    have split := Nat.mod_add_div (pos i) b
    rw [div,mod,Nat.mod_add_div] at split
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    dsimp [pos] at split
    have hi := i.val.val.isLt
    have hj := j.val.val.isLt
    omega
  simpa using Fintype.card_le_of_injective rem inj

theorem total_varying (hb : 0 < b) : ∑ v, Fintype.card (Varying G L v) ≤ L := by
  let coord (s : (v : Fin G.vertices) × Varying G L v) : Fin L :=
    ⟨n-1-s.2.val.val.val,s.2.property⟩
  have inj : Function.Injective coord := by
    rintro ⟨v,i⟩ ⟨w,j⟩ eq
    have h : n-1-i.val.val.val = n-1-j.val.val.val := congrArg Fin.val eq
    have hi := i.val.val.isLt
    have hj := j.val.val.isLt
    have bits : i.val.val = j.val.val := Fin.ext (by omega)
    have sites := (bit_site G v i.val hb).symm
    rw [bits,bit_site] at sites
    subst w
    exact congrArg (Sigma.mk v) (Subtype.ext (Subtype.ext bits))
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_le_of_injective coord inj

theorem joinPayload_high (fits : L ≤ n) (h : Fin (2^(n-L))) (l : Fin (2^L)) :
    (joinPayload n L fits (h,l)).val / 2^L = h.val := by
  change (l.val+2^L*h.val)/2^L = h.val
  rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt l.isLt,zero_add]

/-- All rows in the support have the same high bits. At a vertex, its
input pin factors through the Boolean coordinates below the payload cutoff. -/
theorem input_entropy {A : Type} [Fintype A] (p : FiniteLaw A) (fits : L ≤ n)
    (high : Fin (2^(n-L))) (low : A → Fin (2^L)) (v : Fin G.vertices) :
    let row (a : A) := residueWord n (joinPayload n L fits (high,low a))
    finiteEntropy (p.map (fun a (i : G.localBits G.input v) => row a i.val)).mass ≤
      Fintype.card (Varying G L v)*Real.log 2 := by
  intro row
  let restrict (a : A) (i : Varying G L v) := row a i.val.val
  let fill (s : Varying G L v → Bool) (i : G.localBits G.input v) :=
    if h : n-1-i.val.val < L then s ⟨i,h⟩ else high.val.testBit (n-1-i.val.val-L)
  have same (a : A) (i : G.localBits G.input v) : fill (restrict a) i = row a i.val := by
    by_cases h : n-1-i.val.val < L
    · simp [fill,h,restrict]
    · simp only [fill,h,dite_false,row,residueWord_digit]
      rw [← joinPayload_high fits high (low a),Nat.testBit_div_two_pow]
      congr 1
      omega
  have h := (p.map restrict).map_entropy_le fill
  rw [DualEntropyHelpers.map_comp_mass] at h
  simp_rw [funext (same _)] at h
  apply h.trans
  have bound := (p.map restrict).entropy_le_log_card
  simpa only [Fintype.card_fun,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] using bound

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
