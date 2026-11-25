import OAI.Computability.NearSquareRoot.PrecisionMaskPacket
import OAI.Computability.NearSquareRoot.BoxMaskProgram
import OAI.Computability.NearSquareRoot.PrecisionGridCarry
import OAI.Computability.NearSquareRoot.PrecisionDigitBounds
import OAI.Computability.NearSquareRoot.PrecisionGrid

/-! # Fixed-tape output from the padded inverse-CRT grid

For each valid generated box, a common program rebuilds the mask, discards the
padding cells, rounds the valid coefficients, propagates carries, and emits the
complete plain bit string. The incoming grid is in the order returned by the
inverse CRT permutation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
noncomputable section

abbrev ValidDirectory (k : ℕ) :=
  BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k)

abbrev directoryVolume (k : ℕ) := boxVolume (CoprimeBox.box k)

/-- Payload order on the array after the inverse CRT address permutation.
The argument is given in the original residue order. -/
def afterInverseCRT {k : ℕ} {A : Type} (hv : ValidDirectory k) (v : Fin (2^k) → A) :
    Fin (2^k) → A :=
  letI := BoxFin.modulus_neZero hv
  letI : NeZero (directoryVolume k) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (BoxFin.modulus _ i)⟩
  v ∘ BoxFin.crtSlotPerm hv

/-- Payload of a given natural coefficient before the inverse routing pass. -/
def atResidue {k : ℕ} {A : Type} (hv : ValidDirectory k) (v : Fin (2^k) → A) :
    Fin (directoryVolume k) → A :=
  letI := BoxFin.modulus_neZero hv
  letI : NeZero (directoryVolume k) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (BoxFin.modulus _ i)⟩
  v ∘ BoxFin.residueSlot hv

theorem occupied_afterInverseCRT {k w : ℕ} (hv : ValidDirectory k)
    (x : Fin (2^k) → Dusk.Grain w) :
    occupiedRecords hv (afterInverseCRT hv x) = atResidue hv x := by
  let := BoxFin.modulus_neZero hv
  let : NeZero (directoryVolume k) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (BoxFin.modulus _ i)⟩
  funext j
  exact congrArg x (BoxFin.crtSlotPerm_digitSlot hv j)

/-- The complete post-inverse-routing stack program includes a mask reconstructed
from the unary address width. Its bound is linear in the padded grid volume. -/
theorem decodePaddedGrid {I : Type} (k w n b p : I → ℕ) (D : ℕ)
    (hv : ∀ i, ValidDirectory (k i)) (v : (i : I) → Fin (2^(k i)) → Dusk.Grain (w i))
    (hk : ∀ i, 1 ≤ k i) (hb : ∀ i, b i ≤ 2*k i) (hn : ∀ i, n i ≤ 2^(k i)*k i)
    (hword : ∀ i, w i+p i ≤ D*k i) :
    Task (fun i => 2^(k i)*k i)
      (fun i => send (tally (k i), decodePacket (n i) (b i) (p i) (v i)))
      (fun i => send (finishCarry (carryPacket (n i) (b i)
        (coefficientWords (b i) (p i) (occupiedRecords (hv i) (v i)))))) := by
  have hN i : 1 ≤ 2^(k i) := Nat.one_le_pow _ _ (by decide)
  have comp := (recoverOccupiedStream k w n b p (BoxScale.width ∘ k)
    (CoprimeBox.box ∘ k) hv v (BoxMaskProgram.task k hv)).bound
    (b' := fun i => 2^(k i)*k i) (2*D+8) fun i =>
      decodeBudget le_rfl (hb i) (hn i) (hword i) (hN i) (hk i)
  have fin := decodeAndFinish (fun i => directoryVolume (k i)) w n b p
    (fun i => 2^(k i)) k D (fun i => occupiedRecords (hv i) (v i))
    (fun i => boxVolume_le (hv i)) hb hn hword hN hk
  exact (comp.compose fin).bound 2 (fun _ => by omega)

/-- A fixed physical machine from padded, inverse-routed records to plain output.
The numerical hypothesis concerns only the scaled residue positions corresponding
to the true coefficients. Errors in all padding cells are unrestricted. -/
theorem inverseGridToProduct {I : Type} (k w n b p h : I → ℕ) (D : ℕ)
    (hv : ∀ i, ValidDirectory (k i)) (a c : I → Word)
    (v : (i : I) → Fin (2^(k i)) → Dusk.Grain (w i))
    (hk : ∀ i, 1 ≤ k i) (hb : ∀ i, b i ≤ 2*k i) (hn : ∀ i, n i ≤ 2^(k i)*k i)
    (hword : ∀ i, w i+p i ≤ D*k i)
    (ha : ∀ i, (a i).length = n i) (hc : ∀ i, (c i).length = n i)
    (hcap : ∀ i, n i ≤ b i*h i) (hslots : ∀ i, 4*h i ≤ 2^(k i))
    (hh : ∀ i, 0 < h i) (hd : ∀ i, h i ≤ 2^(b i))
    (herr : ∀ i j, ‖Grid.meaning (p i) (w i) (atResidue (hv i) (v i) j) -
      (ordinaryCoefficient (unpackDigits (b i) (directoryVolume (k i)) (a i))
        (unpackDigits (b i) (directoryVolume (k i)) (c i)) j : ℂ)‖ < 1/2) :
    ∃ z : I → Word, (∀ i, (z i).length = 2*n i ∧ bitValue (z i) = bitValue (a i)*bitValue (c i)) ∧
      Task (fun i => 2^(k i)*k i)
        (fun i => send (tally (k i), decodePacket (n i) (b i) (p i) (afterInverseCRT (hv i) (v i))))
        (fun i => send (z i)) ∧
      TreeToPlainBits (fun i => send (tally (k i), decodePacket (n i) (b i) (p i)
        (afterInverseCRT (hv i) (v i)))) z (fun i => 2^(k i)*k i + 2*n i) := by
  let data i := afterInverseCRT (hv i) (v i)
  let out i := finishCarry (carryPacket (n i) (b i)
    (coefficientWords (b i) (p i) (occupiedRecords (hv i) (data i))))
  have ho i : (out i).length = 2*n i ∧ bitValue (out i) = bitValue (a i)*bitValue (c i) := by
    apply finishGrid_product (a i) (c i) _ (ha i) (hc i) (hcap i)
      (BoxFin.capacity (hv i) (hslots i)) (hh i) (hd i)
    simpa only [data, occupied_afterInverseCRT] using herr i
  have task := decodePaddedGrid k w n b p D hv data hk hb hn hword
  refine ⟨out, ho, task, ?_⟩
  have run := treeToPlainBits_of_task (reply := out) task
  simpa only [fun i => (ho i).1] using run

private theorem releaseBound {I : Type} {q : I → Tree} {z : I → Word} {B n : I → ℕ}
    (run : TreeToPlainBits q z B) (h : ∀ i, B i + 1 ≤ 50*(n i + 1)) :
    TreeToPlainBits q z n := by
  obtain ⟨A,Q,J,fa,fq,fj,sym,blank,inp,out,start,m,C,S,diff,inj,nonblank,r⟩ := run
  refine ⟨A,Q,J,fa,fq,fj,sym,blank,inp,out,start,m,C*50,S*50,diff,inj,nonblank,fun i => ?_⟩
  obtain ⟨tape,finish,t,load,spare,trace,halt,written,time,cells,card,membership⟩ := r i
  refine ⟨tape,finish,t,load,spare,trace,halt,written,?_,cells,?_,membership⟩
  · exact time.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left C (h i))
  · exact card.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left S (h i))

open DigitPacking

set_option maxHeartbeats 1200000 in
/-- With the logarithmic digit and precision parameters, the complete readout
uses linear time and visits linearly many physical cells in the original input
length. The accuracy assumption addresses only actual scaled-residue records. -/
theorem packedInverseGridToProduct {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hv : ∀ i, ValidDirectory (addressBits (n i))) (a c : I → Word)
    (v : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i)))
    (ha : ∀ i, (a i).length = n i) (hc : ∀ i, (c i).length = n i)
    (herr : ∀ i j, ‖FixedPoint.value (addressBits (n i)) (atResidue (hv i) (v i) j) -
      (ordinaryCoefficient (unpackDigits (width (n i)) (directoryVolume (addressBits (n i))) (a i))
        (unpackDigits (width (n i)) (directoryVolume (addressBits (n i))) (c i)) j : ℂ)‖ < 1/2) :
    ∃ z : I → Word, (∀ i, (z i).length = 2*n i ∧ bitValue (z i) = bitValue (a i)*bitValue (c i)) ∧
      Task n (fun i => send (tally (addressBits (n i)), decodePacket (n i) (width (n i))
        (fractionBits (addressBits (n i))) (afterInverseCRT (hv i) (v i)))) (fun i => send (z i)) ∧
      TreeToPlainBits (fun i => send (tally (addressBits (n i)), decodePacket (n i) (width (n i))
        (fractionBits (addressBits (n i))) (afterInverseCRT (hv i) (v i)))) z n := by
  let k i := addressBits (n i)
  have hk i : 1 ≤ k i := by
    have := width_le_twice_addressBits (hn i)
    have := width_pos (hn i)
    dsimp [k]; omega
  have hw i : componentBits (k i) + fractionBits (k i) ≤ 171 * k i := by
    have := hk i
    unfold componentBits fractionBits; omega
  obtain ⟨z,hz,task,run⟩ := inverseGridToProduct k (componentBits ∘ k) n (width ∘ n) (fractionBits ∘ k)
    (count ∘ n) 171 hv a c v hk (fun i => width_le_twice_addressBits (hn i))
    (fun i => (packed_volume (hn i)).1) hw ha hc (fun i => (count_mul_width (hn i)).1)
    (fun i => (capacity_bounds (hn i)).1) (fun i => count_pos (hn i))
    (fun i => count_le_radix (hn i)) herr
  refine ⟨z,hz,task.bound 50 (fun i => ?_),releaseBound run fun i => ?_⟩
  · change capacity (n i) * addressBits (n i) + 1 ≤ 50*(n i+1)
    have := (packed_volume (hn i)).2
    omega
  change capacity (n i) * addressBits (n i) + 2*n i + 1 ≤ 50*(n i+1)
  have := (packed_volume (hn i)).2
  omega

end
end FixedPoint

end NearSquareRoot
end Computability
end OAI
