import OAI.Hierarchy.DescentPackedMatchingRAM
import OAI.Hierarchy.DescentPackedProfileWindow

namespace OAI
/-! # The actual profile count of each packed source chunk -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w H G M : ℕ}

def laneCounts (s : Shape) (M : ℕ) (z : Cell (s.outputBits*M)) (i : Fin M) : Fin (s.pairs+1) :=
  ⟨min s.pairs (decodeOutput s ((encode s.outputBits M).symm z i)).count.val,Nat.lt_succ_of_le (min_le_left ..)⟩

def chunkCount (s : Shape) (M : ℕ) (z : Cell (s.outputBits*M)) := ∑i,(laneCounts s M z i).val

theorem chunkCount_bound (s : Shape) (M : ℕ) (z : Cell (s.outputBits*M)) : chunkCount s M z≤M*s.pairs := by
  simpa only [chunkCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
    Finset.sum_le_sum (s:=Finset.univ) (fun i _=>Nat.le_of_lt_succ (laneCounts s M z i).isLt)

private theorem natural_lane {b M : ℕ} (x : Cell (b*M)) (i : Fin M) :
    ((encode b M).symm x i).val=digit b i.val x.val := by
  simpa only [Equiv.apply_symm_apply] using (digit_encode ((encode b M).symm x) i).symm

theorem count_decoded (s : Shape) (x : Cell s.outputBits) :
    (decodeOutput s x).count.val=digit s.digit 0 x.val := by
  let z:=Fin.castAdd (s.pairs*12) (0:Fin 1)
  exact natural_lane (b:=s.digit) (M:=s.outFields) x z

theorem lane_actual (s : Shape) (x : Inputs s) (bound : Bounded x) (z : Cell (s.outputBits*M))
    (i : Fin M) (read : digit s.outputBits i.val z.val=(encodeOutput (transform x)).val) :
    (laneCounts s M z i).val=amount x := by
  have same := Fin.ext ((natural_lane z i).trans read)
  have n := count_read x bound
  change min s.pairs (decodeOutput s ((encode s.outputBits M).symm z i)).count.val=_
  rw [same,output_inverse]
  simp only [lookupCell,decode_encode,output_inverse] at n
  have within : amount x ≤ s.pairs :=
    PackedLocalMatch.count_le_window (need x) (cap x) bound.item
  change (transform x).count.val = amount x at n
  rw [n,min_eq_right within]

theorem lane_unused (s : Shape) (z : Cell (s.outputBits*M)) (i : Fin M)
    (dead : digit s.outputBits i.val z.val=0) : (laneCounts s M z i).val=0 := by
  change min s.pairs _=0
  rw [count_decoded,natural_lane,dead]
  simp [digit]

def sumLookup (counts output : Bank) : Expr := .lookup counts (.lookup output .row)

/-- One dictionary read sums every live lane of a previous topology output word.
The word itself may already contain the full set of selected incidence handles. -/
theorem sum_scan (s : Shape) (counts output : Bank) (base : ℕ) {n : ℕ} (keys : Fin n→Cell (s.outputBits*M))
    (m : Memory w) (lowCounts : counts.Fits w base) (lowInput : output.Fits w base)
    (capacity : n≤output.size) (size : counts.bits=s.outputBits*M) (space : base+n<2^w)
    (fixed : ∀k : Cell (s.outputBits*M),m (counts.base+k.val)=(chunkCount s M k:Word w))
    (data : ∀i,m (output.base+i.val)=((keys i).val:Word w)) :
    (scan w base n (sumLookup counts output)).Exec m (image base n (sumLookup counts output) m) (4+28*n) ∧
    (∀i,image base n (sumLookup counts output) m (base+i.val)=(chunkCount s M (keys i):Word w)) ∧
      ∀a<base,image base n (sumLookup counts output) m a=m a := by
  have OK : (sumLookup counts output).Fits w base := ⟨lowCounts,lowInput,trivial⟩
  refine ⟨?_,?_,fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha)⟩
  · intro pcCount regCount publicCount machine pc reg pub exit installed params cfg mem entry initial
    simpa only [sumLookup,Expr.work,Nat.mul_comm 28] using
      scan_exec base n (sumLookup counts output) m OK space machine pc reg pub exit installed params cfg mem entry initial
  intro i
  have h := ProtocolRAMGeneratedWrite.read_image base n (sumLookup counts output) m i
  have live := i.isLt.trans_le capacity
  have bound : (keys i).val<counts.size := by simpa only [Bank.size,size] using (keys i).isLt
  simp only [sumLookup,Expr.eval,Bank.read,Fin.val_cast_of_lt (live.trans lowInput.2.1),Nat.mod_eq_of_lt live,
    data i,Fin.val_cast_of_lt (bound.trans lowCounts.2.1),Nat.mod_eq_of_lt bound,fixed] at h
  exact h

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
