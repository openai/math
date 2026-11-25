import OAI.Hierarchy.DescentPackedMinimumFrames
import OAI.Hierarchy.DescentPackedAffineContribution
import OAI.Hierarchy.DescentMultiplierMinimumRAM

namespace OAI
/-! # The two stable ordinary-stage choices on the packed native score ledger -/

namespace Hierarchy.DescentColonies.PackedChoices
open DescentGL DescentBinaryField DescentAffineColors DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM.PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {H G k b w M : ℕ}

def ticks {q : ℕ} (L : DescentPackedMinimum.Layout q) (H G M : ℕ) :=
  4+q*DescentPackedMinimum.cost L.work (H*chunks G M)+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q)

private theorem sorted_names (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

private theorem typed_minimum {q : ℕ} (n : 0<q) (f : Fin q→ℕ) :
    ∃i,(scanMinimum f (List.finRange q)).1=some (i,f i) := by
  have h := (scanMinimum_spec f (List.finRange q)).2
  cases found : (scanMinimum f (List.finRange q)).1 with
  | none=>
    rw [found] at h
    have len := congrArg List.length h
    simp at len
    omega
  | some p=>
    rw [found] at h
    exact ⟨p.1,by rw [←h.1]⟩

/-- The native zero-based selected row is the same ordinal used by seedAt.
Its coefficient word is the successor of that row in the enumeration. -/
theorem seed (inc : Fin H→List (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (hk : 0<k)
    (L : DescentPackedMinimum.Layout (2^k-1))
    (fits : DescentPackedMinimum.Fits L w (1+k*2^k) M H G) (positive : 0<M)
    (room : G*H*2^k<2^w) (m : Memory w)
    (input : ∀i,DescentPackedScore.Input (M:=M) (L.source i) (L.dictionary i) PackedSplit.value
      (PackedSplit.state inc W D cap (modulus hk) (seedAt k i)) m) :
    let Q := uniformColonyScore inc W D cap (modulus hk)
    ∃out : Memory w,∃ i : Fin (2^k-1),
      (DescentPackedMinimum.search L w H G M).Exec m out (ticks L H G M) ∧
      out (L.result+(2^k-1-1))=(i.val:Word w) ∧
      (scanMinimum Q (nonzeroWords k)).1=some (seedAt k i,Q (seedAt k i)) ∧
      MultiplierMinimumRAM.key (seedAt k i)=i.val+1 ∧
      (∀z<L.work,out z=m z) ∧ ∀z,L.result+(2^k-1)≤z→ out z=m z := by
  let score := uniformColonyScore inc W D cap (modulus hk)
  let f := fun _ : Fin (2^k-1)=>@PackedSplit.value k
  let x := fun i : Fin (2^k-1)=>PackedSplit.state inc W D cap (modulus hk) (seedAt k i)
  have real (i) : DescentPackedMinimum.scores f x i=score (seedAt k i) :=
    PackedSplit.score_total inc W D cap (modulus hk) (seedAt k i)
  have pos : 0<2^k-1 := by have := Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide : 1<2);omega
  obtain ⟨i,hit⟩:=typed_minimum pos (fun i=>score (seedAt k i))
  let raw := DescentPackedMinimum.scoreAt f x
  have corresponding : (fun i : Fin (2^k-1)=>raw i.val)=(fun i=>score (seedAt k i)) := by
    funext i
    simp only [raw,DescentPackedMinimum.scoreAt,dite_eq_left i.isLt,real]
  have ledger := MultiplierMinimumRAM.mapWinner (@Fin.val (2^k-1)) raw (List.finRange _)
  rw [sorted_names,corresponding,hit] at ledger
  have official := MultiplierMinimumRAM.mapWinner (seedAt k) score (List.finRange _)
  rw [←List.ofFn_eq_map,hit] at official
  obtain ⟨out,run,found,low,high⟩:=DescentPackedMinimum.minimum_frames L fits f x m (fun _=>PackedSplit.value_zero _) positive
    (fun i=>by rw [real];exact (PackedSplit.score_cap inc W D cap (modulus hk) _).trans_lt room) input ledger
  exact ⟨out,i,run,found,official,seedAt_code i,low,high⟩

/-- Each candidate reads the same retained winning-slab bank. Its dictionary
interprets those occurrence fields with the candidate's actual affine row. -/
theorem affine (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (hk : 0<k) (μ : Nonzero k) (L : DescentPackedMinimum.Layout (2^(k+1)))
    (fits : DescentPackedMinimum.Fits L w (PackedContribution.width k b) M H G) (positive : 0<M)
    (mass : (∑g,∑v,∑x,amt g v x)<2^w) (width : ∀g v x,amt g v x<2^b) (m : Memory w)
    (input : ∀j,DescentPackedScore.Input (M:=M) (L.source j) (L.dictionary j) (PackedContribution.value j)
      (fun v g=>PackedContribution.actual b inc W amt D cap (modulus hk) μ g v) m) :
    let S := GroupedScan.groupedSlabs inc W amt D cap (modulus hk) μ
    ∃out : Memory w,∃ j : Candidate k,
      (DescentPackedMinimum.search L w H G M).Exec m out (ticks L H G M) ∧
      out (L.result+(2^(k+1)-1))=(j.val:Word w) ∧
      (scanMinimum (scoreAt S) (List.range (2^(k+1)))).1=some (j.val,score S j) ∧
      (∀z<L.work,out z=m z) ∧ ∀z,L.result+2^(k+1)≤z→ out z=m z := by
  let S := GroupedScan.groupedSlabs inc W amt D cap (modulus hk) μ
  let f := fun j : Candidate k=>PackedContribution.value (b:=b) j
  let x := fun (_ : Candidate k) v g=>PackedContribution.actual b inc W amt D cap (modulus hk) μ g v
  have real (j) : DescentPackedMinimum.scores f x j=score S j :=
    PackedContribution.sum_value b inc W amt D cap (modulus hk) μ j width
  have equal : DescentPackedMinimum.scoreAt f x=scoreAt S := by
    funext i
    unfold DescentPackedMinimum.scoreAt scoreAt
    split <;> first | apply real | rfl
  obtain ⟨j,best,_⟩:=first S
  have stable : (scanMinimum (DescentPackedMinimum.scoreAt f x) (List.range (2^(k+1)))).1=some (j.val,score S j) := by rw [equal];exact best
  obtain ⟨out,run,found,low,high⟩:=DescentPackedMinimum.minimum_frames L fits f x m (fun j=>PackedContribution.value_zero j)
    positive (fun j=>by rw [real];exact (PackedContribution.score_le_mass inc W amt D cap hk μ j).trans_lt mass) input stable
  exact ⟨out,j,run,found,best,low,high⟩

/-- The two true search clocks price the shared names once per position and
the group-dependent data in short fields. The common candidate and field
widths depend only on the subround. -/
theorem bit_price (L₁ : DescentPackedMinimum.Layout (2^k-1)) (L₂ : DescentPackedMinimum.Layout (2^(k+1)))
    (w H G b : ℕ) (wide : 2*PackedContribution.width k b≤w) :
    let a := PackedContribution.width k b
    let s := 1+k*2^k
    (ticks L₁ H G (lanes w s)+ticks L₂ H G (lanes w a))*w ≤
      400*(2^(k+1)+1)*(w+H*w+4*H*G*a) := by
  let a := PackedContribution.width k b
  let s := 1+k*2^k
  have transfer : s≤a := by dsimp [s,a,PackedContribution.width];omega
  have live : 0<a := by dsimp [a,PackedContribution.width];omega
  have count : 2^k-1+1≤2^(k+1)+1 := by rw [pow_succ];omega
  have raw := DescentPackedMinimum.bit_price L₁ w s H G (by dsimp [s];omega)
    ((Nat.mul_le_mul_left 2 transfer).trans wide)
  have paint := DescentPackedMinimum.bit_price L₂ w a H G live wide
  have firstCost : ticks L₁ H G (lanes w s)*w≤200*(2^(k+1)+1)*(w+H*w+4*H*G*a) :=
    raw.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ count)
      (Nat.add_le_add_left (Nat.mul_le_mul_left (4*H*G) transfer) (w+H*w)))
  change (ticks L₁ H G (lanes w s)+ticks L₂ H G (lanes w a))*w≤_
  rw [Nat.add_mul]
  apply (Nat.add_le_add firstCost paint).trans_eq
  dsimp only [a]
  ring

end
end Hierarchy.DescentColonies.PackedChoices

end OAI
