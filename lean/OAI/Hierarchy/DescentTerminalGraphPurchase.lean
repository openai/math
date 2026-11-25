import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic
import OAI.Hierarchy.DescentTerminalNeighborCount
import OAI.Hierarchy.DescentTerminalGraphVolume
import OAI.Hierarchy.DescentTerminalBinPack

namespace OAI
/-! # A single physical row capacity funded by actual total terminal cable width -/

namespace Hierarchy.DescentTerminalGraphVolume
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalRecipeRows DescentTerminalBinPack
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

theorem exact_pieces (p n : ℕ) (positive : 0<p) (fit : p∣n) : poolBatchCount n p*p=n := by
  obtain ⟨k,rfl⟩:=fit
  have index : p*k+p-1=p*k+(p-1) := by omega
  rw [poolBatchCount,index,Nat.mul_add_div positive,Nat.div_eq_of_lt (by omega : p-1<p)]
  simp [Nat.mul_comm]

variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} {N : Network D P bits}

theorem exact_width (N : Network D P bits) (hp : 0<p) (edges : ∀e,p∣N.width e)
    (ports : ∀z,p∣bits z) : bundleBudget (p:=p) N*p=2*(∑e,N.width e)+∑z,bits z := by
  unfold bundleBudget
  rw [Nat.add_mul,Nat.mul_assoc,Finset.sum_mul,Finset.sum_mul]
  have a e:=exact_pieces p (N.width e) hp (edges e)
  have b v:=exact_pieces p (bits v) hp (ports v)
  simp only [a,b]

theorem purchase (L : Order N S p) (q W degree total exterior : ℕ) (hp : 0<p) (hq : 0<q)
    (edges : ∀e,p∣N.width e) (ports : ∀z,p∣bits z)
    (live : (∑e,N.width e)≤total) (outside : (∑z,bits z)≤exterior)
    (groups : (∑i,(L.site i).groups)≤S*(degree+1)) :
    purchased W (fun i=>(L.site i).rows q)≤rowBudget p q W total exterior S degree := by
  let rows:=∑i,(L.site i).rows q
  have one:=Nat.mul_le_mul_right p (paid_rows L hq)
  have mass:=exact_width N hp edges ports
  have realWidth : bundleBudget (p:=p) N*p≤2*total+exterior := by omega
  have nameCount : (∑i,(L.site i).groups)+2*S≤S*(degree+3) := by
    rw [show degree+3=degree+1+2 by omega,Nat.mul_add];omega
  have rest:=Nat.mul_le_mul_right (q*p) nameCount
  have balance : rows*(q*p)≤3*(2*total+exterior)+(S*(degree+3))*(q*p) := by
    change rows*q*p≤_ at one
    rw [Nat.add_mul] at one
    simp only [Nat.mul_assoc] at one
    exact one.trans (Nat.add_le_add (Nat.mul_le_mul_left 3 realWidth) rest)
  have pos:=Nat.mul_pos hq hp
  have invoice : rows ≤ 3*(2*total+exterior)/(q*p)+S*(degree+3) := by
    have cut:=(Nat.le_div_iff_mul_le pos).2 balance
    simpa [Nat.add_mul_div_right _ _ pos] using cut
  exact paid_of_le (fun i=>(L.site i).rows q) invoice

/-- The paid maximum is integral and is rounded down to whole physical bins.
This still covers every selected graph because its real purchase is a multiple of W. -/
theorem fixed_bins (L : Order N S p) (q W degree total exterior : ℕ) (hp : 0<p) (hq : 0<q) (hw : 0<W)
    (edges : ∀e,p∣N.width e) (ports : ∀z,p∣bits z)
    (live : (∑e,N.width e)≤total) (outside : (∑z,bits z)≤exterior)
    (groups : (∑i,(L.site i).groups)≤S*(degree+1)) :
    bins W (fun i=>(L.site i).rows q)≤rowBudget p q W total exterior S degree/W :=
  (Nat.le_div_iff_mul_le hw).2 (purchase L q W degree total exterior hp hq edges ports live outside groups)

end
end Hierarchy.DescentTerminalGraphVolume

end OAI
