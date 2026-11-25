import OAI.Hierarchy.FactorBucketProcedure
import OAI.Hierarchy.FactorKeyPass
import OAI.Hierarchy.FactorBankFrame

namespace OAI
/-! # Correctness of the native factor assignment from its original resource table -/

namespace Hierarchy.FactorBucketRAM
open FactorAllocation Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

structure BankBounds (b : Banks) (w width N d : ℕ) : Prop where
  resourcesBefore : b.resources+N*d≤b.digits
  thresholdsBefore : b.thresholds+(20*(w+1)+1)≤b.digits
  digitsBefore : b.digits+N*d≤b.keys
  keysBefore : b.keys+N≤b.counts
  countsBefore : b.counts+(20*(w+1)+2)^d≤b.output
  fits : b.output+N≤2^width

/-- The four mutable segments are allowed to have gaps between them. -/
def untouched (b : Banks) (w N d a : ℕ) : Prop :=
  Outside a b.digits (N*d) ∧ Outside a b.keys N ∧
    Outside a b.counts ((20*(w+1)+2)^d) ∧ Outside a b.output N

/-- After the four native passes, both words required by the pin publisher are
present for every original factor, including factors of zero resource cost. -/
theorem compiled_state {w width N d T : ℕ} (ht : 0<T) (hd : 0<d)
    (b : Banks) (bounds : BankBounds b w width N d) (m : Memory width)
    (cost : Fin N → Fin d → ℕ)
    (smallS : 20*(w+1)+1<2^width) (smallD : d<2^width) (smallT : T<2^width)
    (smallScan : N*d*(20*(w+1)+1)<2^width) (smallRows : N*d<2^width)
    (resources : ∀ (i : Fin N) (j : Fin d), (m (b.resources+(i.val*d+j.val))).val=cost i j)
    (thresholds : ∀ j≤20*(w+1), (m (b.thresholds+j)).val=FactorBucket.threshold j) :
    (∀ a, untouched b w N d a → compiledMemory width w N d T b m a = m a) ∧
    (∀ i : Fin N, compiledMemory width w N d T b m (b.keys+i.val) = (classIndex (key w cost i):Word width) ∧
      compiledMemory width w N d T b m (b.output+i.val) = ((owner ht w cost i).val:Word width)) := by
  let s := 20*(w+1)+1
  let v n := passWords width n s d (s+1) T b
  let digits := iterRows digitStep (v (N*d*s)) m (N*d*s)
  let keys := iterRows keyStep (v (N*d)) digits (N*d)
  let clear := iterRows clearStep (v ((s+1)^d)) keys ((s+1)^d)
  have bd := bounds.digitsBefore
  have bk := bounds.keysBefore
  have bc := bounds.countsBefore
  have bf := bounds.fits
  have typed (j : Fin N) (l : Fin d) :
      digits (b.digits+(j.val*d+l.val)) = ((FactorBucket.label w (cost j l)).val:Word width) := by
    have rb := Nat.mul_le_mul_right d (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at rb
    have limit : j.val*d+l.val<N*d := by have := l.isLt; omega
    have run := digit_table w (N*d) b.resources b.thresholds b.digits (v (N*d*s)) m
      (fun a=>(m (b.resources+a)).val) rfl rfl rfl rfl bounds.resourcesBefore
      bounds.thresholdsBefore (by omega) smallScan smallS (fun _ _=>rfl) thresholds _ limit
    simpa [digits,resources] using run
  have keyAt (j : Fin N) : keys (b.keys+j.val)=(classIndex (key w cost j):Word width) :=
    bucket_key_table (v (N*d)) digits cost rfl rfl rfl rfl hd smallD smallRows bd (by omega) typed j
  have radixEq : (s+1)^d=(20*(w+1)+2)^d := rfl
  have clearAt (a : ℕ) : clear a =
      if b.counts≤a ∧ a<b.counts+(s+1)^d then 0 else keys a :=
    clear_bank _ keys _ _ rfl (by rw [radixEq]; omega) a
  let layout : OwnerLayout N ((20*(w+1)+2)^d) := ⟨b.keys,b.counts,b.output,bk,bc⟩
  have keyRead (j : Fin N) : clear (layout.keys+j.val)=(classIndex (key w cost j):Word width) := by
    have jj := j.isLt
    simpa [layout,clearAt, show ¬(b.counts≤b.keys+j.val ∧ b.keys+j.val<b.counts+(s+1)^d) by omega]
      using keyAt j
  have empty (g : Key w d) : clear (layout.counts+classIndex g)=0 := by
    have gi : classIndex g<(s+1)^d := (finFunctionFinEquiv g).isLt
    simp [layout,clearAt,show b.counts≤b.counts+classIndex g ∧
      b.counts+classIndex g<b.counts+(s+1)^d by omega]
  have endState := owner_state ht cost (v N) layout clear rfl rfl rfl rfl smallT bf keyRead empty
  constructor
  · rintro a ⟨hdigit,hkey,hcount,howner⟩
    change iterRows ownerStep (v N) clear N a=m a
    rw [owner_untouched (v N) layout clear (key w cost) rfl rfl rfl rfl smallT bf keyRead
      N le_rfl a hcount howner,clearAt,ite_eq_right (by rw [radixEq]; rcases hcount with h|h <;> omega)]
    have pullKey := key_frame (N:=N) (d:=d) (keyBase:=b.keys) (v (N*d)) digits rfl rfl hd
      smallD smallRows (by omega) (N*d) le_rfl a hkey
    exact pullKey.trans (digit_untouched _ m (N*d) s b.digits (Nat.succ_pos _)
      smallS smallScan (by omega) rfl rfl _ le_rfl a hdigit)
  · intro i
    exact ⟨(endState.1 _ (by dsimp [layout]; have := i.isLt; omega)).trans (keyRead i),
      endState.2 i⟩

end Hierarchy.FactorBucketRAM

end OAI
