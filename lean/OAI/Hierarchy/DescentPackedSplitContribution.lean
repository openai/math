import OAI.Hierarchy.DescentPackedScore
import OAI.Hierarchy.DescentColonyScoreCore
import OAI.Hierarchy.DescentColonyScanLeaves

namespace OAI
/-! # Short occurrence records for the common multiplier score -/

namespace Hierarchy.DescentColonies.PackedSplit
open DescentSIMDLookup DescentGL
open scoped Classical BigOperators
noncomputable section
variable {k H G s : ℕ}

/-- The extra code distinguishes an unfilled final lane from a genuine row
with no split flags, whose one root colony contributes to the multiplier score. -/
def present (c : Cell s) : Cell (1+s) :=
  ⟨c.val+1,by rw [pow_add,pow_one]; have := c.isLt;have := Nat.two_pow_pos s;omega⟩

def strip (c : Cell (1+s)) : Cell s :=
  ⟨(c.val-1)%2^s,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

@[simp] theorem present_ne_zero (c : Cell s) : present c≠0 := by
  intro eqn
  have h:=congrArg Fin.val eqn
  change c.val+1=0 at h
  omega

@[simp] theorem strip_present (c : Cell s) : strip (present c)=c := by
  apply Fin.ext
  change (c.val+1-1)%2^s=c.val
  simp only [Nat.add_sub_cancel,Nat.mod_eq_of_lt c.isLt]

abbrev Flags (k : ℕ) := Fin k→Block k→Bool

def encodeFlags (t : Flags k) : Cell (k*2^k) :=
  finFunctionFinEquiv (fun i : Fin (k*2^k)=>let p : Fin k×Block k:=finProdFinEquiv.symm i
    finTwoEquiv.symm (t p.1 p.2))

def decodeFlags (c : Cell (k*2^k)) : Flags k := fun d x=>
  finTwoEquiv (finFunctionFinEquiv.symm c (finProdFinEquiv (d,x)))

@[simp] theorem decode_encodeFlags (t : Flags k) : decodeFlags (encodeFlags t)=t := by
  funext d x
  simp only [decodeFlags,encodeFlags,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

def actualFlags (rows : Scan.Buffer (Fin H) k) (v : Fin H) : Flags k :=
  fun d x=>Scan.lookup rows d.val v x

def depth (t : Flags k) (x : Block k) :=
  (Scan.seek (fun d=>if h:d<k then t ⟨d,h⟩ x else false) k 0).1

private theorem seek_congr (a b : ℕ→Bool) (n z : ℕ) (same : ∀d,z≤d→d<z+n→a d=b d) :
    Scan.seek a n z=Scan.seek b n z := by
  induction n generalizing z with
  | zero=>rfl
  | succ n ih=>
    simp only [Scan.seek,same z le_rfl (by omega)]
    split
    · rw [ih (z+1) (fun d lo hi=>same d (by omega) (by omega))]
    · rfl

theorem depth_actualFlags (rows : Scan.Buffer (Fin H) k) (v : Fin H) (x : Block k) :
    depth (actualFlags rows v) x=Scan.leafDepth rows v x := by
  apply congrArg Prod.fst
  apply seek_congr
  intro d _ lo
  simp [actualFlags,show d<k by omega]

def localKeys (t : Flags k) : Finset (ℕ×ℕ) :=
  Finset.univ.image (fun x:Block k=>let d:=depth t x; (d,group d x))

theorem keys_read (rows : Scan.Buffer (Fin H) k) (v : Fin H) :
    localKeys (actualFlags rows v)=Scan.siteKeys rows v := by
  simp only [localKeys,Scan.siteKeys,depth_actualFlags]

def value (key : Cell (1+k*2^k)) : ℕ :=
  if key=0 then 0 else (localKeys (decodeFlags (strip key))).card

@[simp] theorem value_zero (k : ℕ) : value (k:=k) 0=0 := ite_eq_left rfl

def state (inc : Fin H→List (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (v : Fin H) (g : Fin G) : Cell (1+k*2^k) :=
  present (encodeFlags (actualFlags (Scan.build inc (multiplierLoad (W g) a μ.val) D cap k) v))

theorem local_value (inc : Fin H→List (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (v : Fin H) (g : Fin G) :
    value (state inc W D cap a μ v g)=
      (Scan.siteKeys (Scan.build inc (multiplierLoad (W g) a μ.val) D cap k) v).card := by
  simp [state,value,keys_read]

theorem score_total (inc : Fin H→List (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :
    (∑v,∑g,value (state inc W D cap a μ v g))=uniformColonyScore inc W D cap a μ := by
  rw [Finset.sum_comm]
  simp only [local_value,uniformColonyScore,Scan.leafScore_siteKeys]

theorem score_cap (inc : Fin H→List (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) : uniformColonyScore inc W D cap a μ≤G*H*2^k := by
  simp only [uniformColonyScore,Scan.leafScore_siteKeys]
  calc
    _ ≤ ∑_g : Fin G,∑_v : Fin H,2^k := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro v _
      exact (Finset.card_image_le).trans_eq (by simp)
    _ = _ := by simp [Nat.mul_assoc]

end
end Hierarchy.DescentColonies.PackedSplit

end OAI
