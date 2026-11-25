import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Packed local profiles from a chronological two-word window -/
namespace Hierarchy.DescentPackedProfileWindow
open DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section

def localPrefix {M U : ℕ} (cnt : Fin M→Fin (U+1)) (i : Fin M) : ℕ :=
  ProtocolRAMPortRanks.«prefix» (fun j=>(cnt j).val) Fin.val i

theorem local_end {M U : ℕ} (cnt : Fin M→Fin (U+1)) (i : Fin M) :
    localPrefix cnt i+(cnt i).val ≤ M*U := by
  calc
    _ ≤ ∑j,(cnt j).val := ProtocolRAMPortRanks.prefix_end (fun j=>(cnt j).val) Fin.val i
    _ ≤ ∑_ : Fin M,U := Finset.sum_le_sum fun j _=>Nat.le_of_lt_succ (cnt j).isLt
    _ = M*U := by simp

def word (d R : ℕ) (stream : ℕ→Cell d) (r : ℕ) : Cell (d*R) :=
  encode d R fun i=>stream (r*R+i.val)

def two (d R : ℕ) (lo hi : Cell (d*R)) (j : ℕ) : Cell d :=
  if first : j < R then (encode d R).symm lo ⟨j,first⟩
  else if next : j-R < R then (encode d R).symm hi ⟨j-R,next⟩ else 0

theorem two_word (d R : ℕ) (stream : ℕ→Cell d) (r j : ℕ) (fit : j < 2*R) :
    two d R (word d R stream r) (word d R stream (r+1)) j=stream (r*R+j) := by
  by_cases first : j < R
  · simp [two,word,first]
  · have next : j-R < R := by omega
    simp only [two,dite_eq_right first,dite_eq_left next,word,Equiv.symm_apply_apply,Nat.add_mul,Nat.one_mul]
    congr 1
    omega

/-- Each lane has U physical output cells. The inactive suffix is forced to
zero, independently of the following occupied source's actual profiles. -/
def localProfile (d U M R : ℕ) (cnt : Fin M→Fin (U+1)) (off : Fin R)
    (lo hi : Cell (d*R)) : Cell (d*(M*U)) :=
  encode d (M*U) fun z=>
    let ij:=finProdFinEquiv.symm z
    if ij.2.val < (cnt ij.1).val then two d R lo hi (off.val+localPrefix cnt ij.1+ij.2.val) else 0

theorem local_digit (d U M R : ℕ) (cnt : Fin M→Fin (U+1)) (off : Fin R)
    (lo hi : Cell (d*R)) (i : Fin M) (j : Fin U) :
    digit d (finProdFinEquiv (i,j)).val (localProfile d U M R cnt off lo hi).val =
      if j.val < (cnt i).val then (two d R lo hi (off.val+localPrefix cnt i+j.val)).val else 0 := by
  rw [localProfile,digit_encode]
  simp only [Equiv.symm_apply_apply]
  split <;> rfl

theorem window (d U M R : ℕ) (cnt : Fin M→Fin (U+1)) (stream : ℕ→Cell d) (start : ℕ)
    (grain : 0 < R) (fits : M*U ≤ R) (i : Fin M) (j : Fin U) :
    let r:=start/R
    let off : Fin R:=⟨start%R,Nat.mod_lt _ grain⟩
    digit d (finProdFinEquiv (i,j)).val
      (localProfile d U M R cnt off (word d R stream r) (word d R stream (r+1))).val =
      if j.val < (cnt i).val then (stream (start+localPrefix cnt i+j.val)).val else 0 := by
  dsimp only
  rw [local_digit]
  by_cases active : j.val < (cnt i).val
  · rw [ite_eq_left active,ite_eq_left active,two_word]
    · have same : start/R*R+start%R=start := Nat.div_add_mod' ..
      rw [show start/R*R+(start%R+localPrefix cnt i+j.val)=start+localPrefix cnt i+j.val by omega]
    · have small:=local_end cnt i
      have rem:=Nat.mod_lt start grain
      omega
  · simp only [ite_eq_right active]

end
end Hierarchy.DescentPackedProfileWindow

end OAI
