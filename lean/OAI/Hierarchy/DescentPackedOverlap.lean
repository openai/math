import OAI.Hierarchy.DescentSIMDLookup
import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Repartition a padded packed row at arbitrary old and new lane widths -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ThreeFlat.Routing ThreeFlat.Routing.CallPool
open scoped BigOperators Fin.CommRing
noncomputable section
variable {a H G A B : ℕ}

/-- Beyond this many old words every remaining contribution is zero. At a nearly
empty last host the minimum also bounds the number of unused input reads. -/
def pieces (G A B : ℕ) := min (chunks G A) (chunks B A+1)

def first (slot B A : ℕ) := slot*B/A
def phase (slot B A : ℕ) := slot*B%A

def source (p : Row H G B) (j : ℕ) : Option (Row H G A) :=
  if h : first p.2.val B A+j<chunks G A then some (p.1,⟨_,h⟩) else none

/-- The table contributes precisely the destination digits contained in the
specified original word. All other positions have value zero. -/
def portion (a A B shift j : ℕ) (z : Cell (a*A)) : Cell (a*B) :=
  encode a B (fun i=>
    if h : (shift+i.val)/A=j ∧ (shift+i.val)%A<A then
      (encode a A).symm z ⟨_,h.2⟩ else 0)

def contribution (X : Fin H→Fin G→Cell a) (p : Row H G B) (j : ℕ) : ℕ :=
  match source (A:=A) p j with
  | none=>0
  | some q=>(portion a A B (phase p.2.val B A) j (data X q)).val

private theorem decomposition (s b a t : ℕ) :
    (first s b a+(phase s b a+t)/a)*a+(phase s b a+t)%a=s*b+t := by
  have front:=Nat.div_add_mod (s*b) a
  have rest:=Nat.div_add_mod (phase s b a+t) a
  unfold first phase at *
  rw [Nat.mul_comm a _] at front rest
  rw [Nat.add_mul]
  omega

private theorem block_lt {j A G : ℕ} (pos : 0<A) (live : j<G) : j/A<chunks G A :=
  (Nat.div_lt_iff_lt_mul pos).mpr (live.trans_le (by
    simpa [chunks,Nat.mul_comm] using count_le_batches_mul G A pos))

private theorem index_lt (p : Row H G B) (t : Fin B) (pos : 0<A)
    (live : p.2.val*B+t.val<G) :
    (phase p.2.val B A+t.val)/A<pieces G A B := by
  let u:=phase p.2.val B A+t.val
  have eqn : (first p.2.val B A+u/A)*A+u%A=p.2.val*B+t.val := decomposition p.2.val B A t.val
  have src : first p.2.val B A+u/A=(p.2.val*B+t.val)/A := by
    have eq' : p.2.val*B+t.val=u%A+(first p.2.val B A+u/A)*A := by omega
    rw [eq',Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt (Nat.mod_lt _ pos),Nat.zero_add]
  apply lt_min
  · have h:=block_lt pos live
    change u/A<chunks G A
    omega
  · apply (Nat.div_lt_iff_lt_mul pos).mpr
    have hp : phase p.2.val B A<A:=Nat.mod_lt _ pos
    have cover : B≤chunks B A*A:=by simpa [chunks,Nat.mul_comm] using count_le_batches_mul B A pos
    rw [Nat.succ_mul]
    omega

def lane (X : Fin H→Fin G→Cell a) (p : Row H G B) (t : Fin B) : Cell a :=
  if h : p.2.val*B+t.val<G then X p.1 ⟨_,h⟩ else 0

theorem contribution_digits (pos : 0<A) (X : Fin H→Fin G→Cell a) (p : Row H G B) (j : ℕ) :
    contribution (A:=A) X p j =
      ∑t : Fin B, (if (phase p.2.val B A+t.val)/A=j then (lane X p t).val else 0)*(2^a)^t.val := by
  classical
  by_cases h : first p.2.val B A+j<chunks G A
  · simp only [contribution,source,dite_eq_left h]
    change (finFunctionFinEquiv _).val=_
    rw [finFunctionFinEquiv_apply]
    apply Finset.sum_congr rfl
    intro t ht
    apply congrArg (·*(2^a)^t.val)
    by_cases same : (phase p.2.val B A+t.val)/A=j
    · subst j
      have eqn:=decomposition p.2.val B A t.val
      simp [Nat.mod_lt _ pos,data,lane,eqn]
    · simp [same]
  · simp only [contribution,source,dite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    by_cases same : (phase p.2.val B A+t.val)/A=j
    · have dead : ¬p.2.val*B+t.val<G:=by
        intro live
        have eqn:=decomposition p.2.val B A t.val
        rw [same] at eqn
        have cover : G≤chunks G A*A:=by simpa [chunks,Nat.mul_comm] using count_le_batches_mul G A pos
        have beyond:=Nat.mul_le_mul_right A (Nat.le_of_not_gt h)
        omega
      simp [same,lane,dead]
    · simp [same]

/-- Adding the overlapping fragments produces the very same live digits and
the canonical all-zero tail, even when neither word width divides the other. -/
theorem reconstruct (pos : 0<A) (X : Fin H→Fin G→Cell a) (p : Row H G B) :
    ∑j : Fin (pieces G A B),contribution (A:=A) X p j.val=(data X p).val := by
  classical
  simp_rw [contribution_digits pos]
  rw [Finset.sum_comm]
  change _=(finFunctionFinEquiv (lane X p)).val
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases live : p.2.val*B+t.val<G
  · let selected : Fin (pieces G A B):=⟨_,index_lt p t pos live⟩
    rw [Finset.sum_eq_single selected]
    · simp [selected]
    · intro other mem ne
      have diff : (phase p.2.val B A+t.val)/A≠other.val := by
        intro eqn
        exact ne (Fin.ext eqn.symm)
      simp [diff]
    · simp
  · simp [lane,live]

end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
