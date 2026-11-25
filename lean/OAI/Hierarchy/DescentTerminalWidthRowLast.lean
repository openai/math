import OAI.Hierarchy.DescentTerminalGrainProfiles
import OAI.Hierarchy.DescentTerminalFixedHeaders

namespace OAI
/-! # Only the last row of a nonempty grain group needs a patched width profile -/
namespace Hierarchy.DescentTerminalWidthRowsRAM
open DescentTerminalDenseHeader DescentTerminalGrainProfiles DescentTerminalHeaderGroups
open ThreeFlat.Routing
noncomputable section

variable {groups : ℕ} (q p : ℕ) (c : Fin groups → ℕ)
def tape := (List.ofFn c).flatMap (rows q p)
def passed (k : ℕ) := ((List.ofFn c).take k).flatMap (rows q p)
def tailCode (q p n : ℕ) := (encode q p
  (mask q p (min q (n-(poolBatchCount n q-1)*q)))).val
def full (q p : ℕ) := (encode q p (mask q p q)).val
def blank (q p : ℕ) := (encode q p (fun _ => 0)).val

theorem passed_add (i : Fin groups) :
    passed q p c (i.val+1) = passed q p c i.val ++ rows q p (c i) := by
  have live : i.val < (List.ofFn c).length := by simp
  simp [passed, List.take_succ_eq_append_getElem live]

theorem passed_len (i : Fin groups) :
    (passed q p c (i.val+1)).length=(passed q p c i.val).length+poolBatchCount (c i) q := by
  simp [passed_add]

theorem passed_all : passed q p c groups = tape q p c := by
  unfold passed tape
  rw [List.take_of_length_le (List.length_ofFn (f := c)).le]

theorem within (k : ℕ) : (passed q p c k).length ≤ (tape q p c).length := by
  have e : passed q p c k ++ ((List.ofFn c).drop k).flatMap (rows q p)=tape q p c := by
    unfold passed tape
    rw [← List.flatMap_append, List.take_append_drop]
  have h := congrArg List.length e
  simp only [List.length_append] at h
  omega

private theorem complete_row (n i : ℕ) (early : i+1<poolBatchCount n q) :
    min q (n-i*q)=q := by
  have upper : poolBatchCount n q*q≤n+q-1 := Nat.div_mul_le_self _ _
  have lower := Nat.mul_le_mul_right q (show i+2≤poolBatchCount n q by omega)
  rw [Nat.add_mul] at lower
  apply Nat.min_eq_left
  omega

/-- Encoded output after patching exactly the first k groups. -/
def value (k j : ℕ) := if hit : j<(passed q p c k).length then
    (encode q p ((passed q p c k)[j])).val
  else if j<(tape q p c).length then full q p else blank q p

theorem initial (j : ℕ) : value q p c 0 j =
    if j<(tape q p c).length then full q p else blank q p := by simp [value,passed]

theorem finish {R : ℕ} (i : Fin R) :
    value q p c groups i.val=(encode q p (padded (tape q p c) i)).val := by
  by_cases h : i.val<(tape q p c).length <;>
    simp [value,passed_all,padded,h,blank,List.get_eq_getElem]

theorem update (i : Fin groups) (j : ℕ) :
    value q p c (i.val+1) j = if poolBatchCount (c i) q ≠ 0 ∧
      j+1=(passed q p c (i.val+1)).length then tailCode q p (c i) else value q p c i.val j := by
  let old := passed q p c i.val
  let n := poolBatchCount (c i) q
  have len := passed_len q p c i
  have lim := within q p c (i.val+1)
  change (passed q p c (i.val+1)).length=old.length+n at len
  by_cases stable : j<old.length
  · have live : j<(passed q p c (i.val+1)).length := by omega
    have no : ¬(poolBatchCount (c i) q≠0 ∧ j+1=(passed q p c (i.val+1)).length) := by
      change ¬(n≠0 ∧ _)
      omega
    have was : j<(passed q p c i.val).length:=stable
    have eqn : (passed q p c (i.val+1))[j]=(passed q p c i.val)[j] := by
      simp only [passed_add,List.getElem_append_left was]
    simp only [value,dite_eq_left live,dite_eq_left was,ite_eq_right no,eqn]
  · by_cases arrived : j<old.length+n
    · have live : j<(passed q p c (i.val+1)).length := by omega
      have global : j<(tape q p c).length := by omega
      have atRow : ((passed q p c (i.val+1))[j]) =
          mask q p (min q (c i-(j-old.length)*q)) := by
        have later : (passed q p c i.val).length≤j:=Nat.le_of_not_gt stable
        simp [passed_add,List.getElem_append_right later,rows,old]
      by_cases last : j+1=old.length+n
      · have yes : poolBatchCount (c i) q≠0 ∧ j+1=(passed q p c (i.val+1)).length := by
          change n≠0 ∧ _;omega
        have digit : j-old.length=poolBatchCount (c i) q-1 := by change _=n-1;omega
        simp only [value,dite_eq_left live,ite_eq_left yes,atRow,tailCode,digit]
      · have early : j-old.length+1<poolBatchCount (c i) q := by change _<n;omega
        have no : ¬(poolBatchCount (c i) q≠0 ∧ j+1=(passed q p c (i.val+1)).length) := by omega
        simp only [value,dite_eq_left live,dite_eq_right (show ¬j<(passed q p c i.val).length from stable),
          ite_eq_right no,ite_eq_left global,atRow,complete_row q (c i) _ early,full]
    · have none : ¬j<(passed q p c (i.val+1)).length := by omega
      have no : ¬(poolBatchCount (c i) q≠0 ∧ j+1=(passed q p c (i.val+1)).length) := by omega
      simp only [ite_eq_right no,value,dite_eq_right none,dite_eq_right (show ¬j<(passed q p c i.val).length from stable)]


end
end Hierarchy.DescentTerminalWidthRowsRAM

end OAI
