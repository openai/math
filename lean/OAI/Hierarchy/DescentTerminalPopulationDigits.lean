import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Add the common number of attached pins to each lane's charged atoms -/
namespace Hierarchy.DescentTerminalPopulation
open DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {G H M a : ℕ}

/-- A page per input chunk moves its old charged digits to their true
positions in the transmitted terminal word. -/
def part (a b G M : ℕ) (q : Fin (chunks G M)) (key : Cell (a*M)) : ℕ :=
  ∑ i : Fin G, if i.val/M=q.val then (2^b)^i.val*digit a (i.val%M) key.val else 0

def common (b G ext : ℕ) : ℕ := ∑i : Fin G,(2^b)^i.val*ext

def words (b : ℕ) (paid : Fin H→Fin G→Cell a) (ext : Fin H→ℕ) (h : Fin H) : ℕ :=
  common b G (ext h)+∑j:Fin (chunks G M),part a b G M j (data paid (h,j))

private theorem paid_digit (paid : Fin H→Fin G→Cell a) (h : Fin H) (i : Fin G) (pos : 0<M) :
    digit a (i.val%M) (data paid (position h i pos)).val=(paid h i).val := by
  let j:=position h i pos
  let l:=lane i pos
  change digit a l.val (data paid j).val=_
  unfold data
  rw [digit_encode]
  have index : j.2.val*M+l.val=i.val:=Nat.div_add_mod' ..
  simp only [dite_eq_left (index.trans_lt i.isLt)]
  exact congrArg (fun z:Fin G=>(paid h z).val) (Fin.ext index)

theorem packed (paid : Fin H→Fin G→Cell a) (ext : Fin H→ℕ) (b : ℕ) (hm : 0<M)
    (bound : ∀h i,(paid h i).val+ext h<2^b) (h : Fin H) :
    words (M:=M) b paid ext h=(encode b G (fun i=>⟨(paid h i).val+ext h,bound h i⟩)).val := by
  have old : ∑j : Fin (chunks G M),part a b G M j (data paid (h,j))=
      ∑i : Fin G,(2^b)^i.val*(paid h i).val := by
    unfold part
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let q:=(position h i hm).2
    rw [Finset.sum_eq_single q]
    · change (if i.val/M=i.val/M then _ else _) = _
      simp only []
      exact congrArg ((2^b)^i.val*·) (paid_digit paid h i hm)
    · intro j _ away
      simp only [ite_eq_right (show i.val/M≠j.val from fun eqn=>away (Fin.ext eqn.symm))]
    · simp
  rw [words,old]
  unfold common
  change _=(finFunctionFinEquiv (fun i:Fin G=>(⟨(paid h i).val+ext h,bound h i⟩ : Cell b))).val
  rw [finFunctionFinEquiv_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem digit_word (paid : Fin H→Fin G→Cell a) (ext : Fin H→ℕ) (b w : ℕ) (hm : 0<M)
    (wide : b*G≤w) (bound : ∀h i,(paid h i).val+ext h<2^b) (h : Fin H) (i : Fin G) :
    digit b i.val ((words (M:=M) b paid ext h:Fin (2^w)).val)=(paid h i).val+ext h := by
  rw [packed paid ext b hm bound,Fin.val_cast_of_lt]
  · exact digit_encode _ i
  · exact (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by decide) wide)

end
end Hierarchy.DescentTerminalPopulation

end OAI
