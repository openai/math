import OAI.Computability.BorderVNP.FiniteOutputSelect
import OAI.Computability.BorderVNP.FiniteTeamReplay

/-! # Choice-tape accounting for the finite-field return selector

A numbered return class introduces one canonical prefix. The remainder of the
tape is exactly the branch tape of that class's native verifier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldSelect

open VPVNP.RAMTape
variable {K Q : Type} [DecidableEq K] {F : Type*} [Field F] {k : ℕ}

/-- Once a return class is entered, the branch tape and terminal weight are exactly
those of its private verifier, at the same clock. -/
theorem leaves_body (p : Fin k → StackCode K Q) (w : Fin k → Q → F) (start : Q)
    (t : ℕ) (i : Fin k) (q : Q) (s : Stacks K) :
    FieldReplay.leaves (code p start) (output w) t (.body i q) s =
      FieldReplay.leaves (p i) (w i) t q s := by
  induction t generalizing q s with
  | zero => rfl
  | succ t ih =>
    cases op : p i q <;> simp only [FieldReplay.leaves, code, output, op, StackOp.rename,
      Function.id_def, Function.comp_apply, ih]

/-- Skipping classes uses one true bit per skip and the selecting false bit. -/
def choiceTape (skip : ℕ) (rest : List Bool) : List Bool :=
  List.replicate skip true ++ false :: rest

private theorem tape_succ (d : ℕ) (tail : List Bool) :
    choiceTape (d+1) tail = true :: choiceTape d tail := by
  simp [choiceTape,List.replicate_succ]

/-- The exact physical choice strings, including the clock paid for the selector.
An empty field class and the unused final rejection contribute no successful string. -/
theorem mem_selection_iff (p : Fin k → StackCode K Q) (w : Fin k → Q → F) (start : Q)
    (s : Stacks K) (v : F) (j : ℕ) (hj : j ≤ k) (ticks : ℕ) (bs : List Bool) :
    (bs,v) ∈ FieldReplay.leaves (code p start) (output w) ticks (.select ⟨j,by omega⟩) s ↔
      ∃ (i : Fin k) (skip : ℕ), i.val + skip + 1 = j ∧ ∃ rest,
        bs = choiceTape skip rest ∧ (rest,v) ∈ FieldReplay.leaves (p i) (w i) (ticks-(skip+1)) start s := by
  induction j generalizing ticks bs with
  | zero =>
    cases ticks <;> simp [FieldReplay.leaves,code]
  | succ j ih =>
    cases ticks with
    | zero => simp [FieldReplay.leaves]
    | succ ticks =>
      let i : Fin k := ⟨j,by omega⟩
      have op : code p start (.select i.succ) = .choose (.body i start) (.select i.castSucc) := by
        simp [code,i,Fin.succ,Fin.castSucc]
      change (bs,v) ∈ FieldReplay.leaves (code p start) (output w) (ticks+1) (.select i.succ) s ↔ _
      rw [FieldReplay.mem_choose_iff _ _ _ _ _ _ _ op,leaves_body]
      constructor
      · rintro (⟨rest,rfl,hm⟩ | ⟨tail,rfl,hm⟩)
        · exact ⟨i,0,by simp [i],rest,rfl,by simpa using hm⟩
        · obtain ⟨a,d,hd,rest,rfl,hchild⟩ := (ih (by omega : j ≤ k) ticks tail).mp hm
          exact ⟨a,d+1,by omega,rest,(tape_succ ..).symm,by simpa using hchild⟩
      · rintro ⟨a,d,ha,rest,rfl,hm⟩
        cases d with
        | zero =>
          have eq : a = i := Fin.ext (by dsimp [i]; omega)
          subst a
          exact Or.inl ⟨rest,rfl,by simpa using hm⟩
        | succ d =>
          apply Or.inr
          refine ⟨choiceTape d rest,tape_succ ..,(ih (by omega : j ≤ k) ticks _).mpr ?_⟩
          exact ⟨a,d,by omega,rest,rfl,by simpa using hm⟩

/-- The branch tape determines both the selected class's unary prefix and the
consumed native verifier suffix, regardless of any bits following the delimiter. -/
theorem choiceTape_injective {j k : ℕ} {xs ys : List Bool}
    (h : choiceTape j xs = choiceTape k ys) : j = k ∧ xs = ys := by
  induction j generalizing k with
  | zero => cases k with
            | zero => simpa [choiceTape] using h
            | succ k => simp [choiceTape,List.replicate_succ] at h
  | succ j ih =>
    cases k with
    | zero => simp [choiceTape,List.replicate_succ] at h
    | succ k =>
      rw [tape_succ,tape_succ,List.cons.injEq] at h
      obtain ⟨rfl,rfl⟩ := ih h.2
      exact ⟨rfl,rfl⟩

end FieldSelect

end BorderVNP
end Computability
end OAI
