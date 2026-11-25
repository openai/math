import Mathlib.Data.List.Basic

namespace OAI
/-! # The stable first minimum of a finite list -/

namespace Hierarchy.DescentColonies

/-- Scan a finite candidate list. The cached pair stores the winning score,
so each visited candidate invokes the cost function once. -/
def scanMinimum {S : Type*} (cost : S → ℕ) : List S → Option (S × ℕ) × ℕ
  | [] => (none,0)
  | s::ss =>
    let tail := scanMinimum cost ss
    let value := cost s
    let winner := match tail.1 with
      | none => (s,value)
      | some p => if value ≤ p.2 then (s,value) else p
    (some winner,tail.2+1)

theorem scanMinimum_spec {S : Type*} (cost : S → ℕ) (ss : List S) :
    (scanMinimum cost ss).2=ss.length ∧
    (match (scanMinimum cost ss).1 with
      | none => ss=[]
      | some p => p.2=cost p.1 ∧ ∀t∈ss,p.2≤cost t) := by
  induction ss with
  | nil => exact ⟨rfl,rfl⟩
  | cons s ss ih =>
    refine ⟨congrArg Nat.succ ih.1,?_⟩
    have previous := ih.2
    cases h : (scanMinimum cost ss).1 with
    | none =>
      simp only [h] at previous
      subst ss
      simp [scanMinimum]
    | some p =>
      simp only [h] at previous
      by_cases keep : cost s≤p.2
      · simp only [scanMinimum,h,ite_eq_left keep]
        refine ⟨True.intro,fun t ht=>?_⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Nat.le_refl _
        · exact Nat.le_trans keep (previous.2 t ht)
      · simp only [scanMinimum,h,ite_eq_right keep]
        refine ⟨previous.1,fun t ht=>?_⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Nat.le_of_not_ge keep
        · exact previous.2 t ht

end Hierarchy.DescentColonies

end OAI
