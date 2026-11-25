import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows

namespace OAI
/-! # The terminal charge bounds the charge at every selected level -/

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- No native ancestor can have a larger accumulated charge than its eventual
owner. Every step includes this precise child's nonnegative summand. -/
theorem charge_le_ancestor {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start : A.Site→ℕ) (x : A.Site) :
    start x≤r.rootArray h C start (r.rawDestination h x) := by
  induction r with
  | done _=>exact le_rfl
  | step R next ih=>
    let v:=R.parent h.1 x
    let j : {a // R.parent h.1 a=v}:=⟨x,rfl⟩
    have one : start x≤∑ a : {a // R.parent h.1 a=v},start a.val:=
      Finset.single_le_sum (fun a _=>Nat.zero_le (start a.val)) (Finset.mem_univ j)
    have pushed : start x≤R.push h.1 (C.1 h.1) start v:=one.trans (Nat.le_add_left ..)
    exact pushed.trans (ih h.1 (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) start) v)

/-- The same dyadic cap holds at every actual level and site, including all
the intermediate stages that the selected emitter can enter. -/
def LevelsCapped (unitWork cap : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) →
    (h : r.plan.History) → r.Charges → (A.Site→ℕ) → Prop
  | _,_,_,.done _,_,_,start=>∀ x,unitWork*start x≤cap
  | _,_,_,.step R next,h,C,start=>(∀ x,unitWork*start x≤cap) ∧
    LevelsCapped unitWork cap (next h.1) (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) start)

theorem levels_capped {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start : A.Site→ℕ) (unitWork cap : ℕ)
    (peak : ∀ z,unitWork*r.rootArray h C start z≤cap) : LevelsCapped unitWork cap r h C start := by
  induction r with
  | done _=>exact peak
  | step R next ih=>
    refine ⟨?_,ih h.1 (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) start) peak⟩
    intro x
    exact (Nat.mul_le_mul_left unitWork ((Run.step R next).charge_le_ancestor h C start x)).trans
      (peak ((Run.step R next).rawDestination h x))

theorem levels_capped_of_terminal {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start : A.Site→ℕ) (unitWork cap : ℕ)
    (peak : ∀ z,r.chargeAt h C start z*unitWork≤cap) : LevelsCapped unitWork cap r h C start := by
  apply levels_capped r h C start unitWork cap
  intro z
  have bound:=peak (r.finalSite h z)
  simpa only [chargeAt,Equiv.symm_apply_apply,Nat.mul_comm unitWork] using bound

end
end ThreeFlat.Diagonal.PhysicalStage.Run

end OAI
