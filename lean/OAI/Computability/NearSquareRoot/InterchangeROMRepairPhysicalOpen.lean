import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalOpenSchedule
import OAI.Computability.NearSquareRoot.InterchangeROMRecursionOpen

/-! # Parent-independent release with request-specific clocks and space -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom InterchangeROM
  InterchangeSpace Space

variable {Q : Type} (leaf : Leaf → List Tree → List Tree) (emit : Leaf → List Tree → List Q)
    (localCost : Leaf → List Tree → Allowance) (h : Tree)

private theorem peak_append (f : Q → ℕ) (a b : List Q) :
    childPeak f (a++b) = max (childPeak f a) (childPeak f b) := by
  apply le_antisymm
  · apply childPeak_le
    intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact (le_childPeak f hq).trans (le_max_left ..)
    · exact (le_childPeak f hq).trans (le_max_right ..)
  · apply max_le
    · exact childPeak_le _ _ _ fun _ hq => le_childPeak _ (List.mem_append_left _ hq)
    · exact childPeak_le _ _ _ fun _ hq => le_childPeak _ (List.mem_append_right _ hq)

/-- Adding request-specific clocks to each leaf adds exactly their sum to
the schedule's clock. The tape and return peaks each reserve one child. -/
theorem allowance_split (ss : List Step) (xs : List Tree) (time data depth : Q → ℕ) :
    let full a u := withChildren (localCost a u) (emit a u) time data depth
    let stand := allowance leaf localCost h ss xs
    let run := allowance leaf full h ss xs
    let qs := docket leaf emit ss xs
    run.time = stand.time + (qs.map time).sum ∧
      run.cap ≤ stand.cap + childPeak data qs ∧ run.depth ≤ stand.depth + childPeak depth qs := by
  induction ss generalizing xs with
  | nil => exact ⟨rfl,le_rfl,le_rfl⟩
  | cons s ss ih =>
    let full a u := withChildren (localCost a u) (emit a u) time data depth
    let head := emit s.2 (xs.drop s.1)
    let rest := docket leaf emit ss (applyStep leaf xs s)
    let A := stageAllowance leaf localCost h xs s
    let B := allowance leaf localCost h ss (applyStep leaf xs s)
    let A' := stageAllowance leaf full h xs s
    let B' := allowance leaf full h ss (applyStep leaf xs s)
    have atime : A'.time = A.time + (head.map time).sum := by
      dsimp [A',A,full,stageAllowance,withChildren,head]; omega
    have acap : A'.cap = A.cap + childPeak data head := by
      dsimp [A',A,full,stageAllowance,withChildren,head]; omega
    have adepth : A'.depth = A.depth + childPeak depth head := by
      dsimp [A',A,full,stageAllowance,withChildren,head]; omega
    obtain ⟨bt,bc,bd⟩ := ih (applyStep leaf xs s)
    change B'.time = B.time + (rest.map time).sum at bt
    change B'.cap ≤ B.cap + childPeak data rest at bc
    change B'.depth ≤ B.depth + childPeak depth rest at bd
    change A'.time+B'.time+2 = A.time+B.time+2+((head++rest).map time).sum ∧
      max A'.cap B'.cap ≤ max A.cap B.cap+childPeak data (head++rest) ∧
      max (A'.depth+1) B'.depth ≤ max (A.depth+1) B.depth+childPeak depth (head++rest)
    rw [List.map_append,List.sum_append,peak_append,peak_append,atime,bt,acap,adepth]
    exact ⟨by omega,by omega,by omega⟩

private theorem ready_in_docket (dom : Leaf → List Tree → Prop) (ss : List Step) (xs : List Tree)
    (ok : Ready leaf dom ss xs) {all : List Q} (inc : ∀ q ∈ docket leaf emit ss xs, q ∈ all) :
    Ready leaf (fun a u => dom a u ∧ ∀ q ∈ emit a u, q ∈ all) ss xs := by
  induction ss generalizing xs with
  | nil => trivial
  | cons s ss ih =>
    exact ⟨ok.1,⟨ok.2.1,fun q hq => inc q (List.mem_append_left _ hq)⟩,
      ih _ ok.2.2 fun q hq => inc q (List.mem_append_right _ hq)⟩

/-- No child solver outside the emitted list is required. The generated
command and its ledger do not depend on the recursive parent or its prices. -/
theorem command_open (job : Job Q) (prog : Leaf → Cmd) (dom : Leaf → List Tree → Prop)
    (stepsOpen : ∀ a u, dom a u →
      let z := localCost a u
      InterchangeROMSequence.Step job (prog a) h (Task.forest id u) (packet h (leaf a u)) (emit a u)
        z.time z.cap z.depth)
    (ss : List Step) (xs : List Tree) (ok : Ready leaf dom ss xs) :
    let a := allowance leaf localCost h ss xs
    InterchangeROMSequence.Step job (command prog ss) h (Task.forest id xs) (packet h (runSteps leaf ss xs))
      (docket leaf emit ss xs) a.time a.cap a.depth := by
  intro a parent env time data depth child r base hr
  let full k u := withChildren (localCost k u) (emit k u) time data depth
  let dom' k u := dom k u ∧ ∀ q ∈ emit k u, q ∈ docket leaf emit ss xs
  have realizes : Realizes leaf dom' full prog h (parent::env) := by
    intro k u good d b hd
    have run := stepsOpen k u good.1 parent env time data depth
      (fun q hq => child q (good.2 q hq)) d b hd
    exact run.mono le_rfl (by apply le_of_eq; exact Nat.add_assoc ..) le_rfl
  have admitted : Ready leaf dom' ss xs := ready_in_docket leaf emit dom ss xs ok fun _ hx => hx
  have run := command_bounded realizes ss xs admitted r base hr
  obtain ⟨ht,hc,hd⟩ := allowance_split leaf emit localCost h ss xs time data depth
  apply run.mono ht.le _ hd
  exact (Nat.add_le_add_left hc base).trans (Nat.add_assoc ..).symm.le

/-- The single small-child list used by the interchange recursion. -/
theorem at_of_open {job : Job Q} {c : Cmd} {h u v : Tree} {qs : List Q} {t s d K : ℕ}
    (run : InterchangeROMSequence.Step job c h u v qs t s d) (ht : t ≤ K) (hs : s ≤ K) (hd : d ≤ K)
    (parent : Cmd) : InterchangeROMRecursion.At parent c job qs [] (.fork h u) v K 0 0 := by
  intro env time data depth solve r base hr
  have a := run parent env time data depth (fun y hy => solve y (List.mem_append_left _ hy)) r base hr
  simp only [List.append_nil] at *
  apply a.mono (Nat.add_le_add_right ht _) _ _
  · exact (Nat.add_le_add_right (Nat.add_le_add_left hs base) _).trans <|
      (Nat.add_assoc ..).le.trans (Nat.add_le_add_left (le_max_left ..) base)
  · exact (Nat.add_le_add_right hd _).trans (le_max_left ..)

end InterchangeROMRepair.Physical

end NearSquareRoot
end Computability
end OAI
