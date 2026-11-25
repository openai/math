import OAI.LinearAlgebra.SpectralBooks.SignedMachine

/-!
# Counting work-symbol tests in the machine interpreter

The rule search compares a rule's state and input symbol before inspecting any work
tape. The count records one test for each comparison of a work head with a symbol.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedMachine

/-- Compare the requested symbols with the work heads, stopping at the first mismatch. -/
def matchWork : List Symbol → List Tape → Bool × ℕ
  | [], [] => (true, 0)
  | [], _ :: _ | _ :: _, [] => (false, 0)
  | s :: ss, t :: ts =>
    if s == t.head then
      let rest := matchWork ss ts
      (rest.1, rest.2 + 1)
    else (false, 1)

theorem matchWork_spec (ss : List Symbol) (ts : List Tape) :
    (matchWork ss ts).1 = (ss == ts.map Tape.head) ∧ (matchWork ss ts).2 ≤ ts.length := by
  induction ss generalizing ts with
  | nil => cases ts <;> exact ⟨rfl, Nat.zero_le _⟩
  | cons s ss ih =>
    cases ts with
    | nil => trivial
    | cons t ts =>
      have ⟨h₁, h₂⟩ := ih ts
      change (matchWork (s :: ss) (t :: ts)).1 = ((s == t.head) && (ss == ts.map Tape.head)) ∧ _
      cases e : s == t.head <;> simp [matchWork, e, h₁, h₂]

/-- Find the first applicable rule, counting the work-symbol tests actually performed. -/
def scanRules (cfg : Config) : List Rule → Option Rule × ℕ
  | [] => (none, 0)
  | r :: rs =>
    if r.state == cfg.state && r.inputSymbol == cfg.inputTape.head then
      let tested := matchWork r.workSymbols cfg.work
      if tested.1 then (some r, tested.2)
      else
        let rest := scanRules cfg rs
        (rest.1, tested.2 + rest.2)
    else scanRules cfg rs

/-- The profiled search selects the rule used by `Program.next`. Even malformed rules
with too many requested symbols perform at most one comparison per actual tape. -/
theorem scanRules_spec (cfg : Config) (rs : List Rule) :
    (scanRules cfg rs).1 = rs.find? (fun r ↦ r.state == cfg.state &&
      r.inputSymbol == cfg.inputTape.head && r.workSymbols == cfg.work.map Tape.head) ∧
    (scanRules cfg rs).2 ≤ rs.length * cfg.work.length := by
  induction rs with
  | nil => simp [scanRules]
  | cons r rs ih =>
    obtain ⟨hf, hc⟩ := ih
    have ⟨hm, ht⟩ := matchWork_spec r.workSymbols cfg.work
    cases e : (r.state == cfg.state && r.inputSymbol == cfg.inputTape.head)
    · simp [scanRules, e, hf, Nat.succ_mul]
      omega
    · cases w : (matchWork r.workSymbols cfg.work).1 <;>
        simp [scanRules, e, ← hm, w, hf, Nat.succ_mul] <;> omega

end SignedMachine

end SpectralBooks
end LinearAlgebra
end OAI
