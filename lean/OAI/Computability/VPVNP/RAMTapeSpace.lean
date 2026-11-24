import OAI.Computability.VPVNP.RAMTapeSpaceAccess
import OAI.Computability.VPVNP.RAMTapeSpacePaths

/-!
# Space preservation by the two-tape stack compiler

At every instruction boundary, the first head has moved left by the growth
in the packed bank since initialization, and the scratch head has returned
to its initial cell. An unfinished instruction can move either head by at
most its own linear scan time. These bounds do not accumulate with the
number of completed instructions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine Turing

variable {k : ℕ} {Q : Type*}

/-- Stack states on any branch starting from the specified initial bank. -/
inductive Reach {K : Type*} [DecidableEq K] (code : StackCode K Q) (start : Q) (initial : Stacks K) :
    Q → Stacks K → Prop
  | initial : Reach code start initial start initial
  | step {q s q' s'} : Reach code start initial q s → StackStep code q s q' s' →
      Reach code start initial q' s'
  | low {q s l h} : Reach code start initial q s → code q = .choose l h → Reach code start initial l s
  | high {q s l h} : Reach code start initial q s → code q = .choose l h → Reach code start initial h s

/-- Each tape head lies in the interval from minus the radius to plus the radius. -/
def HeadBox (radius : ℕ) (dx dy : ℤ) : Prop :=
  -(radius : ℤ) ≤ dx ∧ dx ≤ radius ∧ -(radius : ℤ) ≤ dy ∧ dy ≤ radius

private theorem space_from {code : StackCode (Fin k) Q} {q₀ q : Q} {s₀ s : Stacks (Fin k)}
    {M : ℕ} (bounded : ∀ ⦃q' s'⦄, Reach code q₀ s₀ q' s' → (packed s').length ≤ M)
    (reach : Reach code q₀ s₀ q s) {n : ℕ} {dx dy : ℤ} {r x y}
    (p : HeadPath (rows code) n dx dy (.ready q) (tapeList (packed s)) (tapeList []) r x y) :
    HeadBox (7*M+4) ((packed s₀).length - (packed s).length + dx) dy := by
  induction n using Nat.strong_induction_on generalizing q s dx dy r x y with
  | h n ih =>
    have hbase := bounded (.initial : Reach code q₀ s₀ q₀ s₀)
    have hsize := bounded reach
    have deterministic {q' s'} (step : StackStep code q s q' s') :
        HeadBox (7*M+4) ((packed s₀).length - (packed s).length + dx) dy := by
      obtain ⟨t, ht, hcost, travel⟩ := step_travel code step
      by_cases hlen : t ≤ n
      · obtain ⟨m, ex, ey, hm, hx, hy, tail⟩ := travel.suffix p hlen
        have bound := ih m (by omega) (.step reach step) tail
        have he : (packed s₀).length - (packed s).length + dx =
            ((packed s₀).length : ℤ) - (packed s').length + ex := by omega
        rwa [he, hy, Int.zero_add]
      · have := p.range
        unfold HeadBox
        push_cast
        omega
    cases hc : code q with
    | push i b q' => exact deterministic (.push hc)
    | pop i f => exact deterministic (.pop hc)
    | goto q' => exact deterministic (.goto hc)
    | choose l h =>
      cases p with
      | nil =>
        unfold HeadBox
        push_cast
        omega
      | cons hp tail =>
        simp only [rows, hc, Choices.contains] at hp
        rcases hp with hp | hp
        · cases hp
          simpa only [delta_stay, update_stay, Int.zero_add] using
            ih _ (Nat.lt_succ_self _) (.low reach hc) (by simpa only [update_stay] using tail)
        · cases hp
          simpa only [delta_stay, update_stay, Int.zero_add] using
            ih _ (Nat.lt_succ_self _) (.high reach hc) (by simpa only [update_stay] using tail)
    | halt b =>
      cases p with
      | nil =>
        unfold HeadBox
        push_cast
        omega
      | cons hp _ => simp [rows, hc, Choices.contains] at hp

/-- On either tape every cell visited by every finite prefix lies within
radius 7M+4 of the initial head, uniformly over the execution time. -/
theorem headPath_space {code : StackCode (Fin k) Q} (start : Q) (s : Stacks (Fin k)) {M : ℕ}
    (bounded : ∀ ⦃q' s'⦄, Reach code start s q' s' → (packed s').length ≤ M)
    {n dx dy r x y}
    (p : HeadPath (rows code) n dx dy (.ready start) (tapeList (packed s)) (tapeList []) r x y) :
    HeadBox (7*M+4) dx dy := by
  simpa using space_from bounded Reach.initial p

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI
