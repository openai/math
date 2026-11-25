import OAI.Computability.BorderVNP.TeamPrivateInput
import OAI.Computability.BorderVNP.TeamSiteLayout
import OAI.Computability.BorderVNP.TeamClockedProgram

/-! # Restoring the physical private clock at the beginning of each call

The caller retains one trusted unary template. The routine copies it into an empty
loader, restores the template, and spreads the encoded clock symbol across the
right stacks of the added native tape. The first clock symbol remains in finite control.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateMeterReset

open VPVNP RAMTape
variable {g : ℕ}

/-- The two copy ports and the existing first-symbol loader's ports. -/
inductive Port (g : ℕ) where
  | template
  | copyScratch
  | loader (p : TeamPrivateInput.Port g)
  deriving DecidableEq, Fintype

/-- Copy the number of trusted remaining steps and restore the original template. -/
def copy (g : ℕ) : FiniteRoutine (Port g) :=
  FiniteRoutine.ofRoutine (Tally.copyAdd .template (.loader .raw) .copyScratch)

private def source (g N : ℕ) : Tally.State (Port g)
  | .template => N
  | _ => 0

/-- The initial physical port image for a fresh call, with all clock-private scratch empty. -/
def initial (g N : ℕ) : Stacks (Port g) := Tally.encode (source g N)

private def copied (g N : ℕ) : Stacks (Port g) :=
  Tally.encode (Function.update (source g N) (.loader .raw) N)

/-- The terminal physical stacks: the original template, empty scratch, and the encoded
right neighbors of the unary timer. The left timer stacks are outside this port set. -/
def filled (markBits : Fin g → Bool) (N : ℕ) : Stacks (Port g)
  | .template => List.replicate N true
  | .loader (.lane j) => List.replicate (N-1) (markBits j)
  | _ => []

/-- Fixed finite control that performs the copy followed by loading the unary symbols. -/
abbrev State (g : ℕ) := (copy g).State ⊕ TeamPrivateInput.State g

/-- On completion of the unary copy, the original clock-symbol input loader takes
control and records the first symbol in its finite state. -/
def code (markBits : Fin g → Bool) : StackCode (Port g) (State g)
  | .inl q => ((copy g).body.code q).rename id (Option.elim · (.inr .start) Sum.inl)
  | .inr q => (TeamPrivateInput.code (fun _ => markBits) q).rename Port.loader Sum.inr

/-- Entry to the native clock reset fragment. -/
def entry (g : ℕ) : State g := .inl (copy g).body.entry

/-- Exact physical reset steps, independent of the macro input and choices. -/
def steps (g N : ℕ) := (5*N+2) + ((g+4)*(N-1)+3)

private theorem copy_runs (g N : ℕ) : (copy g).Runs (5*N+2) (initial g N) (copied g N) := by
  have run := Tally.copyAdd_runs (.template : Port g) (.loader .raw) .copyScratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (source g N) rfl
  change (copy g).Runs (5*N+2) (initial g N) (Tally.encode (Function.update (source g N) (.loader .raw) (0+N))) at run
  simpa only [Nat.zero_add,copied] using run

/-- An elementary finite reset preserving the original trusted template, with a
correct initial head marker on both empty and positive budgets. -/
theorem runs (markBits : Fin g → Bool) (N : ℕ) :
    StackRuns (code markBits) (steps g N) (entry g) (initial g N)
      (.inr (.done (List.replicate N true).head?)) (filled markBits N) := by
  let label (z : Option (copy g).State) : State g := z.elim (.inr .start) Sum.inl
  have row (q) (hc : ((copy g).body.standalone q).returns = false) :
      code markBits (label q) = ((copy g).body.standalone q).rename id label := by
    cases q with
    | none => contradiction
    | some q => rfl
  have first := (copy_runs g N).lift id Function.injective_id label (initial g N) row
  have ident (s : Stacks (Port g)) : installStacks id (initial g N) s = s := by
    funext i; exact installStacks_at Function.injective_id ..
  rw [ident,ident] at first
  have inj : Function.Injective (@Port.loader g) := fun _ _ => Port.loader.inj
  let word := List.replicate N true
  have body := (TeamPrivateInput.runs (fun _ => markBits) word).lift Port.loader inj
    (target := code markBits) Sum.inr (copied g N) (fun _ _ => rfl)
  have before (i : TeamPrivateInput.Port g) : copied g N (.loader i) =
      TeamPrivateInput.store word [] (fun _ => []) i := by
    cases i <;> simp [copied,source,Tally.encode,TeamPrivateInput.store,word]
  have after (i : TeamPrivateInput.Port g) : filled markBits N (.loader i) =
      TeamPrivateInput.store [] [] (fun j => word.tail.map fun _ => markBits j) i := by
    cases i with
    | raw | scratch => rfl
    | lane j => cases N <;> simp [filled,TeamPrivateInput.store,word,List.replicate_succ]
  have outside (p : Port g) (hp : ∀ i, Port.loader i ≠ p) : filled markBits N p = copied g N p := by
    cases p with
    | template | copyScratch => rfl
    | loader i => exact (hp i rfl).elim
  rw [installStacks_eq inj _ _ before,installStacks_frame inj after outside] at body
  have size : TeamPrivateInput.steps g word = (g+4)*(N-1)+3 := by cases N <;> simp [TeamPrivateInput.steps,word,List.replicate_succ]
  rw [size] at body
  exact first.trans body

/-- Embed the reset in the true clock-wrapped site. Its three temporary stacks
are disjoint from the real burst input and from every original private tape. -/
def wired (reg k m g : ℕ) : Port g → TeamClocked.Port (TeamSite.Layout.Port reg k ((m+1)*g))
  | .template => .tally .fuel
  | .copyScratch => .reader .tmp
  | .loader .raw => .reader .input
  | .loader .scratch => .reader .size
  | .loader (.lane j) => .user (TeamSite.Layout.site (.track (finProdFinEquiv ((0 : Fin (m+1)),j),true)))

/-- Distinct reset ports are distinct actual site stacks. -/
theorem wired_injective (reg k m g : ℕ) : Function.Injective (wired reg k m g) := by
  rintro (_ | _ | (_ | _ | i)) (_ | _ | (_ | _ | j)) eq <;> simp_all [wired,TeamSite.Layout.site]

/-- A linked reset on the physical processor leaves all unrelated processor stacks
untouched and replaces exactly the timer lane values. -/
theorem runs_wired {reg k m : ℕ} {Q : Type} (markBits : Fin g → Bool) (N : ℕ)
    (target : StackCode (TeamClocked.Port (TeamSite.Layout.Port reg k ((m+1)*g))) Q) (label : State g → Q)
    (s : Stacks (TeamClocked.Port (TeamSite.Layout.Port reg k ((m+1)*g))))
    (ready : ∀ i, s (wired reg k m g i) = initial g N i)
    (rows : ∀ q, (code markBits q).returns = false →
      target (label q) = (code markBits q).rename (wired reg k m g) label) :
    StackRuns target (steps g N) (label (entry g)) s (label (.inr (.done (List.replicate N true).head?)))
      (installStacks (wired reg k m g) s (filled markBits N)) := by
  have run := (runs markBits N).lift _ (wired_injective reg k m g) label s rows
  rwa [installStacks_eq (wired_injective reg k m g) _ _ ready] at run

end TeamPrivateMeterReset

end BorderVNP
end Computability
end OAI
