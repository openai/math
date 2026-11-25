import OAI.Computability.BorderVNP.TeamSiteProcessorBank

/-! # Running the input and parameter loaders on the full processor

The first phase reads the raw input stack and emits time-zero records into the shared
sort buffer. The next phase measures the retained address word and consumes the
contiguous RAM operands and clock parameters from the literal. Its return preserves
the input parser's other stacks and the entire incident stream.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor
open VPVNP BurstRAM RAMTape Layout

variable {Q Γ : Type} {p r k a m g d w : ℕ}

private theorem entry_injective : Function.Injective (entry (r := r) (k := k) (d := d)) := by
  intro i j e
  cases e
  rfl

private theorem initial_installed (raw : List Bool) :
    installStacks (entry (r := r) (k := k) (d := d)) (fun _ => [])
      (Sum.elim (TeamTapeInput.initial raw) (fun _ => [])) = StackCompiler.labeledInput input raw := by
  funext p
  by_cases hi : ∃ i, entry i = p
  · obtain ⟨i,rfl⟩ := hi
    rw [installStacks_at entry_injective]
    change _ = (if entry i = entry (.inl (.cut .input)) then raw else [])
    simp only [entry_injective.eq_iff]
    rcases i with i | i
    · cases i with
      | cut p => cases p <;> rfl
      | _ => rfl
    · rfl
  · have hn : p ≠ input := fun h => hi ⟨.inl (.cut .input),h.symm⟩
    rw [installStacks_outside _ _ (not_exists.mp hi)]
    simp only [StackCompiler.labeledInput,hn,↓reduceIte]

private theorem fromEntry_installed (small : Stacks TeamTapeInput.Entry.Port) :
    installStacks (entry (r := r) (k := k) (d := d)) (fun _ => []) small = Bank.fromEntry small := by
  funext j
  cases j with
  | route j =>
    rcases j with j | j
    · exact installStacks_outside _ _ (fun i h => by cases h)
    · cases j with
      | entry i => exact installStacks_at entry_injective _ _ i
      | _ => exact installStacks_outside _ _ (fun i h => by cases h)
  | _ => exact installStacks_outside _ _ (fun i h => by cases h)

/-- Every physical input initialization run lifts from the sole occupied raw input stack
to the corresponding full processor bank, retaining its exact cost. -/
theorem initialize_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (raw : List Bool) (small : Stacks TeamTapeInput.Entry.Port) {t : ℕ}
    (run : TeamTapeInput.Entry.program.Runs t
      (Sum.elim (TeamTapeInput.initial raw) (fun _ => [])) small) :
    StackRuns (code P lib) t start (StackCompiler.labeledInput input raw)
      (.parameters (TeamPublicStartup.program (k+8)).body.entry) (Bank.fromEntry small) := by
  have lifted := TeamLink.routine run (code P lib)
    entry entry_injective Label.initialize (.parameters (TeamPublicStartup.program (k+8)).body.entry)
    (fun _ => []) (fun _ => rfl)
  rwa [initial_installed,fromEntry_installed] at lifted

private abbrev blankPublic (s : Stacks TeamTapeInput.Entry.Port) : Stacks (TeamPublicStartup.Port (k+8)) :=
  Sum.elim s (fun _ => [])

private theorem public_before (s : Stacks TeamTapeInput.Entry.Port) (i : TeamPublicStartup.Port (k+8)) :
    Bank.fromEntry s (publicPort (r := r) (d := d) i) = blankPublic s i := by
  rcases i with i | i
  · rfl
  · cases i with
    | pub i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [publicPort,paramPort,Fin.append_left]
        rfl
      · simp only [publicPort,paramPort,Fin.append_right]
        fin_cases j <;> rfl
    | _ => rfl

private abbrev paramsLoaded (small : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w)
    (H limit max : Word w) (tail : List Bool) : Stacks (Layout.Port r k d) :=
  Bank.loaded small pub H limit max tail (small (.inl (.cut .incident))) [] [] []

private theorem public_after (s : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w)
    (H limit max : Word w) (tail : List Bool) (i : TeamPublicStartup.Port (k+8)) :
    paramsLoaded (r := r) (d := d) s pub H limit max tail (publicPort i) =
      TeamPublicStartup.loaded (blankPublic s) (parameters pub H limit max) tail i := by
  rcases i with i | i
  · rcases i with i | i
    · cases i with
      | cut u | peek u => cases u <;> rfl
      | _ => rfl
    · rfl
  · cases i with
    | pub i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [TeamPublicStartup.loaded,publicPort,paramPort,parameters,Fin.append_left]
        rfl
      · simp only [TeamPublicStartup.loaded,publicPort,paramPort,parameters,Fin.append_right]
        fin_cases j <;> rfl
    | _ => rfl

private theorem public_outside (s : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w)
    (H limit max : Word w) (tail : List Bool) (j : Layout.Port r k d)
    (hj : ∀ i, publicPort i ≠ j) :
    paramsLoaded s pub H limit max tail j = Bank.fromEntry s j := by
  have hp (i : Fin k) := hj (.inr (.pub (i.castAdd 8)))
  have hh (i : Fin 8) := hj (.inr (.pub (i.natAdd k)))
  simp only [publicPort,paramPort,Fin.append_left] at hp
  simp only [publicPort,paramPort,Fin.append_right] at hh
  cases j with
  | route j =>
    rcases j with j | j
    · rfl
    · cases j with
      | entry i => exact (hj (.inl i) rfl).elim
      | _ => rfl
  | width => exact (hj (.inr .width) rfl).elim
  | work j =>
    cases j with
    | clock u =>
      cases u with
      | isa v =>
        cases v with
        | pub i => exact (hp i rfl).elim
        | persistent => exact (hh 3 rfl).elim
        | _ => rfl
      | meter v =>
        cases v with
        | reg i =>
          fin_cases i <;> first | rfl | exact (hh 0 rfl).elim | exact (hh 1 rfl).elim |
            exact (hh 5 rfl).elim | exact (hh 6 rfl).elim | exact (hh 7 rfl).elim
        | persistent => exact (hh 4 rfl).elim
        | _ => rfl
      | maxBurst => exact (hh 2 rfl).elim
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- The common processor loads all RAM parameters and eight meter words, consumes
exactly their public bytes, and resumes at frame measurement on its original incident bits. -/
theorem parameters_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (small : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w)
    (H limit max : Word w) (tail : List Bool)
    (width : (small (.inr .start)).length = w+1)
    (literal : small (.inl (.peek .input)) = TeamPublicWords.bytes (parameters pub H limit max) ++ tail) :
    StackRuns (code P lib) ((5*(w+1)+2+2) + ((k+8)*(6*w+2)+1))
      (.parameters (TeamPublicStartup.program (k+8)).body.entry) (Bank.fromEntry small)
      (.measure frameMarks.body.entry)
      (Bank.loaded small pub H limit max tail (small (.inl (.cut .incident))) [] [] []) := by
  let args := parameters pub H limit max
  let base : Stacks (Layout.Port r k (m*g)) := Bank.fromEntry small
  let out := TeamPublicStartup.loaded (blankPublic small) args tail
  have run := TeamPublicStartup.runs (blankPublic small) args tail width literal rfl rfl (fun _ => rfl)
  have before : installStacks publicPort base (blankPublic small) = base :=
    installStacks_eq publicPort_injective _ _ (public_before small)
  have after : installStacks publicPort base out = paramsLoaded small pub H limit max tail := by
    funext j
    by_cases hi : ∃ i, publicPort i = j
    · obtain ⟨i,rfl⟩ := hi
      exact (installStacks_at publicPort_injective base out i).trans (public_after ..).symm
    · exact (installStacks_outside _ _ (not_exists.mp hi)).trans
        (public_outside small pub H limit max tail j (not_exists.mp hi)).symm
  have lifted := TeamLink.routine run (code P lib) publicPort publicPort_injective Label.parameters
    (.measure frameMarks.body.entry) base (fun _ => rfl)
  rwa [before,show installStacks publicPort base (TeamPublicStartup.loaded (blankPublic small) args tail) =
    paramsLoaded small pub H limit max tail from after] at lifted

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
