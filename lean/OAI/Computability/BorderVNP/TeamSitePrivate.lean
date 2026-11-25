import OAI.Computability.BorderVNP.TeamSitePorts
import OAI.Computability.BorderVNP.TeamSiteChoices

/-! # Private macro execution inside the signed processor

The same finite alphabet, entry, input tape and native transition table determine
the RAM's private evaluator and its physical bit-stack code. A private halt returns
one of the three signed weights after clearing every private tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM TeamPrivateTape TeamPrivateFragment TeamSiteChoices

variable {Q Γ : Type} {m g w r k : ℕ}

/-- A fixed native private subroutine. Its architecture and code are independent
of the input length, the processor count and the clock. -/
structure Macro (Q Γ : Type) (m g : ℕ) where
  /-- Encoding of symbols on synchronized bit tracks. -/
  alphabet : Alphabet Γ g
  /-- Native symbol for each input bit. -/
  digit : Bool → Γ
  /-- Tape receiving the consecutive RAM words. -/
  inputTape : Fin m
  /-- Native program with deterministic transitions, private guesses and signed halts. -/
  table : TapeTable Q Γ m
  /-- Initial control state. -/
  start : Q

/-- Private initial tapes built from the actual values read by the burst. -/
def Macro.initial (M : Macro Q Γ m g) (vs : List (Word w)) : Fin (m*g) → Track :=
  tracks M.alphabet (input M.alphabet.blank M.digit M.inputTape (TeamPrivateCall.inputBits vs))

/-- The native evaluator used in the outer RAM's instruction semantics. -/
noncomputable def Macro.eval (M : Macro Q Γ m g) (fuel : ℕ) (vs : List (Word w)) (bits : List Bool) :
    Option TeamRAM.Sign :=
  (TeamPrivateCall.evaluate (trackTable M.alphabet M.table) fuel M.start (M.initial vs) bits).map
    (fun z => TeamPrivateCall.sign z.1)

/-- A signed RAM result uses exactly the bits on a bounded native path. -/
theorem Macro.eval_iff (M : Macro Q Γ m g) (fuel : ℕ) (vs : List (Word w)) (bits : List Bool)
    (result : TeamRAM.Sign) :
    M.eval fuel vs bits = some result ↔
      ∃ n < fuel, ∃ out u, Run (trackTable M.alphabet M.table) n M.start (M.initial vs) bits out u ∧
        TeamPrivateCall.sign out = result := by
  constructor
  · intro h
    obtain ⟨⟨out,u⟩, hn, hs⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨n,hf,run⟩ := TeamPrivateCall.evaluate_spec hn
    exact ⟨n,hf,out,u,run,hs⟩
  · rintro ⟨n, hf, out, u, run, h⟩
    simp [Macro.eval, TeamPrivateCall.evaluate_of_run run hf, h]

/-- The actual private machine reaches a native halt on every branch within the
given number of native clock checks. -/
def Macro.bounded (M : Macro Q Γ m g) (fuel : ℕ) (vs : List (Word w)) : Prop :=
  TeamPrivateValue.TapeStops M.table M.alphabet.blank fuel M.start
    (input M.alphabet.blank M.digit M.inputTape (TeamPrivateCall.inputBits vs))

/-- All possible private prefixes come from the native program even when its
fresh branch supply is chosen after all RAM probe guesses. -/
theorem Macro.prefix_run (M : Macro Q Γ m g) {fuel : ℕ} (vs : List (Word w))
    (bound : M.bounded fuel vs) (s : Supply) :
    ∃ a n, a ≤ n ∧ n < fuel ∧ ∃ out u, Run (trackTable M.alphabet M.table) n M.start
      (M.initial vs) (takeBits s a) out u ∧ M.eval fuel vs (takeBits s a) = some (TeamPrivateCall.sign out) := by
  obtain ⟨a,n,ha,hn,out,u,run⟩ := private_prefix (P := trackTable M.alphabet M.table)
    ((TeamPrivateValue.track_stops_iff _ _ _ _ _).2 bound) s
  exact ⟨a,n,ha,hn,out,u,run,(M.eval_iff ..).2 ⟨n,hn,out,u,run,rfl⟩⟩

/-- Native macro compiler wired directly to the site burst input and its private scratch. -/
noncomputable def Macro.rows (M : Macro Q Γ m g) :
    StackCode (Port r k (m*g)) (TeamPrivateCompiler.Control Q m g) :=
  fun q => (TeamPrivateCompiler.code M.alphabet M.digit M.inputTape M.table M.start q).rename privateTape id

/-- Replaying the real call in the site bank consumes exactly its own native choices.
Only the private workspace is erased, so the outer program and the already emitted
probe records survive the return. -/
theorem Macro.run (M : Macro Q Γ m g) (vs : List (Word w)) {n choices out u}
    (h : Run (trackTable M.alphabet M.table) n M.start (M.initial vs) choices out u)
    (rest : List Bool) (base : Stacks (Port r k (m*g)))
    (ready : base ∘ privateTape = TeamPrivateInput.initial (TeamPrivateCall.inputBits vs)) :
    ∃ t ≤ (2*g+4)*(vs.length*w) + n*(3*(m*g)+2) + 2*(m*g)+5,
      StackRuns (replay M.rows) t (.load .start, choices++rest) base (.result out,rest)
        (installStacks privateTape base (fun _ => [])) := by
  let bs := TeamPrivateCall.inputBits vs
  have src := TeamPrivateCompiler.run_input M.alphabet M.digit M.inputTape M.table M.start bs h rest
  have time := TeamPrivateCompiler.run_input_cost_le M.alphabet M.digit M.inputTape M.table M.start bs h
  have lift := TeamLink.replay_lift src M.rows privateTape privateTape_injective id base (fun _ _ => rfl)
  have he := installStacks_eq privateTape_injective base (TeamPrivateInput.initial bs) (congrFun ready)
  rw [show bs.length = vs.length*w from TeamPrivateCall.inputBits_length vs] at time
  exact ⟨_,time, by simpa only [id_eq, he] using lift⟩

end TeamSite

end BorderVNP
end Computability
end OAI
