import OAI.Computability.BorderVNP.TeamPrivateMeterCallBanks

/-! # Complete fixed private code with per-call initialization of the native timer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateMeterCall

open VPVNP.RAMTape TeamPrivateTape
variable {Q Γ : Type} {m g : ℕ}

/-- Finite private control remembers the first burst digit during the independent clock reset. -/
inductive Control (Q : Type) (m g : ℕ) where
  | load (q : TeamPrivateInput.State g)
  | reset (inputHead : Option Bool) (q : TeamPrivateMeterReset.State g)
  | run (q : TeamPrivateFragment.Label Q ((m+1)*g))
  | result (out : Option Bool)

noncomputable instance [Fintype Q] : Fintype (Control Q m g) := derive_fintype% _

private def dataLabel : TeamPrivateInput.State g → Control Q m g
  | .done h => .reset h (TeamPrivateMeterReset.entry g)
  | q => .load q

private def resetLabel (M : TeamSite.Macro Q Γ m g) (mark : Γ) (data : Option Bool) :
    TeamPrivateMeterReset.State g → Control Q m g
  | .inr (.done meter) => .run (.inl (.ready M.start (timedHeads M mark data meter)))
  | q => .reset data q

/-- Fixed program loading both tapes and clearing all private tape stacks at the signed return. -/
noncomputable def code (M : TeamSite.Macro Q Γ m g) (mark : Γ) : StackCode (Port m g) (Control Q m g)
  | .load q => (TeamPrivateInput.code (fun b => M.alphabet.bits (M.digit b)) q).rename
      (dataPorts M.inputTape) dataLabel
  | .reset data q => (TeamPrivateMeterReset.code (M.alphabet.bits mark) q).rename
      meterPorts (resetLabel M mark data)
  | .run q => TeamPrivateFragment.rows
      (trackTable M.alphabet (TeamPrivateTimeout.table M.alphabet.blank mark M.table))
      trackPort Control.run Control.result q
  | .result out => .halt out.isSome

/-- Exact elementary steps of both deterministic loaders, the timed native simulation, and cleanup. -/
def steps {m g : ℕ} (bs : List Bool) (N n : ℕ) (u : Fin ((m+1)*g) → Track) :=
  TeamPrivateInput.steps g bs + TeamPrivateMeterReset.steps g N +
    (n * (2*((m+1)*g)+2) + 1 + TeamPrivateCleanup.steps (bank u))

/-- A physical call replays the exact native choices and returns with its reusable template intact. -/
theorem run_input (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ)
    {n choices out u}
    (native : TeamPrivateFragment.Run (trackTable M.alphabet (TeamPrivateTimeout.table M.alphabet.blank mark M.table))
      n M.start (timedInput M mark bs N) choices out u) (suffix : List Bool) :
    StackRuns (TeamPrivateFragment.replay (code M mark)) (steps bs N n u)
      (.load .start, choices ++ suffix) (initial bs N) (.result out, suffix) (finished N) := by
  have loadRun := (TeamPrivateInput.runs (fun b => M.alphabet.bits (M.digit b)) bs).lift
    (dataPorts M.inputTape) (dataPorts_injective M.inputTape) dataLabel (initial bs N)
    (target := code M mark) (by
      intro q h
      cases q <;> first | rfl | simp [TeamPrivateInput.code] at h)
  have before (p : TeamPrivateInput.Port g) : initial bs N (dataPorts M.inputTape p) =
      TeamPrivateInput.store bs [] (fun _ => []) p := by cases p <;> rfl
  rw [installStacks_eq (dataPorts_injective M.inputTape) _ _ before,install_data] at loadRun
  have resetRun := (TeamPrivateMeterReset.runs (M.alphabet.bits mark) N).lift
    meterPorts meterPorts_injective (resetLabel M mark bs.head?) (loaded M bs N)
    (target := code M mark) (by
      intro q h
      rcases q with (q | q)
      · rfl
      · cases q <;> first | rfl | simp [TeamPrivateMeterReset.code,TeamPrivateInput.code,StackOp.rename] at h)
  rw [installStacks_eq meterPorts_injective _ _ (loaded_meter M bs N),install_meter] at resetRun
  simp only [resetLabel,timedHeads_eq] at resetRun
  have run := TeamPrivateFragment.run_linked native trackPort trackPort_injective Control.run Control.result
    (code M mark) (fun _ => rfl) (clocked M mark bs N) suffix
  rw [installStacks_eq trackPort_injective (clocked M mark bs N) (bank (timedInput M mark bs N))
    (fun _ => rfl),install_empty] at run
  exact (TeamPrivateFragment.replay_segment (loadRun.trans resetRun) (choices ++ suffix)).trans run

/-- Embed the entire clocked call at named labels of the physical site. Other caller stacks retain
their contents, and the entry's private choice suffix is returned without consuming extra bits. -/
theorem run_wired {reg k : ℕ} {R : Type} (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ)
    {n choices out u}
    (native : TeamPrivateFragment.Run (trackTable M.alphabet (TeamPrivateTimeout.table M.alphabet.blank mark M.table))
      n M.start (timedInput M mark bs N) choices out u) (suffix : List Bool)
    (target : StackCode (TeamClocked.Port (TeamSite.Layout.Port reg k ((m+1)*g))) R)
    (label : Control Q m g → R) (base : Stacks (TeamClocked.Port (TeamSite.Layout.Port reg k ((m+1)*g))))
    (ready : ∀ p, base (wired reg k m g p) = initial bs N p)
    (rows : ∀ q, (code M mark q).returns = false → target (label q) =
      (code M mark q).rename (wired reg k m g) label) :
    StackRuns (TeamPrivateFragment.replay target) (steps bs N n u)
      (label (.load .start), choices ++ suffix) base (label (.result out), suffix)
      (installStacks (wired reg k m g) base (finished N)) := by
  have lift := TeamLink.replay_lift (run_input M mark bs N native suffix) target (wired reg k m g)
    (wired_injective reg k m g) label base rows
  rwa [installStacks_eq (wired_injective reg k m g) _ _ ready] at lift

end TeamPrivateMeterCall

end BorderVNP
end Computability
end OAI
