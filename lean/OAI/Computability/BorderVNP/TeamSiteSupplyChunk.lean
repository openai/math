import OAI.Computability.BorderVNP.TeamSiteSupplyDeterminism

/-! # Equivalence of supplied executions and guarded native chunks

The local native path conditions suffice to recover the actual supplied execution
when its finite spelling and terminal guard agree. A native private choice count
is bounded by its continuing transition count; an ordinary binary branch uses
one bit. Both bounds include paths of zero signed contribution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.SupplyRun

open VPVNP RAMTape BurstRAM TeamSiteEvents TeamSiteChoices TeamTapeHandoff

variable {Q Γ : Type} {w p r k a m g : ℕ} {P : TeamOpcode.Program p r k a}
  {pub : Fin k → Word w} {lib : Fin a → Macro Q Γ m g} {fuel : ℕ}
  {s last : TeamOpcode.State w p r} {c fin : Window w} {supply : Supply}
  {es : List (TeamRAM.Event w)} {verdict : Verdict}

/-- Source action and countdown admission imply exactly the physical callback exit. -/
theorem admits_action (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (M : TeamOpcode.Macros w a) (s : TeamOpcode.State w p r) (c : Window w) (act : TeamTranscript.Action (Word w))
    (action : (P.fetch pub M s).action = some act) (cap : act.extra ≤ c.cap.val) (fits : c.Fits act.extra) :
    exit P pub s c = .callback (TeamOpcode.prepare P pub s).1 := by
  have charged : decision c.block.val c.global.val (opcodeBurst P s).val = .execute := by
    rw [opcodeBurst_eq P pub M s act action]
    exact (decision_execute_iff ..).mpr fits
  rw [exit, result_action P pub M s c act action cap, TeamLocalClock.Loop.afterGuard,charged]

/-- The terminal check on the remaining supply follows all complete event spellings. -/
theorem Run.stopped (h : Run P pub lib fuel s c supply es last fin verdict) :
    Run P pub lib fuel last fin (drop supply (chunkBits es).length) [] last fin verdict := by
  induction h with
  | accept t => exact .accept t
  | handoff t => exact .handoff t
  | rejectGuard t => exact .rejectGuard t
  | rejectCallback t failed reason =>
    simpa only [chunkBits,List.flatMap_nil,List.length_nil,drop_zero] using
      Run.rejectCallback (lib := lib) (fuel := fuel) t failed reason
  | @cons s c sup z es last fin verdict _ _ _ _ ih =>
    rw [drop_drop] at ih
    simpa only [chunkBits,List.flatMap_cons,List.length_append,Next.bits,eventBits] using ih

/-- Replay a locally valid chunk on any supply spelling all its events, with the
verified terminal check on the unread suffix. No extra RAM word guess is introduced. -/
theorem of_chunk (h : Chunk (P.fetch pub (macros lib fuel)) s c es last fin)
    (hp : Prefix supply (chunkBits es))
    (endRun : Run P pub lib fuel last fin (drop supply (chunkBits es).length) [] last fin verdict) :
    Run P pub lib fuel s c supply es last fin verdict := by
  induction h generalizing supply with
  | nil => simpa only [chunkBits,List.flatMap_nil,List.length_nil,drop_zero] using endRun
  | @cons s c e next es last fin action advance fits cap _ ih =>
    let z : Next w p r := ⟨e,next⟩
    obtain ⟨he,ht⟩ := (prefix_append supply z.bits (chunkBits es)).mp hp
    refine .cons (admits_action P pub _ s c _ action cap fits) ((decode_iff ..).mpr ⟨action,advance,cap,he⟩)
      fits (ih ht ?_)
    rw [drop_drop]
    simpa only [chunkBits,List.flatMap_cons,List.length_append,Next.bits,eventBits,z] using endRun

/-- Exact source description of every stopped processor execution, including rejection. -/
theorem run_iff_chunk : Run P pub lib fuel s c supply es last fin verdict ↔
    Chunk (P.fetch pub (macros lib fuel)) s c es last fin ∧ Prefix supply (chunkBits es) ∧
      Run P pub lib fuel last fin (drop supply (chunkBits es).length) [] last fin verdict :=
  ⟨fun h => ⟨h.chunk,h.prefix,h.stopped⟩, fun ⟨h,hp,terminal⟩ => of_chunk h hp terminal⟩

private theorem choices_le_steps {d n q t bs out u} {T : TeamPrivateTape.Table Q d}
    (run : TeamPrivateFragment.Run T n q t bs out u) : bs.length ≤ n := by
  induction run with
  | stop => rfl
  | one _ _ ih => omega
  | two _ _ _ ih => exact Nat.succ_le_succ ih

/-- The complete native choice block has at most the number of continuing private
transitions, or the one bit of an ordinary branch. The final native halt uses no bit. -/
theorem advance_choices_bound (lib : Fin a → Macro Q Γ m g) (fuel : ℕ)
    (b : PrivateRAM.LogConfig w p r) (out : TeamOpcode.Exit p r a) (bs : List Bool)
    (vs : List (Word w)) {next sign}
    (advance : (out.action (macros lib fuel) b).advance bs vs = some (next,sign)) :
    bs.length ≤ max 1 (fuel-1) := by
  cases out with
  | call j addr len pc =>
    change (if vs.length = _ then ((lib j).eval fuel vs bs).map _ else none) = _ at advance
    split at advance
    · obtain ⟨sg,eval,_⟩ := Option.map_eq_some_iff.mp advance
      obtain ⟨n,lt,out,u,run,_⟩ := ((lib j).eval_iff ..).mp eval
      have := choices_le_steps run
      omega
    · contradiction
  | sign =>
    cases bs <;> first | exact Nat.zero_le _ | contradiction
  | native cb =>
    cases cb <;> rcases bs with _ | ⟨b, _ | ⟨c,bs⟩⟩ <;>
      first | exact Nat.zero_le _ | exact le_max_left _ _ | contradiction

/-- Every event in a guarded chunk obeys the native binary choice clock. -/
theorem chunk_choices (h : Chunk (P.fetch pub (macros lib fuel)) s c es last fin) :
    ∀ e ∈ es, e.choices.length ≤ max 1 (fuel-1) := by
  induction h with
  | nil => simp
  | cons action advance fits cap tail ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rw [← TeamOpcode.prepare_action] at advance
      exact advance_choices_bound lib fuel _ _ _ _ advance
    · exact ih e he

/-- A complete processor spelling cannot be a proper prefix of a different stopped
history from the same initial state and window. -/
theorem Run.prefix_free (first : Run P pub lib fuel s c supply es last fin verdict)
    {otherSupply es' last' fin' verdict'} (other : Run P pub lib fuel s c otherSupply es' last' fin' verdict')
    (initial : (chunkBits es).IsPrefix (chunkBits es')) :
    es = es' ∧ last = last' ∧ fin = fin' ∧ verdict = verdict' := by
  obtain ⟨tail,h⟩ := initial
  have hp := other.prefix
  rw [← h] at hp
  exact (first.on_prefix otherSupply ((prefix_append ..).mp hp).1).determined other

end TeamSite.SupplyRun

end BorderVNP
end Computability
end OAI
