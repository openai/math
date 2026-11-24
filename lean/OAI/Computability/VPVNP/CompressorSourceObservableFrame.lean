import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Recovering a write footprint from native replay and an external frame

Once a native schedule reads only its data region, the same reports execute
on every memory agreeing there. A write to an outside cell would force its
final value independently of its initial value. Thus a frame theorem valid
for all such initial memories excludes even temporary writes to the cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceTransport

open BurstRAM

variable {w : ℕ} {J : Type*} {src : J → Memory w → List (Report w) → Prop}
variable {data : ℕ → Prop}

private theorem write_forces {a v : Word w} (es : List (Event w)) (hit : Event.write a v ∈ es)
    (m m' : Memory w) : after m es a.val = after m' es a.val := by
  have point {q q' : Memory w} (h : q a.val = q' a.val) (tail : List (Event w)) :
      after q tail a.val = after q' tail a.val := by
    induction tail generalizing q q' with
    | nil => exact h
    | cons e es ih =>
      apply ih
      cases e <;> simp only [update,writeMemory]
      all_goals first | exact h | split <;> first | rfl | exact h
  induction es generalizing m m' with
  | nil => simp at hit
  | cons e es ih =>
    rcases List.mem_cons.mp hit with he|rest
    · subst e
      exact point (q := update m (.write a v)) (q' := update m' (.write a v)) (by simp [update,writeMemory]) es
    · exact ih rest (update m e) (update m' e)

/-- If the same log preserves every value in the complement, a native
instruction cannot have written there at any point of that log. -/
theorem writes_of_replay [Nontrivial (Word w)] (m : Memory w) (es : List (Event w))
    (frame : ∀ m' : Memory w, Agree data m m' → ∀ x, ¬ data x → after m' es x = m' x) :
    Writes data es := by
  intro a v hit
  by_contra ha
  obtain ⟨u,hu⟩ := exists_ne (m a.val)
  let m' := writeMemory m a u
  have agree : Agree data m m' := fun x hx => by
    change m x = if x = a.val then u else m x
    have hn : x ≠ a.val := fun he => ha (he ▸ hx)
    simp [hn]
  have orig := frame m (fun _ _ => rfl) a.val ha
  have alt := frame m' agree a.val ha
  have forced := write_forces es hit m' m
  rw [alt,orig] at forced
  exact hu (by simpa [m',writeMemory] using forced)

theorem walk_deterministic (det : ∀ j m a b, src j m a → src j m b → a = b)
    {js : List J} {m : Memory w} {as bs : List (Report w)}
    (h : SourceWalk src js m as) (g : SourceWalk src js m bs) : as = bs := by
  induction h generalizing bs with
  | done => cases g; rfl
  | @next j js m a b ha hb ih =>
    cases g with
    | @next _ _ _ a' b' ha' hb' =>
      obtain rfl := det j m a a' ha ha'
      exact congrArg (a++·) (ih hb')

/-- A heterogeneous list of actual source calls replays under agreement on
all the addresses read by its complete event log. -/
theorem replay_walk
    (transport : ∀ j m m' rs, Agree data m m' → Reads data (eventLog rs) → src j m rs → src j m' rs)
    {js : List J} {m m' : Memory w} {rs : List (Report w)}
    (h : SourceWalk src js m rs) (agree : Agree data m m') (rd : Reads data (eventLog rs)) :
    SourceWalk src js m' rs := by
  induction h generalizing m' with
  | done => exact .done _
  | @next j js m a b ha hb ih =>
    simp only [eventLog,List.flatMap_append] at rd
    exact .next (transport j m m' a agree (fun x v hx => rd x v (List.mem_append_left _ hx)) ha)
      (ih (agree.after _) (fun x v hx => rd x v (List.mem_append_right _ hx)))

end CompressorRecords.SourceTransport

end VPVNP
end Computability
end OAI
