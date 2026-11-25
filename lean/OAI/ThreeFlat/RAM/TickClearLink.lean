import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.TickClearFrame
import OAI.ThreeFlat.RAM.NativeRelocate

namespace OAI
/-! # A concrete native ROM with an initialized register frame -/

namespace ThreeFlat.RAM.TickClearFrame

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink

variable {w n p r k P R K : ℕ}

/-- The last point is the continuation, so the clear block consumes only `n` labels. -/
def locations (pc : Fin n ↪ Fin P) (exit : Fin P) : Fin (n+1) → Fin P :=
  Fin.lastCases exit pc

@[simp] theorem locations_last (pc : Fin n ↪ Fin P) (exit : Fin P) :
    locations pc exit (Fin.last n) = exit := by simp [locations]

@[simp] theorem locations_castSucc (pc : Fin n ↪ Fin P) (exit : Fin P) (i : Fin n) :
    locations pc exit i.castSucc = pc i := by simp [locations]

@[simp] theorem locations_zero [NeZero n] (pc : Fin n ↪ Fin P) (exit : Fin P) :
    locations pc exit 0 = pc 0 := by
  rw [show (0 : Fin (n+1)) = (0 : Fin n).castSucc from Fin.ext (by simp), locations_castSucc]

/-- The scratch-frame prologue as a composable table with no public operands of its own. -/
def block (w n k : ℕ) [NeZero n] : Block w n n k where
  first := 0
  emit pc reg _ exit := row (locations pc exit) reg

theorem block_rows [NeZero n] (M : Machine w P R K) (pc : Fin n ↪ Fin P)
    (reg : Fin n ↪ Fin R) (pub : Fin k → Fin K) (exit : Fin P)
    (installed : (block w n k).Installed M pc reg pub exit) (i : Fin n) :
    M.code (locations pc exit i.castSucc) = row (locations pc exit) reg i := by
  rw [locations_castSucc]
  exact installed i

/-- Prefix an actual native ROM with zero writes to every one of its registers. -/
def prepend [NeZero n] (native : Machine w p n k) : Machine w (n+p) n k :=
  close (block w n k) native.entry
    (fun pc i => NativeRelocate.relocate pc (Function.Embedding.refl _) id (native.code i))
    native.publicData

private theorem installed_prepend [NeZero n] (native : Machine w p n k) :
    (block w n k).Installed (prepend native) (Fin.castAddEmb p) (Function.Embedding.refl _) id
      (Fin.natAdd n native.entry) :=
  close_installed (block w n k) native.entry _ native.publicData

/-- The assembled prologue leaves the register bank zero at the relocated entry. -/
theorem advance_prepend [NeZero n] (native : Machine w p n k) (c : Config w (n+p) n)
    (mem : Memory w) (start : c.pc = (prepend native).entry) :
    advance (prepend native).program n c mem =
      some (cleared (Function.Embedding.refl _) (Fin.natAdd n native.entry) c,mem) := by
  let pc := (Fin.castAddEmb p : Fin n ↪ Fin (n+p))
  let exit := Fin.natAdd n native.entry
  have atStart : c.pc = locations pc exit 0 := by simpa [pc,prepend,close,block] using start
  simpa [exit] using advance_clear (prepend native) (locations pc exit) (Function.Embedding.refl _)
    (block_rows _ pc _ id exit (installed_prepend native)) c mem atStart

/-- With an external-memory callee, the concrete prefixed ROM realizes its
weighted value from arbitrary initial register values at the cost of `n` steps. -/
theorem mass_prepend {F : Type*} [Semiring F] [NeZero n] (code : FieldCode F w)
    (native : Machine w p n k) (allowed : ∀ i, NativeRelocate.ExternalOnly (native.code i))
    (c : Config w (n+p) n) (mem : Memory w) (start : c.pc = (prepend native).entry)
    (fuel : ℕ) :
    mass code (prepend native).program (fuel+n) c mem = value code native fuel c.persistent mem := by
  rw [mass_of_advance code _ (advance_prepend native c mem start) fuel]
  apply NativeRelocate.mass_eq_value (Fin.natAddEmb n) (Function.Embedding.refl _)
    id native (prepend native) allowed
  · intro i
    exact close_tail _ _ _ _ i
  · intro i
    rfl
  · rfl
  · exact cleared_target _ _ c

end ThreeFlat.RAM.TickClearFrame

end OAI
