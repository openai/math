import OAI.Computability.VPVNP.LiveHeaderUnique

/-! # Memory frames under arbitrary instruction caps and public cursor guards -/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

private theorem Guessed.add_fuel {P : Program w C} {f : ℕ} {c : C} {es : List (Event w)} {out : Option (Word w)}
    (hg : Guessed P f c es out) (pad : ℕ) : Guessed P (f+pad) c es out := by
  induction hg with
  | done hs => simpa [Nat.succ_add] using Guessed.done (f := _+pad) hs
  | step hs _ ih => simpa [Nat.succ_add] using Guessed.step hs ih
  | branch hs _ ih => simpa [Nat.succ_add] using Guessed.branch hs ih
  | read hs _ ih => simpa [Nat.succ_add] using Guessed.read hs ih
  | write hs _ ih => simpa [Nat.succ_add] using Guessed.write hs ih

/-- Extra instruction fuel preserves a successful native path and its report. -/
theorem execute_extend {P : Program w C} {f : ℕ} {c : C} {m : Memory w} {bs : List Bool} {r : Report w}
    (hr : execute P f c m bs = some r) (pad : ℕ) : execute P (f+pad) c m bs = some r := by
  obtain ⟨hg,hm,hbits⟩ := execute_spec hr
  apply execute_iff.mpr
  refine ⟨?_,hm,hbits⟩
  exact hg.add_fuel pad

theorem execute_empty_forces_anyFuel {P : Program w C} {f g : ℕ} {c : C} {m : Memory w} {bits : List Bool}
    {r t : Report w} (h : execute P f c m [] = some r) (ht : execute P g c m bits = some t) :
    bits = [] ∧ t = r := by
  have forced := execute_prefix_unique (suffix := bits) h ht
  exact ⟨forced.1,forced.2.symm⟩

end BurstRAM

namespace LiveHeaderBounded

open BurstRAM BurstRAM.PrivateRAM

variable {w p r k : ℕ}

/-- For any successful call of the guarded table it suffices to check
the frame on successful source calls whose cursor is below the capacity. -/
theorem frame_any (T : Template p r k) (pub : Fin k → Word w) (bound : Word w) (fuel : ℕ) (st : Word w)
    (m : Memory w) (bits : List Bool) (rep : Report w)
    (run : execute (machine T pub bound).program fuel ((machine T pub bound).program.start st) m bits = some rep)
    (a : ℕ) (frame : ∀ f r, st < bound →
      execute (T.instantiate w pub).program f ((T.instantiate w pub).program.start st) m bits = some r →
      after m r.events a = m a) : after m rep.events a = m a := by
  by_cases hlt : st < bound
  · have h := execute_extend run 3
    rw [execute_active T pub bound fuel st hlt,Option.map_eq_some_iff] at h
    obtain ⟨r,hr,rfl⟩ := h
    exact frame fuel r hlt hr
  · have he := execute_closed T pub bound 0 st (le_of_not_gt hlt) m []
    dsimp only [ite_true] at he
    obtain ⟨_,rfl⟩ := execute_empty_forces_anyFuel he run
    rfl

end LiveHeaderBounded

end VPVNP
end Computability
end OAI
