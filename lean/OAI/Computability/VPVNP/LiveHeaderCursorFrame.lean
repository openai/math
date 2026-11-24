import OAI.Computability.VPVNP.LiveStageSegments
import OAI.Computability.VPVNP.LiveHeaderBoundedRun

/-!
# Frames of continuing live-header scan calls

A scan increments its cursor and preserves the reserved stage word at each
step. The extra ticks of the bound check and its closing call preserve this
property for the reported native stage.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveHeaderBounded
open scoped Fin.CommRing

variable {w : ℕ} {C : Type*}

theorem runSegment_cursor_frame (P : Program w C) (fuel bound : ℕ) (addr : Word w)
    (step : ∀ i < bound, ∀ mem rep, execute P fuel (P.start (i : Word w)) mem [] = some rep →
      rep.result = some ((i+1 : ℕ) : Word w) ∧ after mem rep.events addr.val = mem addr.val)
    (start n : ℕ) (m : Memory w) (rs : List (Report w)) (hle : start+n ≤ bound)
    (hrun : runSegment P fuel (some (start : Word w)) m (List.replicate n []) = some rs) :
    PreservesTagOnReturns addr m rs := by
  induction n generalizing start m rs with
  | zero =>
    simp [runSegment] at hrun
    subst rs
    trivial
  | succ n ih =>
    rw [List.replicate_succ,runSegment] at hrun
    cases he : execute P fuel (P.start (start : Word w)) m [] with
    | none => simp [he] at hrun
    | some rep =>
      simp only [he, Option.map_eq_some_iff] at hrun
      obtain ⟨rest, hr, rfl⟩ := hrun
      obtain ⟨hnext, hframe⟩ := step start (by omega) m rep he
      rw [hnext] at hr
      exact ⟨fun _ => hframe, ih (start+1) _ rest (by omega) hr⟩

theorem guarded_frame {addr : Word w} {m : Memory w} {rs : List (Report w)}
    (h : PreservesTagOnReturns addr m rs) : PreservesTagOnReturns addr m (rs.map activeReport ++ [closedReport w]) := by
  apply PreservesTagOnReturns.append
  · induction rs generalizing m with
    | nil => trivial
    | cons r rs ih => exact ⟨h.1, ih h.2⟩
  · exact PreservesTagOnReturns.singleton_accept _ _ _ rfl

end LiveHeader

end VPVNP
end Computability
end OAI
