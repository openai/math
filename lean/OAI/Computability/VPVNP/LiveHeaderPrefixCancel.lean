import OAI.Computability.VPVNP.LiveHeaderUnique

/-!
# Deterministic prefixes of accepting RAM paths

An empty-choice prefix ending at a persistent state fixes its reports and
memory effects in any accepting execution from the same initial state.
The remaining branch inputs execute from the resulting physical memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

theorem accepted_suffix_of_empty_prefix {P : Program w C} {fuel n : ℕ}
    {s : Option (Word w)} {st : Word w} {m : Memory w} {rs outs : List (Report w)}
    {bs : List (List Bool)}
    (hr : runSegment P fuel s m (List.replicate n []) = some rs) (he : endState s rs = some st)
    (h : runSegment P fuel s m bs = some outs) (halt : endState s outs = none) :
    ∃ btail rtail, bs = List.replicate n [] ++ btail ∧ outs = rs ++ rtail ∧
      runSegment P fuel (some st) (after m (eventLog rs)) btail = some rtail ∧
      endState (some st) rtail = none := by
  induction n generalizing s m rs bs outs with
  | zero =>
    simp only [List.replicate_zero,runSegment,Option.some.injEq] at hr
    subst rs
    change s = some st at he
    subst s
    exact ⟨bs,outs,rfl,rfl,h,halt⟩
  | succ n ih =>
    rw [List.replicate_succ] at hr ⊢
    cases s with
    | none => simp [runSegment] at hr
    | some start =>
      cases bs with
      | nil => simp [runSegment] at h; subst outs; contradiction
      | cons b bs =>
        simp only [runSegment] at hr h
        cases hfirst : execute P fuel (P.start start) m [] with
        | none => simp [hfirst] at hr
        | some r =>
          cases hother : execute P fuel (P.start start) m b with
          | none => simp [hother] at h
          | some t =>
            obtain ⟨rfl,rfl⟩ := execute_empty_forces hfirst hother
            simp only [hfirst,Option.map_eq_some_iff] at hr h
            obtain ⟨rest,hrest,rfl⟩ := hr
            obtain ⟨other,hrun,rfl⟩ := h
            obtain ⟨btail,rtail,rfl,rfl,htail,hstop⟩ := ih hrest he hrun halt
            refine ⟨btail,rtail,rfl,rfl,?_,hstop⟩
            simpa only [eventLog,List.flatMap_cons,after,List.foldl_append] using htail

/-- A rejected call immediately after such a prefix excludes every
accepting branch path, even if that path uses different choice lists. -/
theorem no_accept_after_empty_prefix {P : Program w C} {fuel n : ℕ}
    {s : Option (Word w)} {st : Word w} {m : Memory w} {rs : List (Report w)}
    (hr : runSegment P fuel s m (List.replicate n []) = some rs) (he : endState s rs = some st)
    (reject : ∀ b, execute P fuel (P.start st) (after m (eventLog rs)) b = none) :
    ¬∃ bs outs, runSegment P fuel s m bs = some outs ∧ endState s outs = none := by
  rintro ⟨bs,outs,h,halt⟩
  obtain ⟨btail,rtail,_,_,hrest,hend⟩ := accepted_suffix_of_empty_prefix hr he h halt
  cases btail with
  | nil => simp [runSegment] at hrest; subst rtail; contradiction
  | cons b rest => simp [runSegment,reject b] at hrest

end BurstRAM

end VPVNP
end Computability
end OAI
