import OAI.Computability.VPVNP.LiveHeaderProgramRun
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Uniqueness of the native header path

A successful call with the empty choice string executes no binary-choice
instruction. All surplus choices are therefore rejected. Repeating this
argument along the verified header stages proves exact path uniqueness,
including the position of the accepting call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- A successful empty-input call forces both its branch input and its report. -/
theorem execute_empty_forces {P : Program w C} {fuel : ℕ} {c : C} {m : Memory w} {r t : Report w}
    {bits : List Bool} (h : execute P fuel c m [] = some r) (hb : execute P fuel c m bits = some t) :
    bits = [] ∧ t = r := by
  have forced := execute_prefix_unique (suffix := bits) h hb
  exact ⟨forced.1,forced.2.symm⟩

/-- If the empty choice list succeeds at each call and the last call accepts,
this is the sole accepting path at that start state, memory and fuel. -/
theorem accepted_empty_unique {P : Program w C} {fuel n : ℕ} {s : Option (Word w)} {m : Memory w}
    {rs ts : List (Report w)} {bs : List (List Bool)}
    (h : runSegment P fuel s m (List.replicate n []) = some rs) (he : endState s rs = none)
    (hb : runSegment P fuel s m bs = some ts) (hbe : endState s ts = none) :
    bs = List.replicate n [] ∧ ts = rs := by
  induction n generalizing s m rs ts bs with
  | zero =>
    simp only [List.replicate_zero,runSegment,Option.some.injEq] at h
    subst rs
    change s = none at he
    subst s
    cases bs <;> simp_all [runSegment]
  | succ n ih =>
    rw [List.replicate_succ] at h ⊢
    cases s with
    | none => simp [runSegment] at h
    | some st =>
      cases bs with
      | nil => simp [runSegment] at hb; subst ts; contradiction
      | cons b bs =>
        simp only [runSegment] at h hb
        cases hfirst : execute P fuel (P.start st) m [] with
        | none => simp [hfirst] at h
        | some r =>
          cases hother : execute P fuel (P.start st) m b with
          | none => simp [hother] at hb
          | some t =>
            obtain ⟨rfl, rfl⟩ := execute_empty_forces hfirst hother
            simp only [hfirst, Option.map_eq_some_iff] at h hb
            obtain ⟨rest, hr, rfl⟩ := h
            obtain ⟨other, ho, rfl⟩ := hb
            obtain ⟨rfl, rfl⟩ := ih hr he ho hbe
            exact ⟨rfl, rfl⟩

end BurstRAM

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule

variable {w : ℕ}

/-- The physical header table admits exactly one accepted native path when
the scheduled source reports are produced by deterministic microcalls. -/
theorem accepted_path_unique (s : Sizes) (base cap : ℕ) (hfits : stages.length ≤ 2^w)
    {m : Memory w} {xs : List (StageTrace w)} (h : StageRuns s base (some (⟨0, by decide⟩ : StageId)) m xs)
    (hroom : ∀ x ∈ xs, x.fuel + 2*stages.length+5 ≤ cap) (htag : m (Fin.ofNat (2^w) base).val = 0)
    (hchoice : ∀ x ∈ xs, ∀ b ∈ x.paths, b = [])
    {bs : List (List Bool)} {out : List (Report w)}
    (hr : runSegment (program.instantiate w (publicData w s base)).program cap (some 0) m bs = some out)
    (ha : endState (some 0) out = none) :
    bs = xs.flatMap StageTrace.paths ∧ out = xs.flatMap (fun x => x.output (Fin.ofNat _ base)) := by
  obtain ⟨hrun,haccept,_,_⟩ := run_of_stages s base cap hfits h hroom (by rintro i ⟨⟩; exact htag)
  have heq : xs.flatMap StageTrace.paths = List.replicate (xs.flatMap StageTrace.paths).length [] := by
    apply List.eq_replicate_length.mpr
    intro b hb
    obtain ⟨x,hx,hb⟩ := List.mem_flatMap.mp hb
    exact hchoice x hx b hb
  rw [heq] at hrun
  obtain ⟨hbs, hout⟩ := accepted_empty_unique hrun haccept hr ha
  exact ⟨hbs.trans heq.symm, hout⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
