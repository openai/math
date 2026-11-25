import OAI.Computability.BorderVNP.TeamSiteConsistencySchedules

/-!
# Independent physical end modes force the greedy schedule

Each site can decide only its own guarded exit. Its local certificate below
does not refer to any future instruction or even whether later blocks contain
events. A final accepted frame, together with the shared state and clock, forces
these independent exits to agree with the globally recovered accepting path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff TeamLocalClock

variable {w p r k a teams : ℕ}

/-- The semantic certificate of one actual physical endpoint, reading only the incident
input/output state and its own charged signed events. -/
def EndpointRow (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a)
    (H limit cap : Word w) (input : Frame w r) (es : List (TeamRAM.Event w)) (output : Frame w r) : Prop :=
  match input with
  | .accepted elapsed => es = [] ∧ elapsed ≤ limit ∧ output = .accepted elapsed
  | .live word regs elapsed =>
    elapsed ≤ limit ∧ ∃ (pc : Fin p) (z : TeamOpcode.State w p r) (fin : Window w),
      word = packed w pc.val ∧ Chunk (P.fetch pub lib) ⟨pc,regs⟩ (blockWindow H limit elapsed cap) es z fin ∧
      ((TeamLocalClock.Loop.result P pub z fin.block fin.global fin.elapsed fin.cap =
          (.accepted,fin.bank pub z) ∧ output = .accepted fin.elapsed) ∨
        (TeamLocalClock.Loop.result P pub z fin.block fin.global fin.elapsed fin.cap =
          (.handoff z.pc,fin.bank pub z) ∧ output = .live (packed w z.pc.val) z.reg fin.elapsed))

/-- Consecutive physical rows identify only their adjacent frames. -/
def EndpointRows (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a)
    (H limit cap : Word w) : Frame w r → List (List (TeamRAM.Event w)) → List (Frame w r) → Prop
  | _, [], fs => fs = []
  | _, _ :: _, [] => False
  | f, es::rows, next::fs => EndpointRow P pub lib H limit cap f es next ∧ EndpointRows P pub lib H limit cap next rows fs

/-- The charged schedule supplies a certificate for each independent physical exit. -/
theorem ChargedRows.endpoints {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {f : Frame w r}
    {rows : List (List (TeamRAM.Event w))} {fs : List (Frame w r)} (hs : ChargedRows P pub lib H limit cap f rows fs) :
    EndpointRows P pub lib H limit cap f rows fs := by
  induction rows generalizing f fs with
  | nil => exact hs
  | cons es rest ih =>
    cases fs with
    | nil => exact False.elim hs
    | cons out tail =>
      refine ⟨?_, ih hs.2⟩
      cases f with
      | accepted => exact hs.1
      | live word regs elapsed =>
        obtain ⟨ht,pc,z,fin,hw,run,exit,hframe⟩ := hs.1
        refine ⟨ht,pc,z,fin,hw,run,?_⟩
        cases hh : rest.flatten with
        | nil => exact Or.inl (by simpa [chunkExit, chunkMode, hh, Finish.frame] using And.intro exit hframe)
        | cons => exact Or.inr (by simpa [chunkExit, chunkMode, hh, Finish.frame] using And.intro exit hframe)

/-- Independent physical endpoints plus the final accepted-halt requirement recover the
charged schedule. In particular a live handoff cannot precede a completely empty suffix
of accepted processors: that would require the exact same PC to be both accepting and
denied by the clock guard. -/
theorem EndpointRows.charged {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {f : Frame w r}
    {rows : List (List (TeamRAM.Event w))} {fs : List (Frame w r)}
    (physical : EndpointRows P pub lib H limit cap f rows fs) (fits : p ≤ 2^w)
    (last : ∀ out, fs.getLast? = some out → out.halted = true) :
    ChargedRows P pub lib H limit cap f rows fs := by
  induction rows generalizing f fs with
  | nil => exact physical
  | cons es rest ih =>
    cases fs with
    | nil => exact False.elim physical
    | cons out tail =>
      have lastTail (x) (hx : tail.getLast? = some x) : x.halted = true := by
        apply last x
        cases tail with
        | nil => simp at hx
        | cons y ys => simpa only [List.getLast?_cons_cons] using hx
      have checked := ih physical.2 lastTail
      refine ⟨?_,checked⟩
      cases f with
      | accepted => exact physical.1
      | live word regs elapsed =>
        obtain ⟨ht,pc,z,fin,hw,run,hend⟩ := physical.1
        refine ⟨ht,pc,z,fin,hw,run,?_⟩
        rcases hend with ⟨exit,rfl⟩ | ⟨exit,rfl⟩
        · simp [chunkExit, chunkMode, checked.empty_halted, Finish.frame, exit]
        · have future : rest.flatten ≠ [] := by
            by_cases hr : rest = []
            · subst rest
              have ht0 : tail = [] := checked
              subst tail
              have := last (.live (packed w z.pc.val) z.reg fin.elapsed) rfl
              contradiction
            · intro flat
              have h := checked.local_live fits hr
              rw [flat] at h
              have halt := (accept_iff P pub lib z).mp h
              simp [TeamLocalClock.Loop.result, halt] at exit
          cases hh : rest.flatten with
          | nil => contradiction
          | cons => simp [chunkExit, chunkMode, Finish.frame, exit]

/-- A physically checked complete array starting at the prescribed registers recovers
the native locally accepting sequence without any assumed validity of a future path. -/
theorem EndpointRows.local_initial {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {s : TeamOpcode.State w p r}
    {rows : List (List (TeamRAM.Event w))} {fs : List (Frame w r)}
    (physical : EndpointRows P pub lib H limit cap (initial (packed w s.pc.val) s.reg) rows fs)
    (fits : p ≤ 2^w) (ne : rows ≠ []) (last : ∀ f, fs.getLast? = some f → f.halted = true) :
    TeamRAM.Local (P.fetch pub lib) s rows.flatten :=
  (physical.charged fits last).local_initial fits ne

/-- Unique finite array of genuine independent endpoints, with no lookahead and an
explicit final accepted frame at the cumulative charged time. -/
theorem existsUnique_endpointSchedule (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w) (fits : p ≤ 2^w) (hr : 0 < teams)
    (start : TeamOpcode.State w p r) (es : List (TeamRAM.Event w))
    (path : TeamRAM.Local (P.fetch pub lib) start es) (bound : ∀ e ∈ es, e.action.extra ≤ cap.val)
    (time : cost es ≤ limit.val) (capacity : cost es ≤ teams*(H.val-cap.val)) :
    ∃! rows : (Fin teams → List (TeamRAM.Event w)) × (Fin teams → Frame w r),
      (List.ofFn rows.1).flatten = es ∧
      EndpointRows P pub lib H limit cap (initial (packed w start.pc.val) start.reg) (List.ofFn rows.1) (List.ofFn rows.2) ∧
      (List.ofFn rows.2).getLast? = some (.accepted (packed w (cost es))) := by
  apply (existsUnique_congr (q := fun rows : (Fin teams → List (TeamRAM.Event w)) × (Fin teams → Frame w r) =>
    (List.ofFn rows.1).flatten = es ∧ ChargedRows P pub lib H limit cap (initial (packed w start.pc.val) start.reg)
      (List.ofFn rows.1) (List.ofFn rows.2) ∧ (List.ofFn rows.2).getLast? = some (.accepted (packed w (cost es)))) ?_).mpr
  · exact existsUnique_schedule P pub lib H limit cap fits hr start es path bound time capacity
  · intro rows
    refine ⟨fun ⟨flat,h,last⟩ => ⟨flat,h.charged fits ?_,last⟩,
      fun ⟨flat,h,last⟩ => ⟨flat,h.endpoints,last⟩⟩
    intro f hf
    rw [last, Option.some.injEq] at hf
    subst f; rfl

end TeamSite

end BorderVNP
end Computability
end OAI
