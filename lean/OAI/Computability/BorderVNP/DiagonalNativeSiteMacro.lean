import OAI.Computability.BorderVNP.RoutingISACompactDirectory
import OAI.Computability.BorderVNP.TeamSiteEvents

/-! # Installing the actual finite cell translator in the signed processor library

The same fixed control, alphabet, input tape, transition table and entry determine
both the site's literal macro and the compact word-RAM call. The clock remains a
runtime parameter. On every certified packed row the physical symbol machine halts
on all branches within that clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open VPVNP.BurstRAM CellMacro.Generator CellDispatch TeamPrivateTape

/-- Finite control of the private machine running the fixed compact cell generator. -/
abbrev SiteControl (gen : Fragment IO) := CellMacro.StackTape.Control (Label (frontend gen)) (tapeCount gen)

/-- The literal finite-alphabet, multitape private routine in the format consumed
by the signed universal processor. Its architecture does not depend on input length. -/
noncomputable def siteMacro (gen : Fragment IO) :
    TeamSite.Macro (SiteControl gen) (Option Bool) (tapeCount gen) PrivateCell.symbolWidth where
  alphabet := PrivateCell.alphabet
  digit := some
  inputTape := tapePorts gen (.inl .env)
  table := tapeTable gen
  start := entry gen

/-- In the signed evaluator only routine zero is fetched. All eight physical routine
slots may therefore contain the same fixed finite machine. -/
noncomputable def siteLibrary (gen : Fragment IO) :
    Fin 8 → TeamSite.Macro (SiteControl gen) (Option Bool) (tapeCount gen) PrivateCell.symbolWidth := fun _ => siteMacro gen

/-- The complete true burst input to the physical routine, for all word strings. -/
theorem siteMacro_initial {w : ℕ} (gen : Fragment IO) (words : List (Word w)) :
    (siteMacro gen).initial words = inputTracks gen words := rfl

/-- The native signed cell routine is exactly the literal site's evaluator at the
same fuel, including errors, rejected packets and unused choices. -/
theorem siteMacro_eval {w : ℕ} (gen : Fragment IO) (n : ℕ) (words : List (Word w)) (bits : List Bool) :
    (siteMacro gen).eval (nativeClock n) words bits = execute gen n words bits := rfl

/-- The genuine library read by the signed processor coincides at every instruction
slot with the installed compact macro evaluator. -/
theorem siteLibrary_installed {w : ℕ} (gen : Fragment IO) (n : ℕ) :
    TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n) =
      install gen n (TeamSiteEvents.macros (siteLibrary gen) (nativeClock n)) := by
  funext i
  by_cases h : i = 0
  · subst i
    rw [install,Function.update_self]
    rfl
  · rw [install,Function.update_of_ne h]

/-- Genuine packed private rows satisfy the physical site's all-branch stopping
predicate on the words fetched from that row, using its actual charged clock. -/
theorem siteMacro_bounded_row {w n : ℕ} (gen : Fragment IO) {f : Frame} {m : Memory w}
    {payload : ℕ → List Bool} {ops : ℕ → List CellMacro.Op} (rows : PackedRows f m gen n payload ops)
    {i : ℕ} (hi : i < f.count) (own : (m (f.address i)).val = f.team) :
    (siteMacro gen).bounded (nativeClock n) (TeamRAM.previous m (f.burst m i)) := by
  obtain ⟨t,r,time⟩ := rows.generate i hi own
  have stopped := (packed_value gen n rows.width (payload i) (ops i) r time).1
  rw [rows.words i hi own]
  exact (TeamPrivateValue.track_stops_iff _ _ _ _ _).mp stopped

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
