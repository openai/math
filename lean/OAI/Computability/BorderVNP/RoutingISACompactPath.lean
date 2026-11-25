import OAI.Computability.BorderVNP.RoutingISACompactNative

/-!
# Replayable paths of the compact directory machine

An owner supplies the actual words of its directory burst. A result for those
words and a fixed choice string identifies one concrete path of the private
two-tape compiler, including its native time and final tapes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open CellMacro.Generator CellDispatch TeamPrivateTape VPVNP.BurstRAM

variable {w : ℕ}

/-- A path of the private compiler on the tape dimensions of the installed generator. -/
abbrev CompilerPath (generate : Fragment IO) (w : ℕ) :=
  TeamPrivateClock.Path (CellMacro.StackTape.Control (Label (frontend generate)) (tapeCount generate))
    (Option Bool) (tapeCount generate) PrivateCell.symbolWidth w

/-- Exact machine, input and output fields required of a clocked path on a compact burst. -/
structure PathSpec (generate : Fragment IO) (n : ℕ) (words : List (Word w))
    (bits : List Bool) (s : TeamRAM.Sign) (p : CompilerPath generate w) : Prop where
  /-- The private tape symbols have the fixed blank/bit representation. -/
  alphabet : p.alphabet = PrivateCell.alphabet
  /-- Input words are loaded as binary digits. -/
  digit : p.digit = some
  /-- The decoder starts with the burst in the environment stack. -/
  inputTape : p.inputTape = tapePorts generate (.inl .env)
  /-- The fixed program contains the decoder, generator and signed evaluator. -/
  table : p.table = tapeTable generate
  /-- The first instruction enters the decoder. -/
  start : p.start = entry generate
  /-- The path is loaded from the live burst. -/
  inputWords : p.words = words
  /-- The run consumes the complete private choice string. -/
  choices : p.choices = bits
  /-- Rejecting halts have sign zero. -/
  sign : TeamPrivateCall.sign p.sign = s
  /-- One native clock tick remains for the final halt check. -/
  within : p.time < nativeClock n

private theorem spec_unique {generate : Fragment IO} {n words bits s}
    {a b : CompilerPath generate w} (ha : PathSpec generate n words bits s a)
    (hb : PathSpec generate n words bits s b) : a = b := by
  cases a with
  | mk aa ad ai atb ast aw an ab az au ar =>
    cases b with
    | mk ba bd bi btb bst bw bn bb bz bu br =>
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,_,_⟩ := ha
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,_,_⟩ := hb
      obtain ⟨rfl,rfl,rfl⟩ := CellDispatch.unique_run ar br
      rfl

/-- The machine returns a sign exactly when there is a unique replayable physical
path on the supplied burst, within the installed native clock. -/
theorem execute_iff_unique_path (generate : Fragment IO) (n : ℕ) (words : List (Word w))
    (bits : List Bool) (s : TeamRAM.Sign) :
    execute generate n words bits = some s ↔
      ∃! p : CompilerPath generate w, PathSpec generate n words bits s p := by
  constructor
  · intro result
    unfold execute at result
    cases ev : TeamPrivateCall.evaluate (trackTable PrivateCell.alphabet (tapeTable generate))
        (nativeClock n) (entry generate) (inputTracks generate words) bits with
    | none => simp [ev] at result
    | some o =>
      obtain ⟨z, u⟩ := o
      have hs : TeamPrivateCall.sign z = s := by simpa only [ev, Option.map_some, Option.some.injEq] using result
      obtain ⟨t, ht, r⟩ := TeamPrivateCall.evaluate_spec ev
      let p : CompilerPath generate w :=
        ⟨PrivateCell.alphabet, some, tapePorts generate (.inl .env), tapeTable generate, entry generate,
          words, t, bits, z, u, r⟩
      have h : PathSpec generate n words bits s p := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hs,ht⟩
      exact ⟨p,h,fun q hq => spec_unique hq h⟩
  · rintro ⟨p,h,_⟩
    have run := p.run
    rw [h.alphabet, h.digit, h.inputTape, h.table, h.start, h.inputWords, h.choices] at run
    have ev := TeamPrivateCall.evaluate_of_run run h.within
    change TeamPrivateCall.evaluate _ _ _ (inputTracks generate words) bits = some _ at ev
    simp only [execute, ev, Option.map_some, h.sign]

/-- Admission of an owned directory result requires its address interval to fit and
determines a unique clocked path on the actual words at that address. -/
theorem valid_owner_iff_unique_path (generate : Fragment IO) (n : ℕ) (f : Frame)
    (m : Memory w) (routines : TeamOpcode.Macros w 8) (i : ℕ)
    (owner : (m (f.address i)).val = f.team) (o : Outcome) :
    f.Valid m (install generate n routines) i (some o) ↔
      (m (f.address i + 1)).val + (m (f.address i + 2)).val ≤ 2^w ∧
        ∃! p : CompilerPath generate w,
          PathSpec generate n (TeamRAM.previous m (f.burst m i)) o.1 o.2 p := by
  simp [Frame.Valid, owner, install, execute_iff_unique_path]

/-- Compiling a fitting burst uses at most a machine-dependent multiple of the
published twenty-fifth-power bound in elementary stack instructions. -/
theorem PathSpec.cost_le {generate : Fragment IO} {n words bits s}
    {p : CompilerPath generate w} (h : PathSpec generate n words bits s p)
    (hn : 1 ≤ n) (hw : w ≤ n) (hwords : words.length ≤ TeamScales.width n (1/2)) :
    p.cost ≤ TeamPrivateClock.coefficient (tapeCount generate) PrivateCell.symbolWidth * n^25 :=
  p.cost_le hn hw (h.inputWords ▸ hwords) (time_le_of_lt_nativeClock h.within)

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
