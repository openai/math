import OAI.Computability.BorderVNP.RoutingISACompactFrame
import OAI.Computability.BorderVNP.RoutingISACompactMachine
import OAI.Computability.BorderVNP.RoutingISACallPrivate

/-!
# The private multitape call on compact cell arguments

An installed routine receives precisely the fixed-width bits read by the burst.
Its finite table decodes their framing, runs the sparse generator, reverses its
output and executes the signed cell checks. The length parameter supplies the
published private clock. A malformed or overlong call contributes no extra path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open CellMacro.Generator VPVNP.BurstRAM TeamPrivateTape

/-- The real preparation machine uses the framed-input decoder before the fixed generator. -/
def frontend (generate : Fragment IO) : Fragment IO :=
  prepare (CompactFrame.decode IO.env IO.row) generate

/-- Total stack-clock allowance before simulating with two native transitions per step. -/
def stackClock (n : ℕ) := n^25 / 2

/-- Inclusive private transition limit, with a final fuel tick for observing halt. -/
def nativeClock (n : ℕ) := n^25+1

/-- Successful replay performs at most the paper's stated number of transitions. -/
theorem time_le_of_lt_nativeClock {n t : ℕ} (h : t < nativeClock n) : t ≤ n^25 := Nat.le_of_lt_succ h

/-- The fixed set of tape heads, including generator work stacks. -/
abbrev tapeCount (generate : Fragment IO) := Fintype.card (IO ⊕ (frontend generate).Scratch)

/-- Physical tape numbering of the finite private implementation. -/
noncomputable def tapePorts (generate : Fragment IO) := Fintype.equivFin (IO ⊕ (frontend generate).Scratch)

/-- Finite symbol-level tape table for the complete compact-input machine. -/
noncomputable def tapeTable (generate : Fragment IO) :=
  CellMacro.StackTape.table (tapePorts generate) (program (frontend generate)) (negative (frontend generate))

/-- Initial control of the compiled private routine. -/
def entry (generate : Fragment IO) : CellMacro.StackTape.Control (Label (frontend generate)) (tapeCount generate) :=
  .ready (.inl (frontend generate).body.body.entry)

/-- The runtime bit planes receive the actual concatenation of the burst's little-endian words. -/
noncomputable def inputTracks {w : ℕ} (generate : Fragment IO) (words : List (Word w)) :=
  tracks CellDispatch.PrivateCell.alphabet (input none some (tapePorts generate (.inl .env))
    (TeamPrivateCall.inputBits words))

/-- Clocked replay on the actual private guesses, on the selected signed tape table. -/
noncomputable def execute {w : ℕ} (generate : Fragment IO) (n : ℕ) (words : List (Word w))
    (bits : List Bool) : Option TeamRAM.Sign :=
  (TeamPrivateCall.evaluate (trackTable CellDispatch.PrivateCell.alphabet (tapeTable generate))
    (nativeClock n) (entry generate) (inputTracks generate words) bits).map
    (fun p => TeamPrivateCall.sign p.1)

/-- Install the compact, clocked private cell machine at the directory dispatch entry point. -/
noncomputable def install {w : ℕ} (generate : Fragment IO) (n : ℕ)
    (routines : TeamOpcode.Macros w 8) : TeamOpcode.Macros w 8 :=
  Function.update routines 0 (execute generate n)

private theorem extend_stops {Q : Type} {k : ℕ} (P : Table Q k)
    {fuel more : ℕ} {q : Q} {t : Fin k → Track} (h : TeamPrivateValue.Stops P fuel q t)
    (le : fuel ≤ more) : TeamPrivateValue.Stops P more q t ∧ paths P more q t = paths P fuel q t := by
  induction fuel generalizing more q t with
  | zero => exact h.elim
  | succ f ih =>
    cases more with
    | zero => omega
    | succ g =>
      have fg : f ≤ g := Nat.le_of_succ_le_succ le
      cases op : P q (heads t) with
      | halt a b => simp [TeamPrivateValue.Stops,paths,op]
      | one c =>
        have h' := ih (q := c.next) (t := c.apply t) (by simpa only [TeamPrivateValue.Stops,op] using h) fg
        simpa only [TeamPrivateValue.Stops,paths,op] using h'
      | two l r =>
        obtain ⟨hl,hr⟩ : TeamPrivateValue.Stops P f l.next (l.apply t) ∧ TeamPrivateValue.Stops P f r.next (r.apply t) :=
          by simpa only [TeamPrivateValue.Stops,op] using h
        obtain ⟨sl,vl⟩ := ih hl fg
        obtain ⟨sr,vr⟩ := ih hr fg
        simp only [TeamPrivateValue.Stops,paths,op,sl,sr,vl,vr,and_self]

/-- Native signed evaluation of a packed sparse descriptor. The decoder's budget
depends only on the words read from the burst. Generator work, the private reverse
sweep and the signed instruction stream are charged against the native clock. -/
theorem packed_value {w : ℕ} (generate : Fragment IO) (n : ℕ) (hw : 0 < w)
    (payload : List Bool) (ops : List CellMacro.Op) {genCost : ℕ}
    (expand : generate.Runs genCost (io payload [] []) (io [] [] (CellMacro.stream ops).reverse))
    (time : 2 * (3*((CompactFrame.pack w payload).length*w) + genCost +
      (2*(CellMacro.stream ops).length+1) + CellMacro.budget ops) ≤ n^25) :
    let table := trackTable CellDispatch.PrivateCell.alphabet (tapeTable generate)
    let startTracks := inputTracks generate (CompactFrame.pack w payload)
    TeamPrivateValue.Stops table (nativeClock n) (entry generate) startTracks ∧
      paths table (nativeClock n) (entry generate) startTracks = CellMacro.value ops ⟨true,false⟩ [] := by
  let words := CompactFrame.pack w payload
  let wire := TeamPrivateCall.inputBits words
  let prep := frontend generate
  obtain ⟨a,ha,parsed⟩ := CompactFrame.decode_packed (src := IO.env) (dst := IO.row) (by decide) hw payload
    (io [] wire []) rfl rfl
  have image : Function.update (Function.update (io [] wire []) IO.env []) IO.row payload = io payload [] [] := by
    funext i; cases i <;> simp [io]
  rw [image] at parsed
  have r := prefix_run (CompactFrame.decode IO.env IO.row) generate parsed expand
  have lim : a + (genCost + (2*(CellMacro.stream ops).length+1)) + CellMacro.budget ops ≤ stackClock n := by
    unfold stackClock
    omega
  have stack := stack_value prep wire ops r lim
  let nativeInput := input (none : Option Bool) some (tapePorts generate (.inl .env)) wire
  have bank : CellMacro.StackTape.values (tapePorts generate) nativeInput = prep.bank (io [] wire []) := by
    rw [CellMacro.StackTape.values_input]
    funext p
    cases p with
    | inl i => cases i <;> simp [Fragment.bank,io]
    | inr j => simp [Fragment.bank]
  have sim := CellMacro.StackTape.simulation (tapePorts generate) (program prep) (negative prep)
    (stackClock n) (.inl prep.body.body.entry) nativeInput
  rw [bank] at sim
  have small := (TeamPrivateValue.track_stops_iff CellDispatch.PrivateCell.alphabet (tapeTable generate) _ (entry generate) nativeInput).2 (sim.1.2 stack.1)
  have extend := extend_stops _ small (show 2*stackClock n ≤ nativeClock n from (Nat.mul_div_le ..).trans (Nat.le_succ _))
  exact ⟨extend.1, extend.2.trans ((track_paths CellDispatch.PrivateCell.alphabet (tapeTable generate) _ (entry generate) nativeInput).trans
      (sim.2.trans stack.2))⟩

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
