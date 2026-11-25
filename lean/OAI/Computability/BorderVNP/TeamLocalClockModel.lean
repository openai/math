import OAI.Computability.BorderVNP.TeamLocalClockPC
import OAI.Computability.BorderVNP.TeamLocalClockLoop
import OAI.Computability.BorderVNP.TeamTapeHandoff

/-!
# Finite program-counter labels and full-word successor frames

A decoded register message has a word-sized PC. The physical dispatcher names
only the valid labels of its fixed table. Encoding a valid finite PC commutes
with every adaptive RAM instruction, including the sign and private choice
tape of a subroutine. An out-of-range PC rejects.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock.Model

open VPVNP BurstRAM RAMTape.PublicExprMachine Filter

variable {w p r k m : ℕ} {S R : Type*}

/-- Relabel only the continuing register state. Read addresses, intervals, private
choice identities, terminal signs and branch slots are preserved literally. -/
def mapControl (f : S → R) : TeamRAM.Instr w S → TeamRAM.Instr w R
  | .accept => .accept
  | .reject => .reject
  | .localStep next sign => .localStep (f next) sign
  | .choose next => .choose (f ∘ next)
  | .load a next => .load a (f ∘ next)
  | .store a v next => .store a v (f next)
  | .call a n run next => .call a n run (f next)

/-- The local memory actions are invariant under control relabeling. -/
theorem action_mapControl (f : S → R) (i : TeamRAM.Instr w S) :
    (mapControl f i).action = i.action := by cases i <;> rfl

/-- Successful private or ordinary continuations retain the same output sign. -/
theorem advance_mapControl (f : S → R) (i : TeamRAM.Instr w S) (bs : List Bool) (vs : List (Word w)) :
    (mapControl f i).advance bs vs = (i.advance bs vs).map (fun z => (f z.1,z.2)) := by
  cases i with
  | accept | reject => rfl
  | localStep next sign => cases bs <;> cases vs <;> rfl
  | choose next =>
    cases bs with
    | nil => rfl
    | cons b tail => cases tail <;> cases vs <;> rfl
  | load a next | store a _ next =>
    cases bs <;> cases vs with
    | nil => rfl
    | cons v tail => cases tail <;> rfl
  | call a n run next =>
    simp only [mapControl, TeamRAM.Instr.advance]
    split <;> simp [Option.map_map, Function.comp_def]

/-- Commuting with fetch suffices for equality of complete native signed event histories
on every initial memory and every proposed choice tape. -/
theorem execute_commutes (f : S → R) (P : S → TeamRAM.Instr w S) (T : R → TeamRAM.Instr w R)
    (h : ∀ s, T (f s) = mapControl f (P s)) (s : S) (mem : Memory w) (bs : List (List Bool)) :
    TeamRAM.execute T (f s) mem bs = TeamRAM.execute P s mem bs := by
  induction bs generalizing s mem with
  | nil => cases e : P s <;> simp [TeamRAM.execute, h, e, mapControl]
  | cons bits tail ih =>
    rw [TeamRAM.execute, TeamRAM.execute, h, action_mapControl]
    cases he : (P s).action with
    | none => rfl
    | some act =>
      simp only [advance_mapControl]
      cases ha : (P s).advance bits (TeamRAM.previous mem act) with
      | none => rfl
      | some result =>
        obtain ⟨next, sign⟩ := result
        simp only [Option.map_some, ih]

/-- Encode the fixed PC label and retain all architectural register words. -/
def encode (s : TeamOpcode.State w p r) : TeamTapeHandoff.Control w r := ⟨packed w s.pc.val, s.reg⟩

/-- The actual full-word fetch, using the physical finite-PC decoder before accessing the table. -/
def wordFetch (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (macros : TeamOpcode.Macros w m)
    (s : TeamTapeHandoff.Control w r) : TeamRAM.Instr w (TeamTapeHandoff.Control w r) :=
  match TeamLocalClockPC.lookup p s.pc.val with
  | .live pc => mapControl encode (P.fetch pub macros ⟨pc, s.regs⟩)
  | .accepted | .reject => .reject

/-- Every fixed table label has the same fetched instruction in the word-sized model. -/
theorem fetch_encode (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (macros : TeamOpcode.Macros w m)
    (fits : p ≤ 2^w) (s : TeamOpcode.State w p r) :
    wordFetch P pub macros (encode s) = mapControl encode (P.fetch pub macros s) := by
  rw [wordFetch, encode, TeamLocalClockPC.lookup_packed _ fits]

/-- An invalid full-word PC is rejected before indexing the finite program. -/
theorem fetch_badPC (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (macros : TeamOpcode.Macros w m)
    (s : TeamTapeHandoff.Control w r) (bad : p ≤ s.pc.val) :
    wordFetch P pub macros s = .reject := by
  rw [wordFetch, (TeamLocalClockPC.lookup_reject_iff ..).mpr bad]

/-- Full-word and finite-PC runs are identical on the exact choice blocks, at all memories. -/
theorem execute_encode (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (macros : TeamOpcode.Macros w m)
    (fits : p ≤ 2^w) (start : TeamOpcode.State w p r) (mem : Memory w) (bits : List (List Bool)) :
    TeamRAM.execute (wordFetch P pub macros) (encode start) mem bits =
      TeamRAM.execute (P.fetch pub macros) start mem bits :=
  execute_commutes encode _ _ (fetch_encode P pub macros fits) start mem bits

/-- The quantitative typed handoff and sorted-record theorem for the actual finite
instruction-table program. One word-sized PC frame at each boundary represents precisely
the native finite-PC run, including the private word interval and all signed callbacks. -/
theorem eventually_execute_iff_joint {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, ∀ hr : 0 < teams, ∀ {w p r k m : ℕ}
      (P : TeamOpcode.Program p r k m) (pub : Fin k → Word w) (macros : TeamOpcode.Macros w m),
      p ≤ 2^w → ∀ (start : TeamOpcode.State w p r) (limit : Word w),
      limit.val = TeamScales.ticks ξ teams n → ∀ I : ℕ, I ≤ teams*(3*TeamScales.block ξ n) →
      ∀ (header : ℕ → Word w) (es : List (TeamRAM.Event w)) (bits : List (List Bool)),
      (∀ e ∈ es, e.action.extra ≤ TeamScales.width n (1/2)) → TeamTapeHandoff.cost es ≤ limit.val →
      let h := Nat.clog 2 (4*TeamScales.block ξ n)
      ∀ place : Equiv.Perm (Fin (2^(h+Nat.clog 2 teams))),
        TeamRAM.execute (P.fetch pub macros) start (RAMMemory.initialMemory I header) bits = some es ↔
        ∃! t : TeamTapeHandoff.Joint w r teams h,
          t.Valid hr (TeamScales.block ξ n) (wordFetch P pub macros) (encode start) limit I header es bits place := by
  filter_upwards [TeamTapeHandoff.eventually_execute_iff_joint hξ hξ'] with n h
  intro teams hr w p r k m P pub macros fits start limit he I hi header es bits hb ht width place
  rw [← execute_encode P pub macros fits]
  exact h teams hr _ _ limit he I hi header es bits hb ht place

end TeamLocalClock.Model

end BorderVNP
end Computability
end OAI
