import OAI.Computability.BorderVNP.TeamPrivateTape
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ordinary finite-alphabet multitapes in the private stack interpreter

All bit tracks of a tape share its head movement. Every finite alphabet admits
a fixed-width encoding whose blank is all zero. The width and number of tapes
are constants of a private routine, independent of its input and clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateTape

variable {Q Γ : Type*} {m g d : ℕ}

/-- Finite-width symbol encoding with the correct implicit symbol past either end. -/
structure Alphabet (Γ : Type*) (g : ℕ) where
  /-- Blank symbol beyond the visited cells. -/
  blank : Γ
  /-- Injective fixed-width representation. -/
  bits : Γ ↪ (Fin g → Bool)
  /-- Empty bit stacks give the native blank symbol. -/
  blank_bits : bits blank = fun _ => false

/-- A one-hot track encoding with the blank assigned the all-zero word. -/
noncomputable def Alphabet.ofFintype [Fintype Γ] (blank : Γ) : Alphabet Γ (Fintype.card Γ) := by
  classical
  let e := Fintype.equivFin Γ
  let f (x : Γ) (i : Fin (Fintype.card Γ)) := decide (x ≠ blank ∧ e x = i)
  refine ⟨blank, ⟨f, ?_⟩, ?_⟩
  · intro x y h
    by_contra hxy
    by_cases hx : x = blank
    · have hy : y ≠ blank := by rintro rfl; exact hxy hx
      have h' := congrFun h (e y)
      simp [f, hx, hy] at h'
    · have h' := congrFun h (e x)
      have hyx : e y ≠ e x := fun he => hxy (e.injective he).symm
      simp [f, hx, hyx] at h'
  · funext i; simp [f]

/-- Decode a symbol in the fixed control, treating an unused bit pattern as blank. -/
noncomputable def Alphabet.read (a : Alphabet Γ g) (b : Fin g → Bool) : Γ :=
  open Classical in if h : ∃ x, a.bits x = b then h.choose else a.blank

/-- The decoded head of an encoded tape has exactly the original symbol. -/
theorem Alphabet.read_bits (a : Alphabet Γ g) (x : Γ) : a.read (a.bits x) = x := by
  unfold Alphabet.read
  split
  · rename_i h; exact a.bits.injective h.choose_spec
  · rename_i h; exact (h ⟨x, rfl⟩).elim

/-- Ordinary two-sided tape with an arbitrary symbol type. -/
structure SymbolTape (Γ : Type*) where
  /-- Nearest left neighbor first. -/
  left : List Γ
  /-- The scanned symbol. -/
  head : Γ
  /-- Nearest right neighbor first. -/
  right : List Γ

/-- Simultaneous write and stay/left/right transition at a native tape. -/
def SymbolTape.move (t : SymbolTape Γ) (blank write : Γ) : Option Bool → SymbolTape Γ
  | none => { t with head := write }
  | some false => ⟨t.left.tail, t.left.head?.getD blank, write :: t.right⟩
  | some true => ⟨write :: t.left, t.right.head?.getD blank, t.right.tail⟩

/-- One bit plane of a symbol tape. -/
def SymbolTape.track (t : SymbolTape Γ) (a : Alphabet Γ g) (j : Fin g) : Track :=
  ⟨t.left.map (fun x => a.bits x j), a.bits t.head j, t.right.map (fun x => a.bits x j)⟩

/-- Each synchronized bit-track move implements the exact symbol-tape move, including
when the first step enters previously unvisited blank cells. -/
theorem SymbolTape.track_move (t : SymbolTape Γ) (a : Alphabet Γ g) (j : Fin g)
    (write : Γ) (dir : Option Bool) :
    (t.move a.blank write dir).track a j = (t.track a j).move (a.bits write j) dir := by
  rcases t with ⟨l, x, r⟩
  cases dir with
  | none => rfl
  | some dir =>
    cases dir <;> cases l <;> cases r <;> simp [SymbolTape.move, SymbolTape.track, Track.move, a.blank_bits]

/-- A finite native transition on `m` symbol tapes. -/
structure TapeCommand (Q Γ : Type*) (m : ℕ) where
  /-- Next machine state. -/
  next : Q
  /-- Symbols written in parallel. -/
  write : Fin m → Γ
  /-- Directions assigned to the tapes. -/
  direction : Fin m → Option Bool

/-- One native simultaneous multitape step. -/
def TapeCommand.apply (cmd : TapeCommand Q Γ m) (blank : Γ) (ts : Fin m → SymbolTape Γ) :
    Fin m → SymbolTape Γ := fun i => (ts i).move blank (cmd.write i) (cmd.direction i)

/-- Synchronize all bit tracks of each tape while writing its new symbol. -/
def TapeCommand.tracks (c : TapeCommand Q Γ m) (a : Alphabet Γ g) : Command Q (m*g) :=
  ⟨c.next, fun j => a.bits (c.write (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2,
    fun j => c.direction (finProdFinEquiv.symm j).1⟩

/-- Flatten tape and bit coordinates into the interpreter's fixed finite track set. -/
def tracks (a : Alphabet Γ g) (ts : Fin m → SymbolTape Γ) : Fin (m*g) → Track :=
  fun j => (ts (finProdFinEquiv.symm j).1).track a (finProdFinEquiv.symm j).2

/-- Applying the compiled parallel movement commutes with encoding. -/
theorem tracks_apply (a : Alphabet Γ g) (c : TapeCommand Q Γ m) (ts : Fin m → SymbolTape Γ) :
    (c.tracks a).apply (tracks a ts) = tracks a (c.apply a.blank ts) := by
  funext j
  exact (SymbolTape.track_move ..).symm

/-- Native table choices on the entire tuple of scanned symbols. -/
inductive TapeChoice (Q Γ : Type*) (m : ℕ) where
  | halt (accept negative : Bool)
  | one (cmd : TapeCommand Q Γ m)
  | two (low high : TapeCommand Q Γ m)

/-- Fixed finite-state, finite-alphabet multitape transition table. -/
abbrev TapeTable (Q Γ : Type*) (m : ℕ) := Q → (Fin m → Γ) → TapeChoice Q Γ m

/-- The table after compiling symbols into fixed bit tracks. -/
noncomputable def trackTable (a : Alphabet Γ g) (P : TapeTable Q Γ m) : Table Q (m*g) := fun q h =>
  match P q (fun i => a.read (fun j => h (finProdFinEquiv (i,j)))) with
  | .halt accept sign => .halt accept sign
  | .one c => .one (c.tracks a)
  | .two l r => .two (l.tracks a) (r.tracks a)

/-- Signed multiplicity of the finite-alphabet native paths. -/
def tapePaths (P : TapeTable Q Γ m) (blank : Γ) : ℕ → Q → (Fin m → SymbolTape Γ) → ℤ
  | 0, _, _ => 0
  | t+1, q, ts => match P q (fun i => (ts i).head) with
    | .halt accept sign => TeamTape.haltWeight accept sign
    | .one c => tapePaths P blank t c.next (c.apply blank ts)
    | .two l r => tapePaths P blank t l.next (l.apply blank ts) +
        tapePaths P blank t r.next (r.apply blank ts)

/-- The bit-track simulation preserves every signed accepting multiplicity and its clock. -/
theorem track_paths (a : Alphabet Γ g) (P : TapeTable Q Γ m) (fuel : ℕ)
    (q : Q) (ts : Fin m → SymbolTape Γ) :
    paths (trackTable a P) fuel q (tracks a ts) = tapePaths P a.blank fuel q ts := by
  induction fuel generalizing q ts with
  | zero => rfl
  | succ n ih =>
    have he : (fun i : Fin m => a.read (fun j => heads (tracks a ts) (finProdFinEquiv (i,j)))) =
        (fun i => (ts i).head) := by
      funext i
      simpa only [heads, tracks, Equiv.symm_apply_apply, SymbolTape.track] using a.read_bits (ts i).head
    rw [paths, tapePaths]
    unfold trackTable
    rw [he]
    cases P q (fun i => (ts i).head) with
    | halt => rfl
    | one c =>
      change paths (trackTable a P) n c.next ((c.tracks a).apply (tracks a ts)) = _
      rw [tracks_apply, ih]
    | two l r =>
      change paths (trackTable a P) n l.next ((l.tracks a).apply (tracks a ts)) +
        paths (trackTable a P) n r.next ((r.tracks a).apply (tracks a ts)) = _
      rw [tracks_apply, tracks_apply, ih, ih]

/-- Arbitrary binary input is placed on the selected tape, with its first cell scanned.
All other tapes start blank. -/
def input (blank : Γ) (digit : Bool → Γ) (inputTape : Fin m) (bs : List Bool) : Fin m → SymbolTape Γ :=
  fun i => if i = inputTape then ⟨[], (bs.map digit).head?.getD blank, (bs.map digit).tail⟩
    else ⟨[], blank, []⟩

/-- Total number of occupied unbounded bit-stack cells. -/
def cells (t : Fin d → Track) : ℕ := ∑ j, ((t j).left.length + (t j).right.length)

/-- The total length of all private bit stacks is exactly the occupied-cell count. -/
theorem bank_cells (t : Fin d → Track) : (∑ i : Port d, (bank t i).length) = cells t := by
  rw [Fintype.sum_prod_type]
  simp [cells, bank, Nat.add_comm]

/-- One native transition adds at most one occupied cell on each track. -/
theorem cells_apply_le (c : Command Q d) (t : Fin d → Track) : cells (c.apply t) ≤ cells t + d := by
  calc
    _ ≤ ∑ j, (((t j).left.length + (t j).right.length) + 1) := by
      apply Finset.sum_le_sum
      intro j _
      cases h : c.direction j with
      | none => simp [Command.apply, h, Track.move]
      | some dir =>
        cases dir <;> simp [Command.apply, h, Track.move] <;> omega
    _ = _ := by simp [cells, Finset.sum_add_distrib]

/-- The binary input occupies at most its length times the fixed symbol width. -/
theorem input_cells_le (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (bs : List Bool) :
    cells (tracks a (input a.blank digit i bs)) ≤ bs.length * g := by
  unfold cells tracks
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun z : Fin m × Fin g =>
    ((input a.blank digit i bs z.1).track a z.2).left.length +
      ((input a.blank digit i bs z.1).track a z.2).right.length) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ j : Fin m, ∑ _ : Fin g, if j = i then bs.length else 0 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases he : j = i <;> simp [input, SymbolTape.track, he]
    _ = _ := by simp [Nat.mul_comm]

end TeamPrivateTape

end BorderVNP
end Computability
end OAI
