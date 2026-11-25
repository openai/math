import OAI.ThreeFlat.RAM.DescriptorDriver
import OAI.ThreeFlat.RAM.ContractionTail

namespace OAI
/-! # Generating the network in memory and then contracting it on one RAM -/

namespace ThreeFlat.RAM.GeneratedContraction

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout DescriptorScan Contraction Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {w p d r k : ℕ}

abbrev Row (w d r k : ℕ) := Instr w (d+(6+35)) (4+(10+r)) (2+(5+k))

def tailPC (d : ℕ) : Fin 35 ↪ Fin (d+(6+35)) :=
  ⟨tailPc d, fun i j e => by
    apply Fin.ext
    have h := congrArg Fin.val e
    simpa [tailPc] using h⟩

def tailReg (r : ℕ) : Fin 10 ↪ Fin (4+(10+r)) :=
  ⟨fun i => Fin.natAdd 4 (i.castAdd r), fun i j e => by simpa using e⟩

def tailPub (k : ℕ) (i : Fin 5) : Fin (2+(5+k)) := Fin.natAdd 2 (i.castAdd k)

def evalRow (i : Fin 35) : Row w d r k :=
  ContractionTail.relocate (tailPC d) (tailReg r) (tailPub k) (instruction i)

variable (N : BitNetwork F p) (fit : Fits N w)
variable (entry : Fin d) (desc : Fin d → Row w d r k) (pub : Fin k → Word w)

/-- The public words contain two interval endpoints, five evaluator parameters,
and the descriptor's own public operands. The generated cell array occupies
no words in these public operands. -/
noncomputable def machine : Machine w (d+(6+35)) (4+(10+r)) (2+(5+k)) :=
  assemble entry 0 desc evalRow (cellsBase p N.internal : Word w)
    (mulBase p N.internal N.cells : Word w) (Fin.addCases (parameters N fit) pub)

noncomputable def initialized (s : Word w) : Config w (d+(6+35)) (4+(10+r)) :=
  booted (cellsBase p N.internal : Word w) (mulBase p N.internal N.cells : Word w) s

/-- Once each locally computed word is certified on the descriptor's native
instructions, the whole machine constructs all eleven columns of every cell
and returns the exact contraction. The time allowance includes the three
initialization instructions and the final scan comparison. -/
theorem value_eq (cost : ℕ) (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (s : Word w) (m : Memory w) (extra : ℕ)
    (valid : Config w (d+(6+35)) (4+(10+r)) → Memory w → Prop)
    (valid_start : valid (initialized (d:=d) (r:=r) N s) m)
    (routine : Describes (machine N fit entry desc pub) (driverRegs (10+r))
      (driverLabels entry (0 : Fin 35)) cost (memory N (codec N fit) pin hidden) valid)
    (outside : ∀ a < footprint N, a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a →
      m a = memory N (codec N fit) pin hidden a) :
    value (codec N fit) (machine N fit entry desc pub)
      (extra + 13 + 5*N.internal + 22*N.cells + (11*N.cells)*(cost+3)) s m = N.eval pin := by
  let M := machine N fit entry desc pub
  let R := driverRegs (10+r)
  let L := driverLabels entry (0 : Fin 35)
  let init := initialized (d:=d) (r:=r) N s
  let target := memory N (codec N fit) pin hidden
  have first : advance M.program 3 (M.program.start s) m = some (init,m) :=
    boot entry 0 desc evalRow _ _ _ s m
  have guard : init.pc = L.guard := rfl
  have lo : (init.reg (R 0)).val = cellsBase p N.internal := by
    change ((cellsBase p N.internal : Word w) : ℕ) = _
    apply Fin.val_cast_of_lt
    simpa [cellAddr] using cellAddr_lt N fit (Nat.zero_le N.cells)
  have hi : (init.reg (R 1)).val = mulBase p N.internal N.cells := by
    change ((mulBase p N.internal N.cells : Word w) : ℕ) = _
    exact Fin.val_cast_of_lt (mulBase_lt N fit)
  have len : (init.reg (R 0)).val + 11*N.cells = (init.reg (R 1)).val := by
    rw [lo,hi]
    rfl
  obtain ⟨used, bound, out, exitPc, generated⟩ := generate M R L
    (driver_installed entry 0 desc evalRow _ _ _) cost target valid routine
    (11*N.cells) init m guard valid_start len
  have installed (a : ℕ) (ha : a < footprint N) :
      fillSegment (init.reg (R 0)).val (11*N.cells) target m a = target a := by
    rw [lo]
    by_cases h : cellsBase p N.internal ≤ a ∧ a < cellsBase p N.internal+11*N.cells
    · simp [fillSegment, h]
    · simpa [fillSegment, h] using outside a ha (by unfold mulBase; omega)
  let left := extra + (1+(11*N.cells)*(cost+3)-used)
  let rest := left + 9 + 5*N.internal + 22*N.cells
  have cap : extra+13+5*N.internal+22*N.cells+(11*N.cells)*(cost+3) = rest+(3+used) := by
    dsimp [left,rest]
    omega
  rw [value,cap,mass_of_advance (codec N fit) M.program (advance_trans first generated) rest]
  exact ContractionTail.mass_eq_network_of_prefix (tailPC d) (tailReg r) (tailPub k) M N fit
    (fun i => assembled_tail entry 0 desc evalRow _ _ _ i)
    (by intro i; simp [M,machine,assemble,tailPub])
    out exitPc pin hidden left _ installed

end ThreeFlat.RAM.GeneratedContraction

end OAI
