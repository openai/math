import OAI.ThreeFlat.RAM.TickClearLink
import OAI.ThreeFlat.RAM.HistoryInterpreterTail

namespace OAI
/-! # Weighted history evaluation from an arbitrary caller register frame -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Contraction NativeRelocate

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}

/-- Thirty-six native writes initialize the interpreter's complete register
frame. The preparation code can leave arbitrary values in all caller registers. -/
theorem mass_clear_interpreter {P R K : ℕ} (loc : Fin 37 → Fin P)
    (pc : Fin 108 ↪ Fin P) (reg : Fin 36 ↪ Fin R) (pub : Fin 7 → Fin K)
    (M : Machine w P R K) (N : BitNetwork F p) (fit : Fits N w) (L : Library N)
    («meta» lut : ℕ) (hm : mulBase p N.internal N.cells ≤ «meta»)
    (hl : mulBase p N.internal N.cells ≤ lut)
    (bm : «meta»+4*N.cells ≤ 2^w) (bl : lut+8*L.count ≤ 2^w)
    (input : Memory w) (stored : Stores N L (codec N fit) «meta» lut input)
    (pin : Fin p → Bool) (initial : Fin N.internal → Bool)
    (outside : ∀ a < footprint N, a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a →
      input a = memory N (codec N fit) pin initial a)
    (clearRows : ∀ i : Fin 36, M.code (loc i.castSucc) = TickClearFrame.row loc reg i)
    (entry : loc (Fin.last 36) = pc (interpreter p N.internal N.cells «meta» lut (F := F) fit).entry)
    (rows : ∀ i, M.code (pc i) = relocate pc reg pub
      ((interpreter p N.internal N.cells «meta» lut (F := F) fit).code i))
    (params : ∀ i, M.publicData (pub i) =
      (interpreter p N.internal N.cells «meta» lut (F := F) fit).publicData i)
    (c : Config w P R) (start : c.pc = loc 0) (extra : ℕ) :
    mass (codec N fit) M.program (extra+49+5*N.internal+550*N.cells) c input = N.eval pin := by
  rw [show extra+49+5*N.internal+550*N.cells = (extra+13+5*N.internal+550*N.cells)+36 by omega,
    TickClearFrame.mass_clear (codec N fit) M loc reg clearRows c input start]
  exact mass_interpreter pc reg pub M N fit L «meta» lut hm hl bm bl input stored pin initial outside
    rows params _ entry (TickClearFrame.cleared_target reg _ c) extra

attribute [local irreducible] interpreter ExternalOnly TickClearFrame.prepend

/-- The assembled 144-label ROM evaluates the buffered history after clearing the 36 registers.
Its instruction tables are fixed by the capacities and the two table bases. -/
theorem mass_prefixed_interpreter (N : BitNetwork F p) (fit : Fits N w) (L : Library N)
    («meta» lut : ℕ) (hm : mulBase p N.internal N.cells ≤ «meta»)
    (hl : mulBase p N.internal N.cells ≤ lut)
    (bm : «meta»+4*N.cells ≤ 2^w) (bl : lut+8*L.count ≤ 2^w)
    (input : Memory w) (stored : Stores N L (codec N fit) «meta» lut input)
    (pin : Fin p → Bool) (initial : Fin N.internal → Bool)
    (outside : ∀ a < footprint N, a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a →
      input a = memory N (codec N fit) pin initial a)
    (c : Config w (36+108) 36)
    (start : c.pc = (TickClearFrame.prepend
      (interpreter p N.internal N.cells «meta» lut (F := F) fit)).entry) (extra : ℕ) :
    mass (codec N fit) (TickClearFrame.prepend
      (interpreter p N.internal N.cells «meta» lut (F := F) fit)).program
      (extra+49+5*N.internal+550*N.cells) c input = N.eval pin := by
  let T := interpreter p N.internal N.cells «meta» lut (F := F) fit
  let fuel := extra+13+5*N.internal+550*N.cells
  have allow := interpreter_allowed
    (F:=F) (p:=p) (h:=N.internal) (cells:=N.cells) (metadata:=«meta») (lut:=lut) fit
  have clear := TickClearFrame.mass_prepend (codec N fit) T allow c input start fuel
  have result := clear.trans
    (value_interpreter N fit L «meta» lut hm hl bm bl input stored pin initial outside c.persistent extra)
  have ticks : extra+49+5*N.internal+550*N.cells = fuel+36 := by dsimp only [fuel]; omega
  rw [ticks]
  exact result

end ThreeFlat.RAM.HistoryFactors

end OAI
