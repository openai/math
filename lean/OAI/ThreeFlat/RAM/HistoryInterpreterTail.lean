import OAI.ThreeFlat.RAM.HistoryInterpreter
import OAI.ThreeFlat.RAM.ExpressionRelocate

namespace OAI
/-! # Entering the weighted history interpreter after deterministic preparation -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout Contraction DescriptorScan
  DescriptorExpr GeneratedContraction NativeRelocate

variable {F : Type*} [Fintype F] [Field F] {p w h cells metadata lut : ℕ}

private theorem external_resize {a b A B k : ℕ} (M : Machine w a b k) (ha : a=A) (hb : b=B)
    (allowed : ∀ i, ExternalOnly (M.code i)) (i : Fin A) :
    ExternalOnly ((resize M ha hb).code i) := by
  subst A B
  exact allowed i

attribute [local irreducible] NativeRelocate.ExternalOnly GeneratedContraction.machine resize reader

theorem interpreter_allowed (fit : Fits (BitNetwork.blankNetwork (F := F) p h cells) w)
    (i : Fin 108) : ExternalOnly ((interpreter p h cells metadata lut fit).code i) := by
  let e := reader (w:=w) p h metadata lut
  let N := BitNetwork.blankNetwork (F:=F) p h cells
  let pub := (Fin.elim0 : Fin 0 → Word w)
  let M := GeneratedContraction.machine N fit e.first (expressionRows e) pub
  have n : e.binds = 22 := by
    unfold e reader
    exact HistoryFactorScan.binds_readCellWord _ _ _
  have rows : e.labels+(6+35) = 108 := by rw [Term.labels_eq,n]
  have regs : 4+(10+e.binds) = 36 := by rw [n]
  unfold interpreter
  exact external_resize M rows regs (GeneratedContraction.machine_externalOnly N fit e pub) i

attribute [local irreducible] interpreter

/-- Installed after a deterministic prefix, the interpreter reads the compact buffers
and returns the same total weight with arbitrary caller state outside its register bank. -/
theorem mass_interpreter {P R K : ℕ} (pc : Fin 108 ↪ Fin P) (reg : Fin 36 ↪ Fin R)
    (pub : Fin 7 → Fin K) (M : Machine w P R K) (N : BitNetwork F p) (fit : Fits N w)
    (L : Library N) (metadata lut : ℕ) (hm : mulBase p N.internal N.cells ≤ metadata)
    (hl : mulBase p N.internal N.cells ≤ lut)
    (bm : metadata+4*N.cells ≤ 2^w) (bl : lut+8*L.count ≤ 2^w)
    (input : Memory w) (stored : Stores N L (codec N fit) metadata lut input)
    (pin : Fin p → Bool) (initial : Fin N.internal → Bool)
    (outside : ∀ a < footprint N, a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a →
      input a = memory N (codec N fit) pin initial a)
    (rows : ∀ i, M.code (pc i) = relocate pc reg pub
      ((interpreter p N.internal N.cells metadata lut (F := F) fit).code i))
    (params : ∀ i, M.publicData (pub i) =
      (interpreter p N.internal N.cells metadata lut (F := F) fit).publicData i)
    (c : Config w P R)
    (start : c.pc = pc (interpreter p N.internal N.cells metadata lut (F := F) fit).entry)
    (zero : ∀ i, c.reg (reg i) = 0) (extra : ℕ) :
    mass (codec N fit) M.program (extra+13+5*N.internal+550*N.cells) c input = N.eval pin := by
  let native := interpreter p N.internal N.cells metadata lut (F := F) fit
  have allow : ∀ i : Fin 108, ExternalOnly (native.code i) :=
    interpreter_allowed (F:=F) (p:=p) (w:=w) (h:=N.internal) (cells:=N.cells)
      (metadata:=metadata) (lut:=lut) fit
  exact (NativeRelocate.mass_eq_value pc reg pub native M allow
    rows params (codec N fit) _ c 0 input start zero).trans
      (value_interpreter N fit L metadata lut hm hl bm bl input stored pin initial outside 0 extra)

end ThreeFlat.RAM.HistoryFactors

end OAI
