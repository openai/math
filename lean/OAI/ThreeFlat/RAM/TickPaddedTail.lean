import OAI.ThreeFlat.RAM.TickLUTSeed
import OAI.ThreeFlat.RAM.HistoryPadROM
import OAI.ThreeFlat.RAM.HistoryPadStores
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # Finishing a genuine selected row stream at the fixed common slot shape -/

namespace ThreeFlat.RAM.TickPaddedTail
open Computability.VPVNP.BurstRAM PrivateRAM HistoryFactors DescriptorExpr DescriptorScan
open BitLayout Diagonal.TraceCircuit
open scoped Fin.CommRing

variable {F : Type*} [Zero F] [One F] {w k p r pc : ℕ}

set_option maxHeartbeats 300000 in
/-- The metadata producer writes the genuine part of the selected forest and
four size words. The two native loops share the continuation ROM and finish
all padded records and LUT entries in bounded time. -/
theorem generate (M : Machine w pc r k) (code : FieldCode F w)
    (N : BitNetwork F p) (L : Library N) (b u metadata lut : ℕ)
    (base : Fin k) (pad : Fin (HistoryPadROM.count (w:=w) base) → Fin pc)
    (pr : Fin (4+(HistoryPadDriver.term (w:=w) base).binds) ↪ Fin r)
    (seed : Fin ((TickLUTSeed.expr (k:=k) code (L.padded b u).table lut).labels+6) → Fin pc)
    (sr : Fin (4+(TickLUTSeed.expr (k:=k) code (L.padded b u).table lut).binds) ↪ Fin r)
    (exit : Fin pc) (m : Memory w) (c : Config w pc r)
    (romSeed : ∀ i, M.code (seed i) = TickGenerateTable.emit
      (TickLUTSeed.expr code (L.padded b u).table lut) (lut : Word w) (lut+8*(L.count+2) : ℕ)
      seed sr (HistoryPadROM.setup (w:=w) base pad 0) i)
    (romPad : ∀ i, M.code (pad i) = HistoryPadROM.emit base (metadata+4*N.cells+4*(b+u) : ℕ)
      pad pr exit i)
    (start : c.pc = TickGenerateTable.driver (TickLUTSeed.expr code (L.padded b u).table lut) seed 0)
    (safe : metadata+4*N.cells+4*(b+u) ≤ lut) (fit : lut+8*(L.count+2) < 2^w)
    (header : ∀ j : Fin 4, HistoryPadDriver.header (M.publicData base) m j =
      ![(metadata+4*N.cells : ℕ),(b : Word w),(hiddenBase p+N.internal : ℕ),(L.count : Word w)] j)
    (away : ∀ j : Fin 4, (M.publicData base+(j.val : Word w)).val < metadata+4*N.cells ∨
      lut+8*(L.count+2) ≤ (M.publicData base+(j.val : Word w)).val)
    (rows : ∀ i : Fin N.cells, ∀ j : Fin 4, m (metadata+4*i.val+j.val) = metadataWord L i j) :
    ∃ t ≤ (4+8*(L.count+2)*(6*(8*(L.count+2))+10))+(5+62*(4*(b+u))),
      ∃ out : Config w pc r, ∃ result : Memory w, out.pc=exit ∧
        advance M.program t c m = some (out,result) ∧
        Stores (addPadding N b u) (L.padded b u) code metadata lut result ∧
        ∀ i < metadata, result i = m i := by
  have hb : b<2^w := by omega
  have hn : L.count<2^w := by omega
  let lower := metadata+4*N.cells
  let words := 4*(b+u)
  let tables := L.count+2
  let T := (L.padded b u).table
  let seeded : Memory w := fillSegment lut (8*tables) (fun a => TickLUTSeed.entry code T (a-lut)) m
  obtain ⟨s,ls,d,dpc,runs,values⟩ := TickLUTSeed.generate M code T lut fit m c seed sr
    (HistoryPadROM.setup (w:=w) base pad 0) romSeed start
  have seedLow (i : ℕ) (hi : i<lut ∨ lut+8*tables ≤ i) : seeded i = m i := by
    change (if lut ≤ i ∧ i < lut+8*tables then _ else _) = _
    rw [ite_eq_right (by omega)]
  have safeHead (j : Fin 4) : HistoryPadDriver.header (M.publicData base) seeded j =
      ![(lower : Word w),(b : Word w),(hiddenBase p+N.internal : ℕ),(L.count : Word w)] j := by
    change seeded (M.publicData base+(j.val : Word w)).val = _
    rw [seedLow _ (by rcases away j with h|h; exact Or.inl (by omega); exact Or.inr h)]
    have old := header j
    fin_cases j <;> simpa [lower,HistoryPadDriver.header,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hn] using old
  have hspan : ((lower+words : ℕ) : Word w).val = lower+words := Fin.val_cast_of_lt (by
    dsimp [lower,words]; omega)
  have outside (j : Fin 4) : (M.publicData base+(j.val:Word w)).val<lower ∨ lower+words≤(M.publicData base+(j.val:Word w)).val := by
    rcases away j with h|h
    · exact Or.inl h
    · right; dsimp only [lower,words]; omega
  let last : Word w := ((lower+words:ℕ):Word w)
  let first : Word w := ((hiddenBase p+N.internal:ℕ):Word w)
  have padCode : ∀ i,M.code (pad i)=HistoryPadROM.emit (w:=w) base last pad pr exit i := romPad
  have padPC : d.pc=HistoryPadROM.setup (w:=w) base pad 0 := dpc
  have phase := HistoryPadROM.generate (w:=w) (k:=k) (p:=pc) (r:=r) base last M pad pr exit
    padCode lower words (b:Word w) first (L.count:Word w) d seeded
  have controlled := phase safeHead
  have separate := controlled outside
  have spanned := separate hspan
  obtain ⟨t,lt,e,epc,runt⟩ := spanned padPC
  let result := HistoryPadDriver.paddedMemory L b u metadata seeded
  change advance M.program s c m=some (d,seeded) at runs
  change advance M.program t d seeded=some (e,result) at runt
  refine ⟨s+t,Nat.add_le_add ls lt,e,result,epc,advance_trans runs runt,?_,?_⟩
  · apply HistoryPadDriver.stores_after_padding L b u metadata lut code seeded (by omega) safe
    · intro i j
      rw [seedLow _ (Or.inl (by have := i.isLt; have := j.isLt; omega))]
      exact rows i j
    · exact values
  · intro i hi
    change (if lower ≤ i ∧ i < lower+words then _ else seeded i) = m i
    rw [ite_eq_right (by dsimp [lower]; omega)]
    exact seedLow i (Or.inl (by omega))

end ThreeFlat.RAM.TickPaddedTail

end OAI
