import OAI.Computability.VPVNP.PairNodeChildLoop
import OAI.Computability.VPVNP.CompressorShrinkSliceTable

/-!
# Reading the width of a hidden shrinking field

A dense field identifier encodes a motif ordinal and one of four roles.
The reader looks up the motif's repetition count and the role's payload in
the layout opposite the surviving one. The resulting bit width is their
payload plus the selector bits for all repetitions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenWidth

open BurstRAM PrivateRAM CompressorRecords ShrinkSliceArrays NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.read ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k : ℕ}

/-- Registers zero through four hold the ID pointer, term base, term stride,
layout bit, and selector width. Register five receives the width, six keeps
the ID, and registers seven through nine are temporary. -/
def instruction (pc : Fin 18 → Fin p) (reg : Fin 10 ↪ Fin r) (done : Fin p) : Fin 18 → Instr w p r k :=
  ![.readExternal (reg 6) (reg 0) (pc 1),
    .constant (reg 8) 4 (pc 2),
    .binary .div (reg 7) (reg 6) (reg 8) (pc 3),
    .binary .mul (reg 7) (reg 7) (reg 2) (pc 4),
    .binary .add (reg 7) (reg 1) (reg 7) (pc 5),
    .constant (reg 9) 1 (pc 6),
    .binary .add (reg 5) (reg 7) (reg 9) (pc 7),
    .readExternal (reg 5) (reg 5) (pc 8),
    .binary .mul (reg 5) (reg 5) (reg 4) (pc 9),
    .binary .sub (reg 9) (reg 9) (reg 3) (pc 10),
    .binary .mul (reg 9) (reg 9) (reg 8) (pc 11),
    .binary .mod (reg 8) (reg 6) (reg 8) (pc 12),
    .binary .add (reg 9) (reg 9) (reg 8) (pc 13),
    .constant (reg 8) 2 (pc 14),
    .binary .add (reg 8) (reg 7) (reg 8) (pc 15),
    .binary .add (reg 8) (reg 8) (reg 9) (pc 16),
    .readExternal (reg 8) (reg 8) (pc 17),
    .binary .add (reg 5) (reg 8) (reg 5) done]

theorem resize_instruction (pc : Fin 18 → Fin p) (reg : Fin 10 ↪ Fin r) (done : Fin p) (i : Fin 18) :
    (instruction (w := 3) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- The machine implements all 18 width-reader instructions at their assigned addresses with
the specified register bank and continuation. -/
def Linked (M : Machine w p r k) (pc : Fin 18 → Fin p) (reg : Fin 10 ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- Word address of the selected term record. The quotient of the dense hidden ID by four
selects the motif ordinal in the strided term array. -/
def rowBase (termBase termStride id : Word w) : Word w :=
  termBase + BinaryOp.div.eval id 4 * termStride

/-- Payload offset among the eight role coordinates of a term. It takes the role from the ID
modulo four and chooses the four-role half opposite the surviving layout. -/
def coordinate (layout id : Word w) : Word w :=
  (1-layout) * 4 + BinaryOp.mod.eval id 4

/-- The 18 events of a width lookup, including the dense ID read at `ptr`, the repetition count
at `base + 1`, and the payload at `base + 2 + coord`. -/
def events (m : Memory w) (ptr base coord : Word w) : List (Event w) :=
  let read := fun addr : Word w => Event.read addr (m addr.val)
  [read ptr,.tick,.tick,.tick,.tick,.tick,.tick,read (base+1),
   .tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,read (base+2+coord),.tick]

theorem cost (m : Memory w) (ptr base coord : Word w) :
    (events m ptr base coord).length = 18 ∧ countProbes (events m ptr base coord) = 3 ∧
      choiceBits (events m ptr base coord) = [] := ⟨rfl, rfl, rfl⟩

variable {M : Machine w p r k} {pc : Fin 18 → Fin p} {reg : Fin 10 ↪ Fin r} {done : Fin p}

private theorem step_at (link : Linked M pc reg done) (i : Fin 18) {c : Config w p r}
    (h : c.pc = pc i) : M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, h, link i]

/-- Exact native execution, including the retained ID and the complete
frame on the caller's configuration. -/
theorem native (link : Linked M pc reg done) (m : Memory w) (c : Config w p r) (hc : c.pc = pc 0) :
    let ptr := c.reg (reg 0)
    let id := m ptr.val
    let base := rowBase (c.reg (reg 1)) (c.reg (reg 2)) id
    let coord := coordinate (c.reg (reg 3)) id
    ∃ d, Prefix M m c d [] (events m ptr base coord) ∧ d.pc = done ∧
      d.reg (reg 5) = supplyValue (supplyData coord (c.reg (reg 4)) 0) base m ∧
      d.reg (reg 6) = id ∧
      (∀ j, j ≠ reg 5 → j ≠ reg 6 → j ≠ reg 7 → j ≠ reg 8 → j ≠ reg 9 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  intro ptr id base coord
  have path := ReadPrefix.read (m := m) ptr (step_at link 0 hc)
    (ReadPrefix.tick (step_at link 1 rfl)
    (ReadPrefix.tick (step_at link 2 rfl)
    (ReadPrefix.tick (step_at link 3 rfl)
    (ReadPrefix.tick (step_at link 4 rfl)
    (ReadPrefix.tick (step_at link 5 rfl)
    (ReadPrefix.tick (step_at link 6 rfl)
    (ReadPrefix.read _ (step_at link 7 rfl)
    (ReadPrefix.tick (step_at link 8 rfl)
    (ReadPrefix.tick (step_at link 9 rfl)
    (ReadPrefix.tick (step_at link 10 rfl)
    (ReadPrefix.tick (step_at link 11 rfl)
    (ReadPrefix.tick (step_at link 12 rfl)
    (ReadPrefix.tick (step_at link 13 rfl)
    (ReadPrefix.tick (step_at link 14 rfl)
    (ReadPrefix.tick (step_at link 15 rfl)
    (ReadPrefix.read _ (step_at link 16 rfl)
    (ReadPrefix.tick (step_at link 17 rfl) (ReadPrefix.nil _))))))))))))))))))
  let final {d : Config w p r} {es : List (Event w)} (_ : ReadPrefix M m c es d) := d
  refine ⟨final path, ?_, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro fuel tail
    simpa (config := { decide := true }) [events, ptr, id, base, coord, rowBase, coordinate,
      Config.put, reg.injective.eq_iff, BinaryOp.eval, final] using ReadPrefix.execute path fuel tail
  · simp (config := { decide := true }) [final, Config.put, reg.injective.eq_iff, BinaryOp.eval,
      supplyValue, supplyData, base, coord, rowBase, coordinate, id, ptr]
  · simp (config := { decide := true }) [final, Config.put, reg.injective.eq_iff, id, ptr]
  · intro j h5 h6 h7 h8 h9
    simp [final, Config.put, Function.update_of_ne h5, Function.update_of_ne h6,
      Function.update_of_ne h7, Function.update_of_ne h8, Function.update_of_ne h9]

/-- Decode the motif ordinal in the dense field ID. -/
theorem rowBase_eq (id : Word w) (termBase stride ordinal : ℕ) (t : Fin 4)
    (hid : id.val = ordinal*4+t.val) (h4 : 4 < 2^w) :
    rowBase (termBase : Word w) (stride : Word w) id = ((termBase+ordinal*stride : ℕ) : Word w) := by
  have div : BinaryOp.div.eval id 4 = (ordinal : Word w) := by
    change Fin.ofNat _ (id.val/(4 : Word w).val) = _
    rw [show (4 : Word w).val = 4 from Nat.mod_eq_of_lt h4, hid,
      show (ordinal*4+t.val)/4 = ordinal by have := t.isLt; omega]
    rfl
  simp only [rowBase, div, Nat.cast_add, Nat.cast_mul]

/-- Decode the role and switch to the hidden half of the eight payload words. -/
theorem coordinate_eq (id : Word w) (layout : Bool) (ordinal : ℕ) (t : Fin 4)
    (hid : id.val = ordinal*4+t.val) (h4 : 4 < 2^w) :
    coordinate (layout.toNat : Word w) id = (((!layout).toNat*4+t.val : ℕ) : Word w) := by
  have role : BinaryOp.mod.eval id 4 = (t.val : Word w) := by
    change Fin.ofNat _ (id.val%(4 : Word w).val) = _
    rw [show (4 : Word w).val = 4 from Nat.mod_eq_of_lt h4, hid,
      show (ordinal*4+t.val)%4 = t.val by have := t.isLt; omega]
    rfl
  simp only [coordinate, role, Nat.cast_add, Nat.cast_mul]
  cases layout <;> simp

/-- Numeric readback of the native width register for an arbitrary fitted
row. Both the payload and the repetition factor are read from memory. -/
theorem value_eq (m : Memory w) (id selectors : Word w) (termBase stride ordinal : ℕ) (layout : Bool)
    (t : Fin 4) (width : ℕ) (hid : id.val = ordinal*4+t.val)
    (room : termBase+ordinal*stride+10 ≤ 2^w)
    (read : (m (termBase+ordinal*stride+2+((!layout).toNat*4+t.val))).val +
      (m (termBase+ordinal*stride+1)).val * selectors.val = width) (fit : width < 2^w) :
    (supplyValue (supplyData (coordinate (layout.toNat : Word w) id) selectors 0)
      (rowBase (termBase : Word w) (stride : Word w) id) m).val = width := by
  let base := termBase+ordinal*stride
  let index := (!layout).toNat*4+t.val
  have h4 : 4 < 2^w := by omega
  have hi : index < 8 := by
    have h := Bool.toNat_le (!layout)
    have ht := t.isLt
    dsimp only [index]
    omega
  rw [rowBase_eq _ _ _ _ _ hid h4, coordinate_eq _ _ _ _ hid h4]
  have hb : (base : Word w).val = base := Fin.val_cast_of_lt (by dsimp [base]; omega)
  have hc : (index : Word w).val = index := Fin.val_cast_of_lt (by omega)
  apply supplyValue_eq _ _ _ _ _ fit
  · change (base : Word w).val+2+(index : Word w).val < 2^w
    rw [hb, hc]
    dsimp [base]
    omega
  · change (m ((base : Word w).val+2+(index : Word w).val)).val +
      (m ((base : Word w).val+1)).val * selectors.val = _
    rwa [hb, hc]

section Term

open Compression Compression.PackingData ShrinkSliceSweep Allocation SliceSchedule
open MotifBlocks MotifGrid MotifConversion MotifDemandPadding ShrinkMotif

variable {d c n N J nL : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (cd : P.BundleNumbering) (site : Site V Tag L ≃ Fin n)

local notation "count" => (n*d)*pieceCount d c
local notation "order" => ShrinkMotifOrder.number P cd site

variable (T : Allocation w ((n*d)*pieceCount d c) (Slots.oldBaseArcCount N J d c * nL))
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (old : Arc V H Tag L d c → ℕ) (choice : ∀ q : P.Motif, P.ShrinkChoice cd old F q)

/-- The term directory's chosen hidden width is precisely the native
readback for its corresponding dense ID. -/
theorem term_value_eq (m : Memory w) (terms : Terms P cd site T F old choice m)
    (allocation : T.Fits) (sel : T.selectors.val = F.selectorBits)
    (j : Fin count) (t : Fin 4) (id : Word w) (hid : id.val = j.val*4+t.val)
    (fit : P.termWidths F cd old choice ((order).symm j) (!T.layout) t < 2^w) :
    (supplyValue (supplyData (coordinate (T.layout.toNat : Word w) id) T.selectors 0)
      (rowBase (T.termBase : Word w) (T.termStride : Word w) id) m).val =
      P.termWidths F cd old choice ((order).symm j) (!T.layout) t := by
  have limit := T.term_stop allocation j
  have room : T.termStart j+10 ≤ 2^w :=
    limit.trans ((Nat.le_add_right .. : T.widthBase ≤ T.widthEnd).trans
      ((Nat.le_add_right .. : T.widthEnd ≤ T.last).trans allocation.room.le))
  apply value_eq m id T.selectors T.termBase T.termStride j.val T.layout t _ hid room _ fit
  have fields := terms j
  let i := supplyRoles.symm (!T.layout, t)
  have val := fields.2.2 i
  have rep := fields.2.1
  have hb : (Fin.ofNat (2^w) (T.termStart j)).val = T.termStart j :=
    (Fin.val_ofNat ..).trans (Nat.mod_eq_of_lt (by omega))
  rw [hb, show i.val = (!T.layout).toNat*4+t.val from supplyRoles_index ..,
    show supplyRoles i = (!T.layout,t) from supplyRoles.apply_symm_apply _] at val
  rw [hb] at rep
  change (m (T.termStart j+2+((!T.layout).toNat*4+t.val))).val +
    (m (T.termStart j+1)).val * T.selectors.val = _
  rw [val,rep,sel]
  rfl

end Term
end PairSimulation.ShrinkHiddenWidth

end VPVNP
end Computability
end OAI
