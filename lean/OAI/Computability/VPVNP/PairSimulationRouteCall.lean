import OAI.Computability.VPVNP.CursorInitialCheck
import OAI.Computability.VPVNP.PairSimulationRouteAddresses
import OAI.Computability.VPVNP.PairSimulationRouteField
import OAI.Computability.VPVNP.PairSimulationRouteGeometry

/-!
# One native call checking a cursor routing field

The geometry block selects the two side bits and the payload test. A second
block adds the field offset to the corresponding resident buffer bases. The
field loop checks the unused outgoing bit and the selected payload test at
each bit position, accumulating any mismatch into the caller's mask.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteCall

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open CursorRouting CursorNetwork RAMLayout
open scoped Fin.CommRing

variable {D H w W p r k : ℕ}

/-- The bit tests belonging to one successor or sorting field. -/
def Good [NeZero D] (v : Position D) (buf : Buffers D H w) (s : RAMSystem D) : Prop :=
  ∀ j : Fin (ramFieldBits H w s),
    readBuffer buf ⟨.outgoing (!(systemMask s).val.testBit v.1.val), s, j⟩ = false ∧
      (payloadTest v s j).run (readBuffer buf) = true

theorem good_iff_bitTests [NeZero D] (v : Position D) (buf : Buffers D H w) (s : RAMSystem D) :
    Good v buf s ↔ ∀ j, (bitTests v s j).all (BitTest.run (readBuffer buf)) = true := by
  simp [Good, bitTests, BitTest.run]

open private routeAccept_iff from OAI.Computability.VPVNP.CursorRouteChecker

theorem routeAccept_iff_good [NeZero D] (v : Position D) (buf : Buffers D H w) :
    routeAccept H w v (readBuffer buf) = true ↔ ∀ s, Good v buf s :=
  routeAccept_iff v (readBuffer buf)

/-- The scheduler's running offset at entry to this field. -/
def startOffset (D H w : ℕ) : RAMSystem D → ℕ
  | .inl j => j.val * (8 * w)
  | .inr l => D * (8 * w) + l.ordinal.val * blockBits H w

theorem offset_bit (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    (ramFieldOffset D H w ⟨s, j⟩).val = startOffset D H w s + j.val := by
  cases s with
  | inl k => exact ramFieldOffset_successor k j
  | inr l => exact ramFieldOffset_sort l j

/-- Each of the four local half-wire buffers resides at its own base.
The bases and memory addresses are host words. -/
def Resident (c : Config W p r) (base : LocalPort → Word W) (buf : Buffers D H w) : Prop :=
  ∀ port j, c.privateMem (base port + (j.val : Word W)) = ((buf port j).toNat : Word W)

private theorem agrees_iff_good [NeZero D] (v : Position D) (buf : Buffers D H w)
    (s : RAMSystem D) (c : Config W p r) (base : LocalPort → Word W)
    (hres : Resident c base buf) (hW : D < W) :
    let out := (systemMask s).val.testBit v.1.val
    let inc := (systemMask s).val.testBit ((finRotate D).symm v.1).val
    let off : Word W := (startOffset D H w s : Word W)
    RouteField.Agrees c.privateMem (RouteGeometry.mode v s : Word W)
      (base (.outgoing (!out)) + off) (base (.outgoing out) + off)
      (base (.incoming inc) + off) (ramFieldBits H w s) ↔ Good v buf s := by
  have cell (port : LocalPort) (j : Fin (ramFieldBits H w s)) :
      c.privateMem (base port + (startOffset D H w s : Word W) + (j.val : Word W)) =
        ((readBuffer buf ⟨port, s, j⟩).toNat : Word W) := by
    simpa only [readBuffer, offset_bit, Nat.cast_add, add_assoc] using
      hres port (ramFieldOffset D H w ⟨s, j⟩)
  have h2 : 2 < 2 ^ W := calc
    2 < 2 ^ 2 := by decide
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by have := NeZero.pos D; omega)
  have h10 : (1 : Word W) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change 1 % 2 ^ W = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have h20 : (2 : Word W) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change 2 % 2 ^ W = 0 at hv
    rw [Nat.mod_eq_of_lt h2] at hv
    omega
  have h21 : (2 : Word W) ≠ 1 := by
    intro he
    have hv := congrArg Fin.val he
    change 2 % 2 ^ W = 1 % 2 ^ W at hv
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have clear (b : Bool) : (b.toNat : Word W) = 0 ↔ b = false := by cases b <;> simp [h10]
  have same (a b : Bool) : (a.toNat : Word W) = (b.toNat : Word W) ↔ a = b := by
    cases a <;> cases b <;> simp [h10, Ne.symm h10]
  dsimp only
  unfold RouteField.Agrees Good
  simp_rw [cell, clear]
  apply forall_congr'
  intro j
  apply and_congr_right'
  by_cases hz : v.1 = 0
  · cases s with
    | inl m =>
      by_cases ha : v.2.val + 1 < 2 ^ D ∧ v.2.val ^^^ (v.2.val + 1) = (systemMask (.inl m)).val <;>
        simp [RouteGeometry.mode, RouteField.PayloadOK, payloadTest, BitTest.run, hz, ha, h10, clear]
    | inr l => simp [RouteGeometry.mode, RouteField.PayloadOK, payloadTest, BitTest.run, hz]
  · simp [RouteGeometry.mode, RouteField.PayloadOK, payloadTest, BitTest.run, hz, h20, h21, same]

/-- The first twelve slots carry the geometry inputs and outputs. -/
def geometryRegs (reg : Fin 32 ↪ Fin r) : Fin 12 ↪ Fin r :=
  (Fin.castLEEmb (by decide)).trans reg

/-- Register holding the base of the indicated outgoing buffer. -/
def outSlot : Bool → Fin 32
  | false => 12
  | true => 13

/-- Register holding the base of the indicated incoming buffer. -/
def inSlot : Bool → Fin 32
  | false => 14
  | true => 15

private def addressSlot : RouteAddresses.Reg → Fin 32
  | .outFlag => 5
  | .inFlag => 6
  | .outBase b => outSlot b
  | .inBase b => inSlot b
  | .offset => 16
  | .zero => 17
  | .unused => 18
  | .used => 19
  | .incoming => 20

/-- Connect the side flags, buffer bases and selected cursors to the address block. -/
def addressRegs (reg : Fin 32 ↪ Fin r) : RouteAddresses.Reg ↪ Fin r :=
  (⟨addressSlot, by decide⟩ : RouteAddresses.Reg ↪ Fin 32).trans reg

private def fieldSlot : Fin 11 → Fin 32 := ![18, 19, 20, 21, 7, 22, 23, 24, 25, 26, 27]

/-- Connect the selected cursors, width, mode and sticky mask to the field scanner. -/
def fieldRegs (reg : Fin 32 ↪ Fin r) : Fin 11 ↪ Fin r :=
  (⟨fieldSlot, by decide⟩ : Fin 11 ↪ Fin 32).trans reg

/-- All register slots written by at least one block of the call. -/
def Scratch (i : Fin 32) : Prop :=
  5 ≤ i.val ∧ i.val ≤ 11 ∨ 18 ≤ i.val ∧ i.val ≤ 20 ∨ i.val = 22 ∨ 24 ≤ i.val ∧ i.val ≤ 27

instance (i : Fin 32) : Decidable (Scratch i) := by unfold Scratch; infer_instance

/-- The register is outside the scratch slots of the three blocks. -/
def Preserved (reg : Fin 32 ↪ Fin r) (a : Fin r) : Prop :=
  ∀ i : Fin 32, Scratch i → a ≠ reg i

theorem preserved_reg (reg : Fin 32 ↪ Fin r) (i : Fin 32) (h : ¬ Scratch i) :
    Preserved reg (reg i) := fun _ hs he ↦ h (reg.injective he ▸ hs)

/-- The geometry exit enters the address block, whose exit enters the field scan. -/
structure Linked (M : Machine W p r k) (gpc : Fin 30 → Fin p) (apc : Fin 8 → Fin p)
    (fpc : Fin 15 → Fin p) (reg : Fin 32 ↪ Fin r) (done : Fin p) : Prop where
  geometry : RouteGeometry.Linked M gpc (geometryRegs reg) (apc 0)
  addresses : RouteAddresses.Linked M apc (addressRegs reg) (fpc 0)
  field : RouteField.Linked M fpc (fieldRegs reg) done

/-- Live cursor and scheduler inputs at the entry to a routing field. -/
structure Ready (reg : Fin 32 ↪ Fin r) (v : Position D) (s : RAMSystem D)
    (base : LocalPort → Word W) (c : Config W p r) : Prop where
  geometry : RouteGeometry.Ready (geometryRegs reg) v s c
  outBase : ∀ b, c.reg (reg (outSlot b)) = base (.outgoing b)
  inBase : ∀ b, c.reg (reg (inSlot b)) = base (.incoming b)
  offset : c.reg (reg 16) = (startOffset D H w s : Word W)
  zero : c.reg (reg 17) = 0
  width : c.reg (reg 21) = (ramFieldBits H w s : Word W)
  one : c.reg (reg 23) = 1

/-- Clock for geometry, the five address-selection instructions, and the scan. -/
def ticks (W : ℕ) [NeZero D] (v : Position D) (s : RAMSystem D) (width : ℕ) : ℕ :=
  RouteGeometry.ticks s + 5 + RouteField.steps (RouteGeometry.mode v s : Word W) width

theorem ticks_le (W : ℕ) [NeZero D] (v : Position D) (s : RAMSystem D) (width : ℕ) :
    ticks W v s width ≤ 13 * width + 34 := by
  have ht : RouteGeometry.ticks s ≤ 26 := by cases s <;> simp [RouteGeometry.ticks]
  have := RouteField.steps_le (RouteGeometry.mode v s : Word W) width
  unfold ticks
  omega

/-- The final mask records the field tests and preserves earlier failures. -/
structure Result [NeZero D] (reg : Fin 32 ↪ Fin r) (done : Fin p) (v : Position D)
    (buf : Buffers D H w) (s : RAMSystem D) (c d : Config W p r) : Prop where
  pc : d.pc = done
  mask : d.reg (reg 22) = 0 ↔ c.reg (reg 22) = 0 ∧ Good v buf s
  frame : ∀ a, Preserved reg a → d.reg a = c.reg a
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

private theorem geometry_preserves (reg : Fin 32 ↪ Fin r) (i : Fin 32) (hi : 12 ≤ i.val) :
    RouteGeometry.Preserved (geometryRegs reg) (reg i) := by
  intro j _ he
  have hv := congrArg Fin.val (reg.injective he)
  change i.val = j.val at hv
  have := j.isLt
  omega

private theorem field_preserves {reg : Fin 32 ↪ Fin r} {a : Fin r} (h : Preserved reg a) :
    RouteField.Preserved (fieldRegs reg) a :=
  ⟨h 18 (by decide), h 19 (by decide), h 20 (by decide), h 22 (by decide),
    h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide)⟩

/-- Run geometry and address selection, then check the entire resident field.
The mask remains zero exactly when the initial mask was zero and every bit
test at this system accepts. -/
theorem run [NeZero D] {M : Machine W p r k} {gpc : Fin 30 → Fin p} {apc : Fin 8 → Fin p}
    {fpc : Fin 15 → Fin p} {reg : Fin 32 ↪ Fin r} {done : Fin p}
    (hl : Linked M gpc apc fpc reg done) (v : Position D) (s : RAMSystem D)
    (hw : D < W) (hfit : ramFieldBits H w s < 2 ^ W) (c : Config W p r)
    (hc : c.pc = gpc (RouteGeometry.entry s)) {base : LocalPort → Word W} {buf : Buffers D H w}
    (h : Ready (H := H) (w := w) reg v s base c) (hres : Resident c base buf) :
    ∃ d, Prefix M c (List.replicate (ticks W v s (ramFieldBits H w s)) .tick) d ∧
      Result reg done v buf s c d := by
  obtain ⟨g, pre, geo⟩ := RouteGeometry.native hl.geometry v s hw c hc h.geometry
  have kept (i : Fin 32) (hi : 12 ≤ i.val) : g.reg (reg i) = c.reg (reg i) :=
    geo.frame _ (geometry_preserves reg i hi)
  let out := (systemMask s).val.testBit v.1.val
  let inc := (systemMask s).val.testBit ((finRotate D).symm v.1).val
  let off : Word W := (startOffset D H w s : Word W)
  have ha : RouteAddresses.Ready (addressRegs reg) g out inc
      (fun b ↦ base (.outgoing b)) (fun b ↦ base (.incoming b)) off :=
    ⟨geo.outgoing, geo.incoming,
      fun b ↦ (kept _ (by cases b <;> decide)).trans (h.outBase b),
      fun b ↦ (kept _ (by cases b <;> decide)).trans (h.inBase b),
      (kept 16 (by decide)).trans h.offset, (kept 17 (by decide)).trans h.zero⟩
  obtain ⟨a, ptrs, addr⟩ :=
    RouteAddresses.native hl.addresses (Nat.zero_le D |>.trans_lt hw) g geo.pc ha
  have akeep (i : Fin 32) (h₀ : i ≠ 18) (h₁ : i ≠ 19) (h₂ : i ≠ 20) :
      a.reg (reg i) = g.reg (reg i) :=
    addr.frame _ (fun he ↦ h₀ (reg.injective he)) (fun he ↦ h₁ (reg.injective he))
      (fun he ↦ h₂ (reg.injective he))
  have mode : a.reg (fieldRegs reg 4) = (RouteGeometry.mode v s : Word W) :=
    (akeep 7 (by decide) (by decide) (by decide)).trans geo.modeWord
  have mask : a.reg (fieldRegs reg 5) = c.reg (reg 22) :=
    (akeep 22 (by decide) (by decide) (by decide)).trans (kept 22 (by decide))
  have width : a.reg (fieldRegs reg 3) = (ramFieldBits H w s : Word W) :=
    (akeep 21 (by decide) (by decide) (by decide)).trans ((kept 21 (by decide)).trans h.width)
  have one : a.reg (fieldRegs reg 6) = 1 :=
    (akeep 23 (by decide) (by decide) (by decide)).trans ((kept 23 (by decide)).trans h.one)
  obtain ⟨d, scan, hd, _, _, _, hmask, frame, mem, per⟩ :=
    RouteField.run hl.field (ramFieldBits H w s) a addr.pc width one hfit
  rw [mode] at scan hmask
  have unused : a.reg (fieldRegs reg 0) = base (.outgoing (!out)) + off := addr.unused
  have used : a.reg (fieldRegs reg 1) = base (.outgoing out) + off := addr.used
  have incoming : a.reg (fieldRegs reg 2) = base (.incoming inc) + off := addr.incoming
  rw [unused, used, incoming, addr.memory, geo.memory, mask] at hmask
  refine ⟨d, ?_, hd, ?_, ?_, mem.trans (addr.memory.trans geo.memory),
    per.trans (addr.persistent.trans geo.persistent)⟩
  · rw [ticks, List.replicate_add, List.replicate_add]
    exact (pre.append ptrs).append scan
  · exact hmask.trans (and_congr_right' (agrees_iff_good v buf s c base hres hw))
  · intro x hx
    refine (frame x (field_preserves hx)).trans ((addr.frame x (hx 18 (by decide))
      (hx 19 (by decide)) (hx 20 (by decide))).trans (geo.frame x ?_))
    intro j hj
    apply hx (Fin.castLE (by decide) j)
    exact Or.inl ⟨hj, by change j.val ≤ 11; have := j.isLt; omega⟩

end PairSimulation.RouteCall

end VPVNP
end Computability
end OAI
