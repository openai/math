import OAI.Computability.VPVNP.CompressorRecordRefreshDirectory
import OAI.Computability.VPVNP.CompressorRecordRefreshTerms

/-!
# Native writes of the refreshed endpoint and width tables

Each visit takes a bundle (new site) number as its persistent cursor. The bundle
order is old base vertex, port, residual lane. At a fixed local slot, one call
writes the translated incoming identifier, the inverse link and the actual
width. The expander's two fixed columns are indexed by port and expander slot.
The selected supply widths are indexed by the full site and expander slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.NewSlots

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open Compression Compression.Refresh Compression.DegreeRefresh

variable {bits : ℕ}

/-- The fixed-width machine word used for refreshed slot addresses and widths. -/
abbrev W (bits : ℕ) := BurstRAM.Word bits
/-- The thirteen public words supplying dimensions, a local slot index, and the input and
output column heads. -/
abbrev Public (bits : ℕ) := Fin 13 → W bits

/-- The local index is zero for the external slot, an expander-edge number
for an internal slot, and a padding-copy number for a padding slot. -/
inductive Kind where | external | expander | padding

/-- Columns 10 and 11 map an outgoing identifier to its incoming identifier
and vice versa. Column 12 stores the width at the outgoing identifier. -/
structure Row (bits : ℕ) where
  /-- Packed outgoing slot identifier for this incidence row. -/
  src : W bits
  /-- Packed incoming slot identifier at the opposite end of this incidence row. -/
  dst : W bits
  /-- The word encoding the number of bits carried by the arc. -/
  width : W bits

/-- Write the two directed mate links and the outgoing width for the row. -/
def Row.update (p : Public bits) (m : Memory bits) (s : Row bits) : Memory bits :=
  writeMemory (writeMemory (writeMemory m (p 10 + s.src) s.dst) (p 11 + s.dst) s.src)
    (p 12 + s.src) s.width

/-- Read the dimensions, target/total arrays, fixed expander and selected supply
tables. Arithmetic is word arithmetic, including the cyclic padding rotation. -/
def row (kind : Kind) (p : Public bits) (m : Memory bits) (b : W bits) : Row bits :=
  let base := BinaryOp.div.eval b (p 3)
  let j := BinaryOp.mod.eval base (p 0)
  let vertex := BinaryOp.div.eval base (p 0)
  let lane := BinaryOp.mod.eval b (p 3)
  let site := fun t => (vertex * p 0 + t) * p 3 + lane
  match kind with
  | .external => ⟨b * p 2, m (p 5 + b).val * p 2, m (p 6 + b).val⟩
  | .expander =>
    let e := j * p 1 + p 4
    let t := m (p 7 + e).val
    let h := m (p 8 + e).val
    ⟨b * p 2 + (p 4 + 1), site t * p 2 + (h + 1), m (p 9 + (b * p 1 + p 4)).val⟩
  | .padding =>
    let k := p 1 + p 4 + 1
    ⟨b * p 2 + k, site (BinaryOp.mod.eval (j + 1) (p 0)) * p 2 + k, 0⟩

/-- Load the base vertex (register 4), port (5), and lane (6) from the site cursor. -/
private def decode : List (Op 12 13) :=
  [.stateWord 0, .publicWord 7 3, .binary .div 4 0 7, .binary .mod 6 0 7,
    .publicWord 8 0, .binary .mod 5 4 8, .binary .div 4 4 8, .binary .mul 4 4 8]

/-- Register 5 now carries the target port. Restore the target site (register 2)
while preserving the lane. -/
private def restore : List (Op 12 13) :=
  [.binary .add 2 4 5, .binary .mul 2 2 7, .binary .add 2 2 6]

private def prepare : Kind → List (Op 12 13)
  | .external =>
    [.stateWord 0, .publicWord 4 5, .binary .add 4 4 0, .read 2 4,
      .publicWord 4 6, .binary .add 4 4 0, .read 3 4, .publicWord 4 2,
      .binary .mul 1 0 4, .binary .mul 2 2 4]
  | .expander =>
    decode ++ [.publicWord 9 1, .publicWord 10 4, .binary .mul 11 5 9,
      .binary .add 11 11 10, .publicWord 3 7, .binary .add 3 3 11, .read 5 3,
      .publicWord 3 8, .binary .add 3 3 11, .read 11 3] ++ restore ++
    [.binary .mul 3 0 9, .binary .add 3 3 10, .publicWord 4 9, .binary .add 4 4 3,
      .read 3 4, .constant 6 1, .binary .add 10 10 6, .binary .add 11 11 6,
      .publicWord 4 2, .binary .mul 1 0 4, .binary .add 1 1 10,
      .binary .mul 2 2 4, .binary .add 2 2 11]
  | .padding =>
    decode ++ [.constant 9 1, .binary .add 5 5 9, .binary .mod 5 5 8] ++ restore ++
    [.publicWord 10 1, .publicWord 11 4, .binary .add 10 10 11, .binary .add 10 10 9,
      .publicWord 4 2, .binary .mul 1 0 4, .binary .add 1 1 10,
      .binary .mul 2 2 4, .binary .add 2 2 10, .constant 3 0]

/-- Fixed tables of instructions. Public words 0–4 give the port count,
expander degree, new degree, residual lane count and the local copy index.
Words 5–9 give bases of the external target, external total, expander target
port, expander reverse slot and selected supply width arrays. Words 10–12
locate the forward link, inverse link and width arrays. -/
def code (kind : Kind) : List (Op 12 13) :=
  prepare kind ++ [.publicWord 4 10, .binary .add 4 4 1, .write 4 2,
    .publicWord 4 11, .binary .add 4 4 2, .write 4 1,
    .publicWord 4 12, .binary .add 4 4 1, .write 4 3, .constant 4 1, .binary .add 0 0 4]

private def ticks (n : ℕ) : List (Event bits) := List.replicate n .tick

/-- The native read and write events for one external, expander, or padding slot at the current
site. -/
def events (kind : Kind) (p : Public bits) (m : Memory bits) (b : W bits) : List (Event bits) :=
  let read := fun a : W bits => Event.read a (m a.val)
  let before := match kind with
    | .external => ticks 3 ++ [read (p 5 + b)] ++ ticks 2 ++ [read (p 6 + b)] ++ ticks 3
    | .expander =>
      let j := BinaryOp.mod.eval (BinaryOp.div.eval b (p 3)) (p 0)
      let e := j * p 1 + p 4
      ticks 14 ++ [read (p 7 + e)] ++ ticks 2 ++ [read (p 8 + e)] ++ ticks 7 ++
        [read (p 9 + (b * p 1 + p 4))] ++ ticks 8
    | .padding => ticks 24
  let s := row kind p m b
  before ++ ticks 2 ++ [.write (p 10 + s.src) s.dst] ++ ticks 2 ++
    [.write (p 11 + s.dst) s.src] ++ ticks 2 ++ [.write (p 12 + s.src) s.width] ++ ticks 2

theorem events_work (kind : Kind) (p : Public bits) (m : Memory bits) (b : W bits) :
    (events kind p m b).length = (match kind with | .external => 21 | .expander => 45 | .padding => 35) ∧
    countProbes (events kind p m b) = (match kind with | .external => 5 | .expander => 6 | .padding => 3) := by
  cases kind <;> simp [events, countProbes, ticks]

theorem events_after (kind : Kind) (p : Public bits) (m : Memory bits) (b : W bits) :
    after m (events kind p m b) = (row kind p m b).update p m := by
  cases kind <;> rfl

set_option maxRecDepth 8192 in
private theorem code_trace (kind : Kind) (p : Public bits) (m : Memory bits)
    (b : W bits) (regs : Regs bits 12) :
    ∃ rs, trace p b (code kind) regs m =
      some (events kind p m b, rs, (row kind p m b).update p m) ∧ rs 0 = b + 1 := by
  cases kind <;>
    simp (config := {decide := true}) [code, prepare, decode, restore, trace, Op.effect,
      row, Row.update, events, ticks, BinaryOp.eval, Function.update] <;> repeat' constructor

/-- One native call from fresh private memory, including its full event sequence. -/
theorem native (kind : Kind) (p : Public bits) (m : Memory bits) (b : W bits) :
    let M := (template (code kind) 0).instantiate bits p
    execute M.program (1 + (code kind).length) (M.program.start b) m [] =
      some ⟨events kind p m b, some (b + 1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := code_trace kind p m b (fun _ => 0)
  let M := (template (code kind) 0).instantiate bits p
  change execute M.program (1 + (code kind).length) ⟨M.entry,b,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hr]

/-- Read back the two endpoint links and the width after this native call.
The inequalities separate the three actual output cells, including at loops
of the numerical permutation. -/
theorem written (kind : Kind) (p : Public bits) (m : Memory bits) (b : W bits)
    (oi : p 10 + (row kind p m b).src ≠ p 11 + (row kind p m b).dst)
    (ow : p 10 + (row kind p m b).src ≠ p 12 + (row kind p m b).src)
    (iw : p 11 + (row kind p m b).dst ≠ p 12 + (row kind p m b).src) :
    let s := row kind p m b
    let m' := after m (events kind p m b)
    m' (p 10 + s.src).val = s.dst ∧ m' (p 11 + s.dst).val = s.src ∧ m' (p 12 + s.src).val = s.width := by
  dsimp only
  rw [events_after]
  simp [Row.update, writeMemory, Fin.val_inj, oi, ow, iw]

section Graph

variable {V H L : Type} {n r D dH d₀ : ℕ}
variable (vertices : V ≃ Fin n) (lanes : L ≃ Fin r)

/-- The external directory enumerates the base arc before the residual lane. -/
def sites : (V × L) × Fin D ≃ Fin (n * D * r) :=
  let base := (vertices.prodCongr (Equiv.refl (Fin D))).trans finProdFinEquiv
  promotedSites.trans ((base.prodCongr lanes).trans finProdFinEquiv)

/-- The endpoint identifiers range bijectively over the refreshed half-slots. -/
def arcs : ActualArc V L D d₀ ≃ Fin (n * D * r * d₀) :=
  let site := promotedSites.symm.trans (sites (D := D) vertices lanes)
  (site.prodCongr (Equiv.refl _)).trans finProdFinEquiv

theorem sites_val (s : (V × L) × Fin D) :
    (sites vertices lanes s).val =
      ((vertices s.1.1).val * D + s.2.val) * r + (lanes s.1.2).val := by
  change (lanes s.1.2).val + r * (s.2.val + D * (vertices s.1.1).val) = _
  ring

theorem arcs_val (s : (V × L) × Fin D) (k : Fin d₀) :
    (arcs vertices lanes (promotedSites s,k)).val = (sites vertices lanes s).val * d₀ + k.val := by
  change k.val + d₀ * (sites vertices lanes s).val = _
  ring

/-- Embed a numerical array index into a word. -/
abbrev word (a : ℕ) : W bits := Fin.ofNat _ a

/-- With product-order base slots, the binary directory and new slots have
identical site numbers. -/
theorem bundleOrder_sites (a g : ℕ) :
    bundleOrder g ((vertices.prodCongr (Equiv.refl (Fin (2^a)))).trans finProdFinEquiv) =
      sites vertices (bitWordFinEquiv g) := by
  ext x
  rfl

private theorem add_word (a b : ℕ) : word a + word b = word (bits := bits) (a+b) :=
  Fin.ext (Nat.add_mod a b (2 ^ bits)).symm

private theorem mul_word (a b : ℕ) : word a * word b = word (bits := bits) (a*b) :=
  Fin.ext (Nat.mul_mod a b (2 ^ bits)).symm

private theorem unit_word (a : ℕ) : word a + 1 = word (bits := bits) (a+1) := add_word a 1

private theorem asWord (x : W bits) : x = word x.val :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

private theorem div_mod_pack (x stride : W bits) {q d u : ℕ}
    (h : x.val = q * d + u) (hs : stride.val = d) (hu : u < d) :
    BinaryOp.div.eval x stride = word q ∧ BinaryOp.mod.eval x stride = word u := by
  have hd : 0 < d := Nat.zero_lt_of_lt hu
  constructor <;> apply Fin.ext
  · change (x.val / stride.val) % _ = q % _
    rw [h, hs, Nat.mul_comm q, Nat.mul_add_div hd, Nat.div_eq_of_lt hu, Nat.add_zero]
  · change (x.val % stride.val) % _ = u % _
    rw [h, hs, Nat.mul_add_mod_of_lt hu]

/-- Public constants common to the three scans. The whole interval of output
half-slot identifiers fits in the address word. -/
structure Dimensions (p : Public bits) (n D r dH d₀ : ℕ) : Prop where
  ports : (p 0).val = D
  expander : (p 1).val = dH
  degree : (p 2).val = d₀
  lanes : (p 3).val = r
  fits : n * D * r * d₀ ≤ 2 ^ bits

variable {p : Public bits} {m : Memory bits}
variable (hD : 1 < D) (hd : dH + 1 ≤ d₀) (dim : Dimensions p n D r dH d₀)

include hd dim in
private theorem decode_exact (s : (V × L) × Fin D) :
    let b := word (bits := bits) (sites vertices lanes s).val
    let base := BinaryOp.div.eval b (p 3)
    BinaryOp.div.eval base (p 0) = word (vertices s.1.1).val ∧
      BinaryOp.mod.eval base (p 0) = word s.2.val ∧
      BinaryOp.mod.eval b (p 3) = word (lanes s.1.2).val := by
  let v := (vertices s.1.1).val
  let l := (lanes s.1.2).val
  have hl : l < r := (lanes s.1.2).isLt
  have hfit := (sites vertices lanes s).isLt.trans_le
    ((Nat.le_mul_of_pos_right (n*D*r) (by omega : 0 < d₀)).trans dim.fits)
  have hq : v * D + s.2.val < 2 ^ bits := by
    have hle := Nat.le_mul_of_pos_right (v * D + s.2.val) (Nat.zero_lt_of_lt hl)
    rw [sites_val] at hfit
    dsimp [v] at hle ⊢
    omega
  have hval : (word (bits := bits) (sites vertices lanes s).val).val = (v * D + s.2.val) * r + l :=
    (Nat.mod_eq_of_lt hfit).trans (sites_val vertices lanes s)
  obtain ⟨hb,hlane⟩ := div_mod_pack _ _ hval dim.lanes hl
  obtain ⟨hv,hj⟩ := div_mod_pack (word (bits := bits) (v * D + s.2.val)) (p 0)
    (Nat.mod_eq_of_lt hq) dim.ports s.2.isLt
  exact ⟨hb ▸ hv, hb ▸ hj, hlane⟩

private theorem extNumber (hd : dH + 1 ≤ d₀) :
    (refreshSlots hd (.inl 0)).val = 0 := rfl

private theorem expNumber (hd : dH + 1 ≤ d₀) (k : Fin dH) :
    (refreshSlots hd (.inr (.inl k))).val = k.val + 1 := by
  change 1 + k.val = k.val + 1
  omega

private theorem padNumber (hd : dH + 1 ≤ d₀) (k : Fin (d₀-(dH+1))) :
    (refreshSlots hd (.inr (.inr k))).val = dH + k.val + 1 := by
  change 1 + (dH + k.val) = _
  omega

private theorem rotate_word (j : Fin D) (degree : W bits) (hdeg : degree.val = D) :
    BinaryOp.mod.eval (word j.val + 1) degree = word (finRotate D j).val := by
  have room := hdeg ▸ degree.isLt
  have hj : j.val + 1 < 2 ^ bits := (Nat.succ_le_of_lt j.isLt).trans_lt room
  let := j.neZero
  apply Fin.ext
  change ((word j.val + 1 : W bits).val % degree.val) % _ = (finRotate D j).val % _
  rw [unit_word, show (word (bits := bits) (j.val+1)).val = j.val+1 from Nat.mod_eq_of_lt hj, hdeg,
    finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- Equality with the numbered graph record before writing the three cells. -/
def Represents (s : Row bits) (record : NewSlot V L D d₀) : Prop :=
  s.src.val = (arcs vertices lanes record.src).val ∧
    s.dst.val = (arcs vertices lanes record.dst).val ∧ s.width.val = record.width

private theorem represents_of_words {s : Row bits} {record : NewSlot V L D d₀}
    (src : s.src = word (arcs vertices lanes record.src).val)
    (dst : s.dst = word (arcs vertices lanes record.dst).val) (width : s.width.val = record.width)
    (fit : n * D * r * d₀ ≤ 2 ^ bits) : Represents vertices lanes s record := by
  rw [Represents,src,dst]
  exact ⟨Nat.mod_eq_of_lt ((arcs vertices lanes record.src).isLt.trans_le fit),
    Nat.mod_eq_of_lt ((arcs vertices lanes record.dst).isLt.trans_le fit), width⟩

variable [AddCommGroup L] (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D)
  (width : (V × Fin D) × (H × L) → ℕ) (P : SlotGraph (Fin D) dH)
  (internal : V × L → Fin D × Fin dH → ℕ)

include dim

/-- The translated target directory and the computed prefix total are the two
input words of the external-slot visit. -/
theorem external_record (s : (V × L) × Fin D)
    (target : (m (p 5 + word (sites vertices lanes s).val).val).val = (sites vertices lanes (bundleTarget G s)).val)
    (total : (m (p 6 + word (sites vertices lanes s).val).val).val = ∑ j, bundleWidths port width s j) :
    Represents vertices lanes (row .external p m (word (sites vertices lanes s).val))
      (slotRecord G port width P hd internal s (.inl 0)) := by
  have hg := (asWord (p 2)).trans (congrArg word dim.degree)
  have ht := (asWord (m (p 5 + word (sites vertices lanes s).val).val)).trans (congrArg word target)
  apply represents_of_words vertices lanes _ _ total dim.fits
  · simp only [row,slotRecord,arcs_val,extNumber,Nat.add_zero,hg,mul_word]
  · simp only [row,slotRecord,arcs_val,extNumber,Nat.add_zero,ht,hg,mul_word]

/-- A RAM visit reads the matching reverse port and reverse slot from the fixed
expander, and the selected width from the current term's supply table. -/
theorem expander_record (s : (V × L) × Fin D) (k : Fin dH) (hk : (p 4).val = k.val)
    (t : (m (p 7 + word (s.2.val * dH + k.val)).val).val = (P.target (s.2,k)).1.val)
    (u : (m (p 8 + word (s.2.val * dH + k.val)).val).val = (P.target (s.2,k)).2.val)
    (supply : (m (p 9 + word ((sites vertices lanes s).val * dH + k.val)).val).val = internal s.1 (s.2,k)) :
    Represents vertices lanes (row .expander p m (word (sites vertices lanes s).val))
      (slotRecord G port width P hd internal s (.inr (.inl k))) := by
  obtain ⟨hv,hj,hl⟩ := decode_exact vertices lanes hd dim s
  have h0 := (asWord (p 0)).trans (congrArg word dim.ports)
  have h1 := (asWord (p 1)).trans (congrArg word dim.expander)
  have h2 := (asWord (p 2)).trans (congrArg word dim.degree)
  have h3 := (asWord (p 3)).trans (congrArg word dim.lanes)
  have h4 := (asWord (p 4)).trans (congrArg word hk)
  have ht := (asWord (m (p 7 + word (s.2.val * dH + k.val)).val)).trans (congrArg word t)
  have hu := (asWord (m (p 8 + word (s.2.val * dH + k.val)).val)).trans (congrArg word u)
  apply represents_of_words vertices lanes _ _ _ dim.fits
  · simp only [row,slotRecord,arcs_val,expNumber,h2,h4,unit_word,mul_word,add_word]
  · simp only [row,slotRecord,arcs_val,expNumber,hv,hj,hl]
    simp only [h0,h1,h2,h3,h4,mul_word,add_word,ht,hu,unit_word,sites_val]
  · simpa only [row,slotRecord,h1,h4,mul_word,add_word] using supply

/-- Padding preserves the local copy number, advances the port modulo the old
degree at the same vertex and lane, and emits the zero-width row. -/
theorem padding_record (s : (V × L) × Fin D) (k : Fin (d₀-(dH+1))) (hk : (p 4).val = k.val) :
    Represents vertices lanes (row .padding p m (word (sites vertices lanes s).val))
      (slotRecord G port width P hd internal s (.inr (.inr k))) := by
  obtain ⟨hv,hj,hl⟩ := decode_exact vertices lanes hd dim s
  have h0 := (asWord (p 0)).trans (congrArg word dim.ports)
  have h1 := (asWord (p 1)).trans (congrArg word dim.expander)
  have h2 := (asWord (p 2)).trans (congrArg word dim.degree)
  have h3 := (asWord (p 3)).trans (congrArg word dim.lanes)
  have h4 := (asWord (p 4)).trans (congrArg word hk)
  have hrot := rotate_word s.2 (p 0) dim.ports
  apply represents_of_words vertices lanes _ _ rfl dim.fits
  · simp only [row,slotRecord,arcs_val,padNumber,h1,h2,h4,mul_word,add_word,unit_word]
  · simp only [row,slotRecord,arcs_val,padNumber,hv,hj,hl,hrot]
    simp only [h0,h1,h2,h3,h4,mul_word,add_word,unit_word,sites_val]

omit dim

/-- The identifiers stored by any of the three verified visits give precisely
the actual matching and width, including the incoming slot number. -/
theorem actual_record (s : (V × L) × Fin D) (k : RefreshSlot dH d₀) (out : Row bits)
    (ok : Represents vertices lanes out (slotRecord G port width P hd internal s k)) :
    let src := (promotedSites s, refreshSlots hd k)
    out.src.val = (arcs vertices lanes src).val ∧
      out.dst.val = (arcs vertices lanes ((degreeRefresh G P hD hd).actualGraph.target src)).val ∧
      out.width.val = actualWidths hd port width internal ((src.1.1,src.2),src.1.2) := by
  obtain ⟨hs,ht,hw⟩ := slotRecord_spec G port width P hD hd internal s k
  obtain ⟨ha,hb,hc⟩ := ok
  rw [hs] at ha ht hw
  exact ⟨ha,hb.trans (congrArg (fun x => (arcs vertices lanes x).val) ht.symm),hc.trans hw.symm⟩

open MotifGrid MotifBlocks MotifConversion SpectralGeometry

variable [AddCommGroup H] {K : Type*} [_root_.Field K] {c₁ c₂ : ℝ}
  (E : RegularArcGraph (Fin D) dH) (hdH : 0 < dH) (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : FixedBlock K tieSource tieTarget (expanderSupply E hdH conn)
    (realWidths tieMass) (realWidths (expanderMass d₀)) c₁ c₂)

include dim in
/-- The expander visit applies also to the explicit supply lengths of a
term admitted by the block reader, including its selector fields. -/
theorem chosen_expander_record (c : BlockChoices G port width E hdH conn F)
    (s : (V × L) × Fin D) (k : Fin dH) (hk : (p 4).val = k.val)
    (t : (m (p 7 + word (s.2.val * dH + k.val)).val).val = (E.reverse (s.2,k)).1.val)
    (u : (m (p 8 + word (s.2.val * dH + k.val)).val).val = (E.reverse (s.2,k)).2.val)
    (supply : (m (p 9 + word ((sites vertices lanes s).val * dH + k.val)).val).val =
      supplyWidths F (fun t => (demandRecord G port width s.1 t).width) (c s.1).val (s.2,k)) :
    Represents vertices lanes (row .expander p m (word (sites vertices lanes s).val))
      (slotRecord G port width E.toSlotGraph hd (blockSupplyWidths G port width E hdH conn F c)
        s (.inr (.inl k))) := by
  apply expander_record vertices lanes hd dim G port width E.toSlotGraph _ s k hk t u
  exact supply.trans (chosen_supply_record G port width E hdH conn F hd c s.1 (s.2,k)).2.2.symm

omit [AddCommGroup H] in
/-- The two input words of the external-slot writer come directly from the
terminal memory of the external segment pass. -/
theorem external_terminal_record {a : ℕ} (X : LiftedSlots V (2^a) (BitWord a × L))
    (w : (V × Fin (2^a)) × (BitWord a × L) → ℕ) (E : SlotGraph (Fin (2^a)) dH)
    (int : V × L → Fin (2^a) × Fin dH → ℕ) (q : Fin 8 → W bits) (A : RefreshRAM.Input bits)
    (fit : n * 2^a * r * 2^a ≤ 2^bits) (sizes : Dimensions p n (2^a) r dH d₀)
    (dir : Directory X (sites vertices lanes) w q A fit)
    (done : RefreshRAM.AtCursor q (n * 2^a * r * 2^a) A m (n * 2^a * r * 2^a))
    (targetBase : p 5 = q 2) (totalBase : p 6 = q 4)
    (s : (V × L) × Fin (2^a))
    (total : (RefreshRAM.cell q m 4 (bundleWord (sites vertices lanes) fit s)).val =
      ∑ j, bundleWidths (bitWordFinEquiv a) w s j) :
    Represents vertices lanes (row .external p m (word (sites vertices lanes s).val))
      (slotRecord X (bitWordFinEquiv a) w E hd int s (.inl 0)) := by
  let ord := sites (D := 2^a) vertices lanes
  have idx : word (bits := bits) (ord s).val = bundleWord ord fit s :=
    (asWord (bundleWord ord fit s)).symm
  have ht := (congrArg Fin.val (done.target _ (bundleWord_live ord q (fit := fit) dir.degree s))).trans (dir.target s)
  apply external_record vertices lanes hd sizes X (bitWordFinEquiv a) w E int s
  · change (m (p 5 + word (ord s).val).val).val = _
    rw [idx,targetBase]
    exact ht
  · change (m (p 6 + word (ord s).val).val).val = _
    rw [idx,totalBase]
    exact total

end Graph


/-- The three output words of a visit. -/
inductive Column where | outgoing | incoming | width

/-- Select a row's write address, indexing the incoming column by destination and the other two
by source. -/
def Row.address (s : Row bits) (p : Public bits) : Column → W bits
  | .outgoing => p 10 + s.src
  | .incoming => p 11 + s.dst
  | .width => p 12 + s.src

/-- Select the row value to store in the outgoing-mate, incoming-mate, or width column. -/
def Row.value (s : Row bits) : Column → W bits
  | .outgoing => s.dst
  | .incoming => s.src
  | .width => s.width

/-- All read addresses are determined by the cursor and the public words. -/
def inputs (kind : Kind) (p : Public bits) (b : W bits) : List (W bits) :=
  match kind with
  | .external => [p 5 + b, p 6 + b]
  | .expander =>
    let j := BinaryOp.mod.eval (BinaryOp.div.eval b (p 3)) (p 0)
    let e := j * p 1 + p 4
    [p 7 + e, p 8 + e, p 9 + (b * p 1 + p 4)]
  | .padding => []

private theorem row_congr (kind : Kind) (p : Public bits) (b : W bits) {m ref : Memory bits}
    (reads : ∀ a ∈ inputs kind p b, m a.val = ref a.val) : row kind p m b = row kind p ref b := by
  cases kind <;> simp [inputs] at reads
  · simp only [row,reads.1,reads.2]
  · simp only [row,reads.1,reads.2.1,reads.2.2]
  · rfl

private theorem update_miss (s : Row bits) (p : Public bits) (m : Memory bits) (a : ℕ)
    (miss : ∀ c, a ≠ (s.address p c).val) : s.update p m a = m a := by
  have ho := miss .outgoing
  have hi := miss .incoming
  have hw := miss .width
  simp only [Row.address] at ho hi hw
  simp [Row.update,writeMemory,ho,hi,hw]

private theorem update_hit (s : Row bits) (p : Public bits) (m : Memory bits)
    (inj : Function.Injective (s.address p)) (c : Column) :
    s.update p m (s.address p c).val = s.value c := by
  have oi : s.address p .outgoing ≠ s.address p .incoming := fun h => Column.noConfusion (inj h)
  have ow : s.address p .outgoing ≠ s.address p .width := fun h => Column.noConfusion (inj h)
  have iw : s.address p .incoming ≠ s.address p .width := fun h => Column.noConfusion (inj h)
  simp only [Row.address] at oi ow iw
  cases c <;> simp [Row.address,Row.value,Row.update,writeMemory,Fin.val_inj,oi,ow,iw]

section Pass

variable {N : ℕ} (kind : Kind) (p : Public bits) (ref : Memory bits)

/-- Expected record at a source site, calculated in the input memory. -/
abbrev expected (i : Fin N) : Row bits := row kind p ref (word i.val)

/-- Output words of different rows and columns have distinct addresses. They
are disjoint from all inputs of the pass. -/
structure PassLayout (N : ℕ) : Prop where
  reads : ∀ (i j : Fin N) c a, a ∈ inputs kind p (word i.val) →
    a ≠ (expected kind p ref j).address p c
  writes : ∀ (i j : Fin N) c d,
    (expected kind p ref i).address p c = (expected kind p ref j).address p d → i = j ∧ c = d

/-- Every visited row is complete. Every memory word outside the visited
output cells has its original value, including words beyond the RAM range. -/
structure Prefix (N : ℕ) (m : Memory bits) (k : ℕ) : Prop where
  rows : ∀ (i : Fin N), i.val < k → ∀ c,
    m ((expected kind p ref i).address p c).val = (expected kind p ref i).value c
  frame : ∀ a, (∀ (i : Fin N), i.val < k → ∀ c, a ≠ ((expected kind p ref i).address p c).val) → m a = ref a

private theorem prefix_step (L : PassLayout kind p ref N) {m : Memory bits} {k : ℕ}
    (cur : Prefix kind p ref N m k) (hk : k < N) :
    Prefix kind p ref N ((row kind p m (word k)).update p m) (k+1) := by
  let j : Fin N := ⟨k,hk⟩
  have same : row kind p m (word k) = expected kind p ref j := by
    apply row_congr
    intro a ha
    exact cur.frame a.val (fun i _ c he => L.reads j i c a ha (Fin.ext he))
  rw [same]
  constructor
  · intro i hi c
    by_cases eq : i = j
    · subst i
      exact update_hit _ p m (fun c d h => (L.writes j j c d h).2) c
    · have ne : i.val ≠ k := fun h => eq (Fin.ext h)
      rw [update_miss _ p m _ (fun d h => eq (L.writes i j c d (Fin.ext h)).1)]
      exact cur.rows i (by omega) c
  · intro a ha
    rw [update_miss _ p m _ (ha j (Nat.lt_succ_self k))]
    exact cur.frame a (fun i hi => ha i (hi.trans (Nat.lt_succ_self k)))

/-- Probe count of a native visit, before adding its call boundary. -/
def probeCount : Kind → ℕ
  | .external => 5
  | .expander => 6
  | .padding => 3

/-- Choose the native table for each slot class. -/
def kindOf {dH d₀ : ℕ} : RefreshSlot dH d₀ → Kind
  | .inl _ => .external
  | .inr (.inl _) => .expander
  | .inr (.inr _) => .padding

/-- Summing the full-pass costs over the numbered local slots counts each
expander and each padding copy separately. -/
theorem slot_cost {dH d₀ : ℕ} (hd : dH+1 ≤ d₀) (N : ℕ) :
    ∑ k : Fin d₀, (1 + probeCount (kindOf ((refreshSlots hd).symm k))) * N =
      (6 + 7*dH + 4*(d₀-(dH+1))) * N := by
  rw [← (refreshSlots hd).sum_comp]
  simp only [Equiv.symm_apply_apply,Fintype.sum_sum_type,kindOf,probeCount,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

/-- All calls for one fixed local slot, starting at any already completed prefix. -/
theorem scan_run (layout : PassLayout kind p ref N) (m : Memory bits) (k calls : ℕ)
    (cur : Prefix kind p ref N m k) (room : k + calls ≤ N) :
    let M := (template (code kind) 0).instantiate bits p
    ∃ rs, runSegment M.program (1 + (code kind).length) (some (word k)) m (List.replicate calls []) = some rs ∧
      Prefix kind p ref N (after m (eventLog rs)) (k + calls) ∧ rs.length = calls ∧
      RAMBuckets.cost (fun r : Report bits => countProbes r.events) rs = (1 + probeCount kind) * calls := by
  let M := (template (code kind) 0).instantiate bits p
  induction calls generalizing k m with
  | zero => exact ⟨[],rfl,cur,rfl,by simp [RAMBuckets.cost]⟩
  | succ t ih =>
    let i := word (bits := bits) k
    let r : Report bits := ⟨events kind p m i, some (i+1)⟩
    have next := prefix_step kind p ref layout cur (by omega)
    obtain ⟨rs,hr,hc,hl,hw⟩ := ih _ (k+1) next (by omega)
    have hm : after m (eventLog (r :: rs)) = after ((row kind p m i).update p m) (eventLog rs) := by
      change List.foldl BurstRAM.update m (events kind p m i ++ eventLog rs) = _
      rw [List.foldl_append]
      change after (after m (events kind p m i)) (eventLog rs) = _
      rw [events_after]
    refine ⟨r :: rs, ?_, ?_, by simp [hl], ?_⟩
    · change runSegment M.program _ (some i) m (List.replicate (t+1) []) = _
      rw [List.replicate_succ,runSegment,native]
      simp only [M,r,i,events_after,unit_word,hr,Option.map_some]
    · simpa only [hm,Nat.add_assoc,Nat.add_comm 1 t] using hc
    · have hprobe : countProbes r.events = probeCount kind := (events_work kind p m i).2
      rw [RAMBuckets.cost,hprobe,hw,Nat.mul_succ,Nat.add_comm]

/-- From arbitrary initial memory, one complete native pass produces all
forward and inverse links and widths for its slot and preserves every other
cell. This costs six, seven or four per site, according to the slot class. -/
theorem full_pass (layout : PassLayout kind p ref N) :
    let M := (template (code kind) 0).instantiate bits p
    ∃ rs, runSegment M.program (1 + (code kind).length) (some 0) ref (List.replicate N []) = some rs ∧
      Prefix kind p ref N (after ref (eventLog rs)) N ∧ rs.length = N ∧
      RAMBuckets.cost (fun r : Report bits => countProbes r.events) rs = (1 + probeCount kind) * N := by
  have zero : word (bits := bits) 0 = 0 := Fin.ext (by simp [word])
  simpa only [Nat.zero_add,zero] using scan_run kind p ref layout ref 0 N
    ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩ (by simp)

end Pass


section ActualPass

variable {V H L : Type} {n r D dH d₀ : ℕ} [AddCommGroup L]
variable (vertices : V ≃ Fin n) (lanes : L ≃ Fin r)
variable (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D)
  (width : (V × Fin D) × (H × L) → ℕ) (P : SlotGraph (Fin D) dH)
  (internal : V × L → Fin D × Fin dH → ℕ) (hD : 1 < D) (hd : dH + 1 ≤ d₀)
  (kind : Kind) (p : Public bits) (ref : Memory bits)

include hD in
/-- For a fixed local slot, injectivity within each physical column follows
from the permutation of actual lifted half-slots. This also covers parallel
expander edges. Only the separation of input and output arrays and of distinct
output columns needs to be supplied by the address layout. -/
theorem PassLayout.ofActual (k : RefreshSlot dH d₀)
    (rows : ∀ i : Fin (n * D * r), Represents vertices lanes (expected kind p ref i)
      (slotRecord G port width P hd internal ((sites vertices lanes).symm i) k))
    (reads : ∀ (i j : Fin (n * D * r)) c a, a ∈ inputs kind p (word i.val) →
      a ≠ (expected kind p ref j).address p c)
    (columns : ∀ (i j : Fin (n * D * r)) c d, c ≠ d →
      (expected kind p ref i).address p c ≠ (expected kind p ref j).address p d) :
    PassLayout kind p ref (n * D * r) := by
  let src := fun i : Fin (n * D * r) => (promotedSites ((sites vertices lanes).symm i),refreshSlots hd k)
  have si : Function.Injective src := fun _ _ h =>
    (sites vertices lanes).symm.injective (promotedSites.injective (congrArg Prod.fst h))
  have ids := fun i => actual_record vertices lanes hD hd G port width P internal
    ((sites vertices lanes).symm i) k (expected kind p ref i) (rows i)
  have outgoing : Function.Injective (fun i : Fin (n*D*r) => (expected kind p ref i).src) := by
    intro i j he
    apply si
    apply (arcs vertices lanes).injective
    exact Fin.ext ((ids i).1.symm.trans ((congrArg Fin.val he).trans (ids j).1))
  have incoming : Function.Injective (fun i : Fin (n*D*r) => (expected kind p ref i).dst) := by
    intro i j he
    apply si
    apply (degreeRefresh G P hD hd).actualGraph.target.injective
    apply (arcs vertices lanes).injective
    exact Fin.ext ((ids i).2.1.symm.trans ((congrArg Fin.val he).trans (ids j).2.1))
  refine ⟨reads,fun i j c d he => ?_⟩
  have hcd : c = d := by_contra fun h => columns i j c d h he
  subst d
  refine ⟨?_,rfl⟩
  cases c with
  | outgoing | width => exact outgoing (add_left_cancel he)
  | incoming => exact incoming (add_left_cancel he)

end ActualPass

end CompressorRecords.PortRefresh.NewSlots

end VPVNP
end Computability
end OAI
