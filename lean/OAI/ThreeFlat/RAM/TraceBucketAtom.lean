import OAI.ThreeFlat.RAM.TraceBucketLayout
import OAI.ThreeFlat.RAM.TraceBucketFields
import OAI.ThreeFlat.RAM.TraceOwnerNative
import OAI.ThreeFlat.Diagonal.TraceBucketRelayExpr

namespace OAI
/-! # The fixed native emitter for one physical four-word initial atom -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing

/-- Registers are row number within the atom, word number in its
four-word record, lane ordinal, and cursor stage. -/
private abbrev E (W : ℕ) := Term W 1 4
private abbrev lit {W : ℕ} (n : ℕ) : E W := .literal n
private abbrev reg {W : ℕ} (i : Fin 4) : E W := .result i
private abbrev plus {W : ℕ} := @Term.binary W 1 4 .add
private abbrev times {W : ℕ} := @Term.binary W 1 4 .mul
private abbrev sub {W : ℕ} := @Term.binary W 1 4 .sub
private abbrev quot {W : ℕ} := @Term.binary W 1 4 .div
private abbrev modulo {W : ℕ} := @Term.binary W 1 4 .mod

def laneBase {W : ℕ} (s : Layout) : E W := times (reg 2) (lit s.lowRows)
def pinStart {W : ℕ} (s : Layout) : E W := times (laneBase s) (lit 2)
def ext {W : ℕ} (s : Layout) : E W :=
  let start :=  pinStart s
  let extent := lit (2*s.lowRows)
  .select .lt (lit s.shape.header) start (lit 0)
    (.select .lt (lit s.shape.header) (plus start extent) (sub (lit s.shape.header) start) extent)

def raw {W : ℕ} (s : Layout) (site slot leg : E W) : E W :=
  .load (plus (plus (lit s.records) (times (lit 11) (plus (times site (lit s.slots)) slot))) leg)

def origArgs {W : ℕ} (s : Layout) : Fin 13 → E W :=
  let i := sub (reg 0) (lit s.relays)
  let slot := modulo i (lit s.slots)
  let site := plus (laneBase s) (quot i (lit s.slots))
  let source := raw s site slot (reg 1)
  ![reg 1,source,TraceOwnerFormula.direct .owner s.shape 1 source site,site,lit s.slots,
    slot,lit s.lowRows,ext s,lit s.tags,lit s.bank,lit (2^(s.depth-1)),lit s.dictionary,lit s.tableIds]

def cmpArgs {W : ℕ} (s : Layout) : Fin 15 → E W :=
  let t := sub (reg 0) (lit (s.relays+s.gates))
  let o := quot t (lit s.per)
  let low := modulo (quot t (lit (s.slots*3))) (lit s.lowRows)
  let slot := modulo (quot t (lit 3)) (lit s.slots)
  let leg := modulo t (lit 3)
  let own := plus (laneBase s) low
  let mask := Term.load (plus (lit s.masks) o)
  let dest := Term.binary .bitXor own mask
  let source := raw s dest slot leg
  let h := Term.select .lt source (lit (2+s.shape.header)) (lit 0) (sub source (lit (2+s.shape.header)))
  let hrow := TraceOwnerFormula.direct .row s.shape 1 h (lit 0)
  let localSlot := plus (times (modulo hrow (lit s.lowRows)) (lit s.shape.stride)) (TraceOwnerFormula.direct .slot s.shape 1 h (lit 0))
  ![reg 1,source,TraceOwnerFormula.direct .owner s.shape 1 source dest,own,o,lit s.depth,lit s.shape.header,
    pinStart s,ext s,lit (s.bank+s.bank),localSlot,modulo (quot mask (lit s.lowRows)) (lit 2),
    lit s.tags,t,lit s.equalId]

def holeArgs {W : ℕ} (s : Layout) : Fin 7 → E W :=
  let q := sub (reg 0) (lit (s.relays+s.gates+s.tags))
  let site := plus (laneBase s) (quot q (lit s.shape.stride))
  let slot := modulo q (lit s.shape.stride)
  ![reg 1,ext s,lit (s.bank+s.bank),q,TraceOwnerFormula.validSlot s.shape 1 site slot,
    lit s.zeroId,lit s.unitId]

def relayArgs {W : ℕ} (s : Layout) : Fin 10 → E W :=
  ![reg 0,reg 1,lit s.arcs,lit s.tags,lit s.per,lit s.depth,lit s.low,reg 3,
    .select .eq (reg 3) (lit 0) (ext s) (lit 0),lit s.equalId]

/-- All four cases are fixed-size pure word programs. This program can
therefore be emitted into the private RAM ISA with fixed text capacity
while all literal words and region sizes vary. -/
def program (W : ℕ) (s : Layout) : E W :=
  let relay := (Diagonal.TraceBucketRelay.program W 1 (fun _=>0)).instantiate (relayArgs s)
  let orig := (TraceBucketFields.original.compile (fun _=>0)).instantiate (origArgs s)
  let cmp := (TraceBucketFields.compare.compile (fun _=>0)).instantiate (cmpArgs s)
  let hole := (TraceBucketFields.hole.compile (fun _=>0)).instantiate (holeArgs s)
  .select .lt (reg 0) (lit s.relays) relay
    (.select .lt (reg 0) (lit (s.relays+s.gates)) orig
      (.select .lt (reg 0) (lit (s.relays+s.gates+s.tags)) cmp hole))

end ThreeFlat.RAM.TraceBucketAtom

end OAI
