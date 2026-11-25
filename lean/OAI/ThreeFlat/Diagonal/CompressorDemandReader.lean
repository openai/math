import OAI.ThreeFlat.Diagonal.CompressorNativeArc
import OAI.ThreeFlat.RAM.MotifRows

namespace OAI
/-! # Native old-width reads for the AB and CD demand records

A single old width is at (base, outgoing slot, physical lane). The low
digits of the lane are color bits, consumed port, tag, and remaining lane,
in that order. At a bundle the AB numerator is the sum over all thick-thick
edges. The piece ordinal counts preceding designated thin incidences in
physical old-arc order. Each such incidence appears once.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Demand
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
variable {n : ℕ}

def formulaOps (n : ℕ) : Ops (Formula n) := ⟨.lit,.op,.load,.select .eq⟩

structure WidthLayout (n : ℕ) where
  table : Formula n
  laneCount : Formula n
  tagCount : Formula n
  degree : ℕ
  colors : ℕ

def physical (p : WidthLayout n) (x : Position (Formula n)) (outSlot : Formula n) : Formula n :=
  let o := formulaOps n
  let site := x.site
  let tagged := o.bin .add site.tag (o.bin .mul p.tagCount site.lane)
  let rest := o.bin .add x.slot (o.bin .mul (o.lit p.degree) tagged)
  let lane := o.bin .add x.bits (o.bin .mul (o.lit (2^p.colors)) rest)
  let edge := o.bin .add (o.bin .mul site.base (o.lit p.degree)) outSlot
  o.bin .add (o.bin .mul edge p.laneCount) lane

def width (p : WidthLayout n) (x : Position (Formula n)) (outSlot : Formula n) : Formula n :=
  .load (.op .add p.table (physical p x outSlot))

def allSlots (d c : ℕ) (f : Fin d → Fin (2^c) → Formula n) : Formula n :=
  RAM.MotifRows.totals ((List.finRange d).map fun h =>
    RAM.MotifRows.totals ((List.finRange (2^c)).map (f h)))

def element (g : ArcColumns (Formula n)) (p : WidthLayout n) (s : Site (Formula n))
    (port : Formula n) (h : Fin p.degree) (u : Fin (2^p.colors)) : Formula n :=
  let o := formulaOps n
  let x : Position (Formula n) := ⟨s,.lit u.val,.lit h.val⟩
  let a := ends o g p.degree false x port
  o.choose (thickBit o g.toColumns x) (o.lit 1)
    (o.choose (thickBit o g.toColumns a.target) (o.lit 1) (width p x port) (o.lit 0))
    (o.lit 0)

def thickWidth (g : ArcColumns (Formula n)) (p : WidthLayout n) (s : Site (Formula n))
    (port : Formula n) : Formula n :=
  allSlots p.degree p.colors (element g p s port)

/-- For outgoing incidences C must be thin; for incoming incidences its
predecessor must also be thick. Both compare the original outgoing arc
address to that of the current demand. -/
def earlier (g : ArcColumns (Formula n)) (p : WidthLayout n) (s : Site (Formula n))
    (port key : Formula n) (incoming : Bool) (i : Fin p.degree) (u : Fin (2^p.colors)) : Formula n :=
  let o := formulaOps n
  let x : Position (Formula n) := ⟨toggle o g.toColumns s,.lit u.val,port⟩
  let e := ends o g p.degree incoming x (.lit i.val)
  let test := Formula.select .lt (physical p e.source e.originalSlot) key (.lit 1) (.lit 0)
  let side := if incoming then o.choose (thickBit o g.toColumns e.source) (.lit 1) test (.lit 0) else test
  o.choose (thickBit o g.toColumns x) (.lit 1) (.lit 0) side

def bundleNumber (g : ArcColumns (Formula n)) (p : WidthLayout n) (s : Site (Formula n))
    (port key : Formula n) : Formula n :=
  .op .add (allSlots p.degree p.colors (earlier g p s port key false))
    (allSlots p.degree p.colors (earlier g p s port key true))

def balanced (total : Formula n) (Q : ℕ) (i : Formula n) : Formula n :=
  .op .add (.op .div total (.lit Q))
    (.select .lt i (.op .mod total (.lit Q)) (.lit 1) (.lit 0))

/-- These are the two consecutive old-demand words consumed by `MotifRows.scoreRow`. -/
def pair (g : ArcColumns (Formula n)) (p : WidthLayout n) (Q : ℕ) (e : Ends (Formula n)) :
    Fin 2 → Formula n :=
  let o := formulaOps n
  let c := Position.select o (thickBit o g.toColumns e.source) e.target e.source
  let s := toggle o g.toColumns c.site
  let key := physical p e.source e.originalSlot
  let ab := balanced (thickWidth g p s c.slot) Q (bundleNumber g p s c.slot key)
  ![ab,width p e.source e.originalSlot]

def fromSource (g : ArcColumns (Formula n)) (p : WidthLayout n) (Q : ℕ)
    (x : Position (Formula n)) (outSlot : Formula n) : Fin 2 → Formula n :=
  pair g p Q (ends (formulaOps n) g p.degree false x outSlot)

theorem physical_value (p : WidthLayout n) (x : Position (Formula n)) (slot : Formula n)
    (w : ℕ) (pub : RAM.PhysicalPinsExpr.Param → ℕ) (m : ℕ → ℕ) (vs : Fin n → ℕ) :
    let v := Formula.natural w pub m vs
    v (physical p x slot) =
      (v x.site.base*p.degree+v slot)*v p.laneCount+
        (v x.bits+2^p.colors*(v x.slot+p.degree*(v x.site.tag+v p.tagCount*v x.site.lane))) := rfl

theorem width_value (p : WidthLayout n) (x : Position (Formula n)) (slot : Formula n)
    (w : ℕ) (pub : RAM.PhysicalPinsExpr.Param → ℕ) (m : ℕ → ℕ) (vs : Fin n → ℕ) :
    let v := Formula.natural w pub m vs
    v (width p x slot) = m (v p.table+v (physical p x slot)) := rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.Demand

end OAI
