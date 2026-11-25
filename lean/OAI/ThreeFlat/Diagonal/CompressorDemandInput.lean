import OAI.ThreeFlat.Diagonal.CompressorShrinkWidthWriter

namespace OAI
/-! # Inverting a dense CD row to generate the two old-demand words before admission -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
variable {n : ℕ}

/-- Decode all digits left after removing the color word. -/
def upperSource (p : Demand.WidthLayout n) (remain upper : F n) : Position (F n) × F n :=
  let label := Formula.op .mod upper (.lit p.degree)
  let qTag := Formula.op .div upper (.lit p.degree)
  let tag := Formula.op .mod qTag p.tagCount
  let qLane := Formula.op .div qTag p.tagCount
  let lane := Formula.op .mod qLane remain
  let qPort := Formula.op .div qLane remain
  let port := Formula.op .mod qPort (.lit p.degree)
  let base := Formula.op .div qPort (.lit p.degree)
  (⟨⟨base,tag,lane⟩,.lit 0,label⟩,port)

def firstWord {b : ℕ} (test : Fin b → F n) (xs : List (Fin b)) : F n :=
  xs.foldr (fun u tail => .select .eq (test u) (.lit 1) (.lit u.val) tail) (.lit 0)

def cdTest (g : ArcColumns (F n)) (p : Demand.WidthLayout n) (x : Position (F n))
    (port rank : F n) (k : Fin (2^p.colors)) : F n :=
  let o := Demand.formulaOps n
  let y := {x with bits := Formula.lit k.val}
  let e := ends o g p.degree false y port
  let cd := o.choose (thickBit o g.toColumns y) (.lit 1)
    (o.choose (thickBit o g.toColumns e.target) (.lit 1) (.lit 0) (.lit 1)) (.lit 1)
  .select .eq cd (.lit 1) (.select .eq (lowerCD g p y port) rank (.lit 1) (.lit 0)) (.lit 0)

/-- Each accepted color word is tested against its dense lower-prefix
rank. The search length depends only on the fixed base degree. -/
def decodeRow (g : ArcColumns (F n)) (p : Demand.WidthLayout n) (remain ordinal : F n) :
    Position (F n) × F n :=
  let size := Formula.lit (3*2^(p.colors-2))
  let (x,port) := upperSource p remain (.op .div ordinal size)
  let rank := Formula.op .mod ordinal size
  let bits := firstWord (cdTest g p x port rank) (List.finRange (2^p.colors))
  ({x with bits},port)

def inputPair (g : ArcColumns (F n)) (p : Demand.WidthLayout n) (remain i : F n) : F n :=
  let (x,port) := decodeRow g p remain (.op .div i (.lit 2))
  let read := Demand.fromSource g p (3*(2^p.colors*p.degree)/4) x port
  .select .eq (.op .mod i (.lit 2)) (.lit 0) (read 0) (read 1)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
