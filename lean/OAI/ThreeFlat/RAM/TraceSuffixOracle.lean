import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # A fixed native scalar reader for the prepared H trace's public header -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The virtual header overlays code on the advice, startup parameters and
serialized local table. Their three backing segments are bit-per-word. -/
structure Layout where
  paired : ℕ
  rawParams : ℕ
  rawTable : ℕ
  rawCount : ℕ
  hWidth : ℕ
  description : ℕ
  parameters : ℕ
  table : ℕ
  codeBase : ℕ
  textOffset : ℕ
  textSize : ℕ

def tailBit (w bit : ℕ) := if bit/w%11=3 then if bit%w=w-1 then 1 else 0 else 0

def raw (s : Layout) (m : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t<s.paired then 0 else if t<s.rawParams then m (s.description+(t-s.paired))
  else if t<s.rawTable then m (s.parameters+(t-s.rawParams))
  else if t<s.rawCount then m (s.table+(t-s.rawTable))
  else tailBit s.hWidth (t-s.rawTable)

def read (s : Layout) (m : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t<s.codeBase then raw s m t else if t<s.codeBase+s.textSize then
    m (s.description+s.textOffset+(t-s.codeBase)) else raw s m t

end ThreeFlat.RAM.TraceSuffixOracle

end OAI
