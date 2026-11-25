import OAI.ThreeFlat.Diagonal.TraceStaticRecordData

namespace OAI
/-! # Address records after fixing the unused bits of each input word -/

namespace ThreeFlat.Diagonal.TraceAddressRecord

variable {w r p k d : ℕ}

def changeBase (R : Record) (drop : ℕ) : Record := { R with sub := R.sub+drop }

def bitHeader (s j S : ℕ) : Record :=
  if j=0 then { testStride := 2, testBias := s, hi := S, base := 2+s, stride := 2 }
  else {}

/-- Shared addresses lose the unused high input bits. Every remaining
header port addresses a single low bit, and control ports still read zero
or one. -/
def bitPort (hw : 3≤w+1) (_base S f : ℕ) (a : TraceUniformRow.Port w p r k d) : Record :=
  match a with
  | .inl (.inr (.inl (s,j))) => bitHeader s.val j.val S
  | z => changeBase (portRecord (by omega) S f z) (S*w-S)

def staticBitPort (hw : 3≤w+1) (base S f : ℕ) : StaticPortIndex w p r k d → Record
  | .inl z => bitPort hw base S f z
  | .inr z => staticPort (r:=r) hw base S f (.inr z)

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
