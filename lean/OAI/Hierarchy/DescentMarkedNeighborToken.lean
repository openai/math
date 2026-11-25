import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! The outgoing marked neighbor encoded by one signed cable word. -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSIMDLookup

def word (d v : ℕ) : Cell d := ⟨v%2^d,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

namespace Stage

def marked {D cap : ℕ} (d : ℕ) : Option (DescentSharedCableNames.Stage.Live D cap)→Cell d
  | none=>0
  | some p=>if p.markedOut then word d (p.neighbor.val+1) else 0

end Stage
end Hierarchy.DescentPacking.PackedMatch.Local

namespace Hierarchy.DescentPackedMatchSenderPins
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap d : ℕ}

def fromChips (d : ℕ) (census : Cell 2) (near : Cell (Packed.bits D)) : Cell d :=
  if census.val=3 then word d near.val else 0

theorem chips_at (x : Option (DescentSharedCableNames.Stage.Live D cap)) :
    fromChips d (DescentSharedCableNames.Stage.censusTag x) (Packed.token (x.map DescentSharedCableNames.Stage.Live.neighbor))=Stage.marked d x :=by
  cases x with
  | none=>simp [fromChips,DescentSharedCableNames.Stage.censusTag,Stage.marked]
  | some t=>cases h:t.markedOut <;> simp [fromChips,DescentSharedCableNames.Stage.censusTag,h,Stage.marked,Packed.token]

def table (D cap d : ℕ) (c : Cell (DescentSignedCableCodec.width D cap)) : Cell d :=
  fromChips d (DescentSignedCableCodec.census c) (DescentSignedCableCodec.neighbor c)

theorem table_at (x : Option (DescentSharedCableNames.Stage.Live D cap)) :
    table D cap d (DescentSignedCableCodec.encode x)=Stage.marked d x :=by simp only [table,DescentSignedCableCodec.census_at,DescentSignedCableCodec.neighbor_at];exact chips_at x

theorem empty : table D cap d 0=0 :=by rw [←DescentSignedCableCodec.empty (D:=D) (cap:=cap),table_at];rfl

end
end Hierarchy.DescentPackedMatchSenderPins

end OAI
