import OAI.Computability.NearSquareRoot.PhysicalWalshSwapCodec
import OAI.Computability.NearSquareRoot.PhysicalWalshOpen

/-! # Two fixed programs for packing and unpacking arbitrary suffix widths -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapCodec
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshSwapCodec

structure Batch where
  w : ℕ
  b : ℕ
  n : ℕ
  bpos : 0 < b
  npos : 0 < n
  data : ℕ → Dusk.Grain w

namespace Batch

def work (t : Batch) := (t.n*t.b+1)*(t.w+1)
def stream (t : Batch) := (List.range (t.n*t.b)).map (Dusk.mark ∘ t.data)
def packed (t : Batch) := (List.range t.n).map (payload t.b t.data)
def packKey (t : Batch) := (tally t.n,tally (t.b*(2*(t.w+1))))
def unpackKey (t : Batch) := (tally (t.n*t.b),tally (2*(t.w+1)))

end Batch

def Packs (c : Cmd) := ClosedRuns c Batch.work Batch.work
  (fun t => send (t.packKey,t.stream)) (send ∘ Batch.packed)
def Unpacks (c : Cmd) := ClosedRuns c Batch.work Batch.work
  (fun t => send (t.unpackKey,t.packed)) (send ∘ Batch.stream)

theorem fixed : (∃ c, Packs c) ∧ (∃ c, Unpacks c) :=
  ⟨packOrdinal Batch.w Batch.b Batch.n Batch.data Batch.npos Batch.bpos,
    unpackOrdinal Batch.w Batch.b Batch.n Batch.data Batch.npos Batch.bpos⟩

end PhysicalWalshCompileSwapCodec

end NearSquareRoot
end Computability
end OAI
