import OAI.Hierarchy.GridReceiverHeader

namespace OAI
/-! # Numeric memory layout shared by the native publisher and its room estimates -/

namespace Hierarchy
namespace GridPinNativeLoops

structure FactorBanks where
  items : ℕ
  keys : ℕ
  owners : ℕ
  resource : ℕ
  stride : ℕ
  amount : ℕ
  ticks : ℕ
  bases : ℕ

structure BucketBanks where
  span : ℕ
  cap : ℕ
  owners : ℕ
  cursors : ℕ
  blocks : ℕ

structure SourceBanks where
  span : ℕ
  external : ℕ
  originals : ℕ
  blocks : ℕ
  literal : ℕ
  rails : ℕ
  dest : ℕ

end GridPinNativeLoops

namespace GridSelfHeader

def rawSize (w E B n : ℕ) :=
  E*2+w^2+B*w^2+(n+GridReceiverHeader.count w)*(64*w)

end GridSelfHeader

namespace GridPinHeaderNative
open GridReceiverHeader

/-- Absolute addresses of captured text, the serialized structural and threshold operands,
the checked selector bit array, and the output pin bank. -/
structure Banks where
  textBase : ℕ
  operandBase : ℕ
  selectorBase : ℕ
  literalBase : ℕ
  pins : ℕ
  text : ℕ
  operandBits : ℕ
  selector : ℕ

/-- The array parameters contain only the public banks in the actual evaluator
input. Each field read is recovered from the original captured memory. -/
def captureBanks (w e compact n ell start literal pins text : ℕ) : Banks :=
  ⟨e*2,e*2+w^2+compact*w^2,start,literal,pins,text,(n+count w)*(64*w),ell⟩

end GridPinHeaderNative

namespace GridPinPublisher
open GridPinNativeLoops

/-- Public native scan lengths and the physical allocator's distinct banks. -/
structure Plan where
  ticks : ℕ
  factors : ℕ
  lanes : ℕ
  literals : ℕ
  endpoints : ℕ
  headerSize : ℕ
  factor : FactorBanks
  bucket : BucketBanks
  source : SourceBanks
  header : GridPinHeaderNative.Banks

/-- The source fields of the actual evaluator and the last immutable
lane-destination row in the relocated archive. Keys and owners use the same
original physical ordinal as the admission matrix. -/
def canonical (scale k n q pinWidth nparams selector text compact rails bits
    nFactors stages fullLanes span : ℕ) : Plan :=
  let J := GridDescription.sector scale
  let g := 2^(16*scale)
  let tickCur := 15*J+8*g
  let factorCur := 15*J+9*g
  let laneBase := 15*J+10*g
  let railRank := 15*J+11*g
  let D := 16*J+g+stages*fullLanes
  { ticks := (n+1)^k*q
    factors := (20*(scale+1)+2)^(k+2)*nFactors
    lanes := (bits+span-1)/span
    literals := GridSelfHeader.rawSize scale rails compact nparams-rails*2
    endpoints := rails*2
    headerSize := text+((nparams+1)*(64*scale)+(GridReceiverHeader.count scale*(64*scale)+selector))
    factor := ⟨nFactors,15*J+g,15*J+3*g,14*J,k+2,1,tickCur,factorCur⟩
    bucket := ⟨span,bits,D,factorCur,laneBase⟩
    source := ⟨span,rails*2,0,laneBase,10*J,railRank,9*J⟩
    header := GridPinHeaderNative.captureBanks scale rails compact nparams selector
      (12*J) (10*J) pinWidth text }

end GridPinPublisher
end Hierarchy

end OAI
