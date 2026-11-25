import OAI.Hierarchy.GridPinPublisherLayout

namespace OAI
/-! # Named physical tables of the pin publisher and their immutable boundaries -/

namespace Hierarchy.GridPinPublisher

inductive Bank where
  | raw | selector | keys | owners | resource | ancestors | ticks | factors | blocks | rails | dest | literals
  deriving DecidableEq

def Bank.base (P : Plan) : Bank→ℕ
  | .raw => P.source.originals
  | .selector => P.header.selectorBase
  | .keys => P.factor.keys
  | .owners => P.factor.owners
  | .resource => P.factor.resource
  | .ancestors => P.bucket.owners
  | .ticks => P.factor.ticks
  | .factors => P.factor.bases
  | .blocks => P.bucket.blocks
  | .rails => P.source.rails
  | .dest => P.source.dest
  | .literals => P.source.literal

def Bank.length (P : Plan) (rawSize fullLanes : ℕ) : Bank→ℕ
  | .raw => rawSize
  | .selector => P.header.selector
  | .keys | .owners | .factors => P.factor.items
  | .resource => P.factor.items*P.factor.stride
  | .ancestors => fullLanes
  | .ticks => P.ticks
  | .blocks => P.lanes
  | .rails => P.endpoints/2
  | .dest => P.endpoints
  | .literals => P.ticks*P.header.pins

structure BankRoom (W : ℕ) (P : Plan) (rawSize fullLanes : ℕ) : Prop where
  fit : ∀b : Bank,b.base P+b.length P rawSize fullLanes≤2^W
  disjoint : ∀ b c : Bank,b≠c → b.base P+b.length P rawSize fullLanes≤c.base P ∨
    c.base P+c.length P rawSize fullLanes≤b.base P

variable {W rawSize fullLanes : ℕ} {P : Plan}

theorem BankRoom.address (R : BankRoom W P rawSize fullLanes) (b : Bank) {i : ℕ}
    (hi : i<b.length P rawSize fullLanes) : b.base P+i<2^W := by
  have := R.fit b
  omega

theorem BankRoom.away (R : BankRoom W P rawSize fullLanes) (b c : Bank) (different : b≠c)
    {i : ℕ} (hi : i<b.length P rawSize fullLanes) :
    b.base P+i<c.base P ∨ c.base P+c.length P rawSize fullLanes≤b.base P+i := by
  have := R.disjoint b c different
  omega

theorem BankRoom.ne (R : BankRoom W P rawSize fullLanes) (b c : Bank) (different : b≠c)
    {i j : ℕ} (hi : i<b.length P rawSize fullLanes) (hj : j<c.length P rawSize fullLanes) :
    b.base P+i≠c.base P+j := by
  have := R.away b c different hi
  omega

end Hierarchy.GridPinPublisher

end OAI
