import OAI.Hierarchy.DescentActorHeaderGateRun

namespace OAI
/-! Public addresses of the successor actor plane following the reset root tables. -/
namespace Hierarchy.DescentDatedAddressBook
open ProtocolRAM DescentSIMDLookup DescentActorRaster
noncomputable section

/-- The previous date fixes the common block and its packing. A whole scalar depth and
shared-book count is read for each old host. The actor plane has one bit per group. -/
structure ActorSetup where
  hosts : ℕ
  common : ℕ
  localDepth : ℕ
  lanes : ℕ
  stencilBits : ℕ
  headerBits : ℕ
  shapes : ℕ
  arity : ℕ
  oldWidth : ℕ
  maxCount : ℕ

namespace ActorSetup
variable (v : ActorSetup)

def bank (base extent : ℕ) : Bank := ⟨base,Nat.clog 2 extent⟩
def next (b : Bank) := b.base+b.size

def depths (base : ℕ) := bank base v.hosts
def counts (base : ℕ) := bank (next (v.depths base)) (v.hosts*v.arity)
def starts (base : ℕ) := bank (next (v.counts base)) v.hosts
def levels (base : ℕ) := bank (next (v.starts base)) (v.oldWidth+1)
def heights (base : ℕ) := bank (next (v.levels base)) (v.maxCount+1)
def sources (population : Bank) (base : ℕ) : Headers.Banks :=
  ⟨population,v.depths base,v.counts base,v.starts base,v.levels base,v.heights base⟩

def groups := 2^v.common
def chunksPerHost := chunks v.groups v.lanes
def unitBits := v.stencilBits*2^v.localDepth+v.headerBits

def gate (base : ℕ) : HeaderGate.Layout :=
  let s:=next (v.heights base)
  let b:=s+v.shapes*v.hosts
  let g:=DescentSharedLeafLookup.Public.stop b v.hosts v.groups v.lanes v.headerBits
  ⟨s,b,g,g+v.shapes*(2*2^(v.unitBits*v.lanes))⟩

def scene (base : ℕ) := bank (v.gate base).output (v.shapes*(v.hosts*v.chunksPerHost))
def endAddress (base : ℕ) := next (v.scene base)

theorem extent_scene (base : ℕ) : v.shapes*(v.hosts*v.chunksPerHost)≤(v.scene base).size :=
  Nat.le_pow_clog (by decide) _

theorem gate_order (base : ℕ) :
    (v.gate base).scalar+v.shapes*v.hosts=(v.gate base).repeatBase ∧
    DescentSharedLeafLookup.Public.stop (v.gate base).repeatBase v.hosts v.groups v.lanes
      v.headerBits=(v.gate base).gateBase ∧
    (v.gate base).gateBase+v.shapes*(2*2^(v.unitBits*v.lanes))=(v.gate base).output :=
  ⟨rfl,rfl,rfl⟩

theorem extent_input (base : ℕ) :
    v.hosts≤(v.depths base).size ∧ v.hosts*v.arity≤(v.counts base).size ∧
    v.hosts≤(v.starts base).size ∧ v.oldWidth<(v.levels base).size ∧
    v.maxCount<(v.heights base).size :=
  ⟨Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,
    Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _⟩

end ActorSetup
end
end Hierarchy.DescentDatedAddressBook

end OAI
