import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentResetPeerProgram
import OAI.Hierarchy.DescentResetSelfPortsRAM
import OAI.Hierarchy.DescentResetTrunkPalette

namespace OAI
/-! # The true union of the predecessor's three neighbors with the receiving host -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetPeerUnionRAM Filter
noncomputable section

structure PeerAperture where
  oldHosts : ℕ
  shapes : ℕ
  oldDegree : ℕ
  evidence : ℕ
  bits : ℕ
  evidenceGroups : ℕ
  evidenceLanes : ℕ
  groups : ℕ
  lanes : ℕ

namespace PeerAperture
variable (p : PeerAperture)
def hosts := p.oldHosts*p.shapes
def slots :=Candidates.count p.shapes p.oldDegree
def three (base : ℕ) :=Program.endAddress base p.oldHosts p.shapes p.oldDegree p.evidence p.bits p.evidenceLanes
def self (base : ℕ) :=DescentResetSelfPortsRAM.endAddress (p.three base) p.hosts p.groups p.lanes
def threshold (base : ℕ) :=p.self base
/-- Three trunk palette words per actual public host, the exact range of TrunkPalette.run. -/
def endAddress (base : ℕ) :=p.threshold base+2*p.hosts+DescentDyadicSpan.span p.hosts

theorem three_extent (base : ℕ) : p.three base=base+p.three 0 := by
  simp only [three,Program.endAddress,Program.scratchAt,Program.tablesAt,stop,outBase,Nat.zero_add]
  omega

theorem extent (base : ℕ) : p.endAddress base=base+p.endAddress 0 := by
  unfold endAddress threshold self
  rw [DescentResetSelfPortsRAM.extent (p.three base), DescentResetSelfPortsRAM.extent (p.three 0),p.three_extent base]
  omega

theorem bounded {ι : ℕ→Type*} (q : ∀h,ι h→PeerAperture)
    (old : Bounded (fun h i=>(q h i).oldHosts)) (shapes : Bounded (fun h i=>(q h i).shapes))
    (degree : Bounded (fun h i=>(q h i).oldDegree)) (evidence : Bounded (fun h i=>(q h i).evidence))
    (groups : Bounded (fun h i=>(q h i).groups)) (lanes : Bounded (fun h i=>(q h i).lanes))
    (packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(q h i).bits*(q h i).evidenceLanes≤K*h) :
    Bounded (fun h i=>(q h i).endAddress 0) := by
  obtain ⟨K,hk⟩:=packed
  have menu:=Bounded.pow_of_linear (K:=K) hk
  have total:=old.mul shapes
  have count:=(((degree.add (Bounded.const 1)).mul shapes).add (Bounded.const 3))
  have P:=(total.add (Bounded.const 1)).padded
  have O:=(old.add (Bounded.const 1)).padded
  have raw:=(((Bounded.const 2).mul P).add O).add ((count.mul evidence).mul menu)
  have threeRate:=((raw.add (count.mul P)).add ((Bounded.const 3).mul total))
  have fourRate:=DescentResetSelfPortsRAM.bounded total groups lanes
  apply (((threeRate.add fourRate).add ((Bounded.const 2).mul total)).add total.padded).of_le
  intro h i
  unfold endAddress threshold self
  rw [DescentResetSelfPortsRAM.extent]
  simp only [three, Program.endAddress,Program.tablesAt,Program.scratchAt,Candidates.length,
    Candidates.count,Packed.words,stop,outBase,hosts,DescentDyadicSpan.span,stride,pageBits,Nat.zero_add,Nat.le_refl]

end PeerAperture
end
end Hierarchy.DescentDatedAddressBook

end OAI
