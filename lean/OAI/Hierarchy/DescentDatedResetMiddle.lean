import OAI.Hierarchy.DescentDatedSignedArea
import OAI.Hierarchy.DescentProjectedResetShelves
import OAI.Hierarchy.DescentSignedGLRun
import OAI.Hierarchy.DescentSignedRetile
import OAI.Hierarchy.DescentDatedStencilRate
import OAI.Hierarchy.DescentDatedResetWindows
import OAI.Hierarchy.DescentDatedRootShelf

namespace OAI
/-! # Contiguous weighted stencil, separate signed-port transport, and all physically issued roots -/
namespace Hierarchy.DescentDatedAddressBook
open DescentGLPacked.BankImage DescentGLControlCode DescentPlainTerminal.Suffix DescentSixParty.Chronology Filter
noncomputable section
structure ResetMiddle where
  stencil : StencilBook
  signedPorts : ℕ
  signedHosts : ℕ
  high : ℕ
  low : ℕ
  signedBits : ℕ
  oldBlocks : ℕ
  signedLanes : ℕ
  signedRatio : ℕ
  rootHosts : ℕ
  rootGroups : ℕ
  rootLanes : ℕ
  rootDepth : ℕ
  rotorBits : ℕ
  rootDegree : ℕ
  rootShapes : ℕ
  rootField : ℕ
  rootLawWidth : ℕ

namespace ResetMiddle
variable (v : ResetMiddle)
def afterStencil (base : ℕ) :=v.stencil.endAddress base
def retileEnd (base : ℕ) :=SignedFields.Retile.stop base v.signedBits v.signedHosts v.rootGroups
  v.signedRatio v.signedLanes (v.signedPorts*v.oldBlocks)
def signedCharts (base : ℕ) :=
  SignedFields.stop (SignedFields.joinStop (v.retileEnd base) v.signedBits v.oldBlocks v.signedLanes)
    v.signedPorts v.signedHosts v.high v.low v.signedBits
def afterSigned (base : ℕ) :=v.signedCharts (v.afterStencil base)
def projectBits :=max (v.stencil.t*2^v.rootDepth) (v.signedBits*2^v.rootDepth)
def projectCount :=2*2^v.rootDepth+v.signedPorts*2^v.rootDepth
def afterProjection (base : ℕ) :=DescentFallbackPeriod.Projected.start (v.afterSigned base)
  v.projectBits v.rootHosts v.rootGroups v.rootLanes v.projectCount
def rootHeader (base : ℕ) :=rootHeaderEnd base v.rootDepth v.rotorBits v.rootDegree v.rootHosts
  v.rootGroups v.rootLanes v.rootShapes v.rootField v.rootLawWidth
def stop (base : ℕ) :=RootTemplates.privateEnd (v.rootHeader (v.afterProjection base))
  v.rootHosts v.rootGroups v.rootLanes v.rootDepth v.rotorBits v.rootDegree

theorem translated (base : ℕ) : v.stop base=base+v.stop 0 := by
  have stencil:=v.stencil.translated 0 base
  simp only [Nat.zero_add] at stencil
  unfold stop
  rw [show v.rootHeader (v.afterProjection base)=v.afterProjection base+v.rootHeader 0 from root_header_affine ..,
    show v.rootHeader (v.afterProjection 0)=v.afterProjection 0+v.rootHeader 0 from root_header_affine ..]
  unfold afterProjection DescentFallbackPeriod.Projected.start afterSigned afterStencil signedCharts SignedFields.stop SignedFields.joinStop retileEnd SignedFields.Retile.stop DescentSIMDLookup.Subwords.destination
  simp only [Dated.extent,stencil,RootTemplates.privateEnd,RootArena.first,RootArena.stride]
  omega

variable {ι : ℕ→Type*}
theorem retile_rate (v : ∀h,ι h→ResetMiddle)
    (hosts : Bounded (fun h i=>(v h i).signedHosts)) (groups : Bounded (fun h i=>(v h i).rootGroups))
    (lanes : Bounded (fun h i=>(v h i).signedLanes)) (ports : Bounded (fun h i=>(v h i).signedPorts))
    (blocks : Bounded (fun h i=>(v h i).oldBlocks)) (ratio : Bounded (fun h i=>(v h i).signedRatio))
    (key : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let m:=v h i; m.signedBits*(m.signedRatio*m.signedLanes)≤K*h) :
    Bounded (fun h i=>(v h i).retileEnd 0) := by
  obtain ⟨K,b⟩:=key
  have page:=Bounded.pow_of_linear (K:=K) b
  have cells:=hosts.mul ((groups.add lanes).of_le (y:=fun h i=>DescentSIMDLookup.chunks (v h i).rootGroups (v h i).signedLanes)
    fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have store:=(Bounded.const 4).mul (((Bounded.const 1).add cells).add (ratio.mul page))
  apply (store.add (((ports.mul blocks).add (Bounded.const 1)).mul cells.padded)).of_le
  intro h i
  simp only [retileEnd,SignedFields.Retile.stop,DescentSIMDLookup.Subwords.destination,
    SignedFields.Retile.pitch,DescentSIMDLookup.Subwords.stride,Nat.zero_add,Nat.le_refl]

theorem signed_span (v : ∀h,ι h→ResetMiddle) (pay : ∀h,ι h→ℕ)
    (blocks : Bounded (fun h i=>(v h i).oldBlocks))
    (priorTable : Bounded (fun h i=>2^(((v h i).signedBits*(v h i).oldBlocks+(v h i).signedBits)*(v h i).signedLanes)))
    (retile : Bounded (fun h i=>(v h i).retileEnd 0))
    (channels : Bounded (fun h i=>(v h i).signedPorts*(v h i).signedHosts))
    (dimensions : Bounded (fun h i=>(v h i).high+(v h i).low))
    (chunks : Bounded (fun h i=>2^(v h i).high))
    (pages : Bounded (fun h i=>2^(pay h i/2)))
    (packed : ∀ᶠ h:ℕ in atTop,∀i,let a:=v h i;(a.signedBits+a.signedBits)*2^a.low≤pay h i/2)
    (square : ∀ᶠ h:ℕ in atTop,∀i,let a:=v h i;(a.high+a.low)*(a.high+a.low)≤pay h i/2) :
    Bounded (fun h i=>(v h i).signedCharts 0) := by
  have count : Bounded (fun h i=>Count ((v h i).high+(v h i).low)) :=
    (((Bounded.const 3).mul dimensions).mul dimensions).of_le fun _ _=>DescentGLNielsen.length_le _
  have byrow:=channels.mul chunks
  have firstRows := ((((Bounded.const 1).add count).mul pages).add count).add (dimensions.mul chunks)
  have gate := (Bounded.const 4).mul (firstRows.add (Bounded.const 1))
  have upper := (gate.add ((Bounded.const 2).mul (byrow.add (Bounded.const 1)))).add count
  have trailing:=(((Bounded.const 7).mul count).add (Bounded.const 1)).mul
    (((Bounded.const 2).mul (byrow.add (Bounded.const 1))).add pages)
  have coal:=blocks.mul ((Bounded.const 2).mul priorTable)
  apply ((retile.add coal).add (upper.add trailing)).of_eventually_le
  filter_upwards [packed,square] with h words matrix
  intro i
  have use:=SignedFields.span_price (SignedFields.joinStop ((v h i).retileEnd 0) (v h i).signedBits (v h i).oldBlocks (v h i).signedLanes)
    (v h i).signedPorts (v h i).signedHosts (v h i).high (v h i).low (v h i).signedBits
    (pay h i) (words i) (matrix i)
  dsimp only [SignedFields.joinStop,SignedFields.joinWidth,Nat.zero_add,signedCharts] at use ⊢
  omega

theorem geometric_rate (v : ∀h,ι h→ResetMiddle)
    (stencil : StencilBook.ScalarRoom (fun h i=>(v h i).stencil))
    (signed : Bounded (fun h i=>(v h i).signedCharts 0))
    (rootH : Bounded (fun h i=>(v h i).rootHosts)) (rootG : Bounded (fun h i=>(v h i).rootGroups))
    (rootM : Bounded (fun h i=>(v h i).rootLanes)) (rootK : Bounded (fun h i=>2^(v h i).rootDepth))
    (rotors : Bounded (fun h i=>2^(v h i).rotorBits)) (rootD : Bounded (fun h i=>(v h i).rootDegree))
    (channels : Bounded (fun h i=>(v h i).signedPorts))
    (headers : Bounded (fun h i=>(v h i).rootHeader 0))
    (project : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(v h i).projectBits*(v h i).rootLanes≤C*h) :
    Bounded (fun h i=>(v h i).stop 0) := by
  have first:=StencilBook.extent_rate (fun h i=>(v h i).stencil) stencil
  have roots:=RootTemplates.private_span_rate _ _ _ _ _ _ rootH rootG rootM rootK rotors rootD
  obtain ⟨C,key⟩:=project
  have selectors:=Bounded.pow_of_linear (K:=C) key
  have batches : Bounded (fun h i=>DescentSIMDLookup.chunks (v h i).rootGroups (v h i).rootLanes) :=
    (rootG.add rootM).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have cells:=rootH.mul batches
  have stride_ :=(selectors.add cells.padded).add cells.padded
  have n:=((Bounded.const 2).mul rootK).add (channels.mul rootK)
  apply ((((first.add signed).add (stride_.mul n)).add headers).add roots).of_le
  intro h i
  unfold stop
  rw [show (v h i).rootHeader ((v h i).afterProjection 0)= (v h i).afterProjection 0+(v h i).rootHeader 0 from root_header_affine ..]
  unfold afterProjection DescentFallbackPeriod.Projected.start afterSigned afterStencil signedCharts SignedFields.stop SignedFields.joinStop retileEnd SignedFields.Retile.stop DescentSIMDLookup.Subwords.destination
  simp only [Dated.extent,RootTemplates.privateEnd,RootArena.first,RootArena.stride,
    DescentFallbackPeriod.Projected.stride,projectCount,Nat.zero_add]
  omega

end ResetMiddle
end
end Hierarchy.DescentDatedAddressBook

end OAI
