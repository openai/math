import OAI.Hierarchy.DescentResetOriginalDonors
import OAI.Hierarchy.DescentResetOriginalZeroHaloPrice
import OAI.Hierarchy.DescentStemNumberOperands
import OAI.Hierarchy.DescentStemCoordinateBook
import OAI.Hierarchy.DescentDatedCandidateFront
import OAI.Hierarchy.DescentResetCandidateDate
import OAI.Hierarchy.DescentResetPublicOriginalPhase
import OAI.Hierarchy.DescentResetOriginalBooks
import OAI.Hierarchy.DescentResetCandidatePair
import OAI.Hierarchy.DescentUniformSlotOperands
import OAI.Hierarchy.DescentOperandPairBook

namespace OAI
/-! # Compact and original parent numbers at the same physical receiver -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetCandidateDate DescentSIMDLookup DescentDyadicSpan DescentResetMixedWordRAM
noncomputable section

structure CandidateSheets where
  blocks : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  candidates : ℕ
  jobs : ℕ
  contacts : ℕ
  privates : ℕ
  metaBits : ℕ
  stemBits : ℕ
  selectorBits : ℕ
  shortBits : ℕ
  zeroBits : ℕ
  haloBits : ℕ
  argBits : ℕ
  stemDimension : ℕ
  stemFine : ℕ
  stemResidual : ℕ
  stemSignedBits : ℕ
  sparseHosts : ℕ
  donorSlots : ℕ
namespace CandidateSheets
variable (s : CandidateSheets)
def rows :=s.hosts*chunks s.groups s.lanes
def rank (base : ℕ) : Shape :=⟨base,3*s.jobs,s.lanes,s.hosts,s.groups⟩
def masks (base : ℕ) : Shape :=⟨(s.rank base).endAddress 5 s.metaBits,s.jobs,s.lanes,s.hosts,s.groups⟩
def metaEnd (base : ℕ) :=(s.masks base).endAddress 9 s.metaBits

theorem physically_mixed (base : ℕ) (rankRead : ℕ→Fin 5→ProtocolRAM.Expr) (raw : ℕ→Fin 9→ProtocolRAM.Expr) :
    s.metaEnd base=({
      first := base, jobs := s.jobs, lanes := s.lanes, hosts := s.hosts, groups := s.groups,
      bits := s.metaBits, rankReads := rankRead, rawReads := raw } : Mixed).endAddress :=rfl

def coordinate : DescentStemCoordinateBook.Shape :=
  ⟨s.stemDimension,s.stemFine,s.stemResidual,s.hosts,s.groups,s.lanes,s.stemBits⟩
def stemSources : DescentStemNumberOperands.Plan :=⟨s.coordinate,s.stemSignedBits,s.metaBits,s.metaBits⟩
def coordinateOnly (base : ℕ) :=s.coordinate.endAddress (s.metaEnd base)
def coordinateEnd (base : ℕ) :=s.stemSources.endAddress (s.metaEnd base)
def originalDonors : DescentResetOriginalDonors.Layout :=
  ⟨s.sparseHosts,s.groups,s.blocks,s.lanes,s.donorSlots,s.stemSignedBits,s.metaBits,s.selectorBits,s.shortBits⟩
def inputDonorsBase (base : ℕ) :=
  DescentResetOriginalZeroHalo.endAddress (s.coordinateEnd base) s.hosts s.groups s.lanes s.metaBits
def inputDonorsEnd (base : ℕ) :=s.originalDonors.endAddress (s.inputDonorsBase base)
theorem donors_shift (base : ℕ) : s.inputDonorsEnd base = s.coordinateEnd base +
    (DescentResetOriginalZeroHalo.endAddress 0 s.hosts s.groups s.lanes s.metaBits+s.originalDonors.endAddress 0) :=by
  rw [inputDonorsEnd,s.originalDonors.extent (s.inputDonorsBase base),inputDonorsBase,
    DescentResetOriginalZeroHalo.shift (s.coordinateEnd base)]
  omega
def donorEnd (base : ℕ) :=s.inputDonorsEnd base+DescentResetDonorBook.words s.contacts s.selectorBits s.shortBits s.lanes
def publicFormatEnd (base : ℕ) :=OriginalBooks.afterHeader s.metaBits s.zeroBits s.shortBits s.shortBits s.lanes (s.donorEnd base)
def stemFormatEnd (base : ℕ) :=s.publicFormatEnd base+DescentOperandPairBook.words 6 s.stemBits s.lanes
def privateArgsEnd (base : ℕ) :=DescentUniformSlotOperands.stop (s.stemFormatEnd base) s.privates
  s.hosts s.groups s.lanes s.argBits
def original (base : ℕ) :=OriginalBooks.afterHeader s.metaBits s.zeroBits s.haloBits s.argBits s.lanes (s.privateArgsEnd base)
def originalEnd (base : ℕ) :=DescentResetOriginalSlots.finish (s.original base) s.rows s.blocks s.candidates
def endAddress (base : ℕ) :=DescentResetCandidatePair.endAddress (s.originalEnd base) s.blocks s.candidates (Nat.clog 2 s.rows)

theorem shift (base : ℕ) : s.endAddress base=base+s.endAddress 0 := by
  have coordinate_shift : s.coordinateEnd base = base+s.coordinateEnd 0 := by
    unfold coordinateEnd
    rw [s.stemSources.extent (s.metaEnd base), s.stemSources.extent (s.metaEnd 0)]
    simp only [metaEnd,masks,rank,Shape.endAddress,Shape.base,Shape.scratch,Shape.size,Shape.width,
      Shape.stride,Shape.rowBits,Shape.rows,Nat.zero_add,Nat.add_assoc]
  simp only [endAddress,originalEnd,original,privateArgsEnd,stemFormatEnd,publicFormatEnd,donorEnd,
    s.donors_shift base,s.donors_shift 0,coordinate_shift,
    DescentResetCandidatePair.endAddress,DescentResetCandidatePair.originalBase,
    DescentResetOriginalSlots.finish,OriginalBooks.afterHeader,DescentUniformSlotOperands.stop,
    DescentResetHaloBroadcast.endAt,Nat.add_assoc]

theorem room (base : ℕ) : base≤ s.endAddress base :=by rw [s.shift];exact Nat.le_add_right ..

end CandidateSheets
end
end Hierarchy.DescentDatedAddressBook

end OAI
