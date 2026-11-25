import OAI.Hierarchy.DescentPhysicalResetOriginalSeries
import OAI.Hierarchy.DescentResetOriginalDonorFit

namespace OAI
/-! Numeric fit of the original-number pipeline from its earlier measured register reads. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets
open ProtocolRAM DescentSIMDLookup DescentResetMixedWordRAM
noncomputable section

/-- Successive original page banks, including the first field projection and the dense donor output. -/
theorem number_cuts (s : CandidateSheets) (base : ℕ) :
    s.metaEnd base≤ s.inputDonorsEnd base ∧ s.inputDonorsEnd base≤ s.publicFormatEnd base ∧
    s.publicFormatEnd base≤ s.stemFormatEnd base ∧ s.stemFormatEnd base≤ s.privateArgsEnd base ∧
    s.privateArgsEnd base≤ s.original base ∧ s.original base≤ s.originalEnd base := by
  have first : s.metaEnd base≤ s.inputDonorsEnd base :=by
    rw [s.donors_shift,coordinateEnd,s.stemSources.extent];omega
  refine ⟨first,?_,Nat.le_add_right ..,?_,Nat.le_add_right ..,Nat.le_add_right ..⟩
  · unfold publicFormatEnd donorEnd OriginalBooks.afterHeader
    omega
  · unfold privateArgsEnd DescentUniformSlotOperands.stop DescentResetHaloBroadcast.endAt
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..

namespace OriginalInputs
variable {s : CandidateSheets} (u : s.OriginalInputs) (base w : ℕ)

theorem of_reads (donors : s.originalDonors.Ready (s.inputDonorsBase base) u.sensor w)
    («meta» : ∀x j,(u.sources.meta x j).Fits w (s.inputDonorsEnd base))
    (z : ∀x,(u.sources.zero x).Fits w (s.inputDonorsEnd base))
    (self : ∀x,(u.sources.self x).Fits w (s.inputDonorsEnd base))
    (shape : ∀x,(u.sources.shape x).Fits w (s.inputDonorsEnd base))
    (label : ∀x f j,(u.sources.label x f j).Fits w (s.inputDonorsEnd base))
    (cargo : ∀x f t j,(u.sources.cargo x f t j).Fits w (s.inputDonorsEnd base))
    (stems : ∀x j t,(u.stem x j t).Fits w (s.publicFormatEnd base))
    (privateMeta : ∀x j,(u.privateMeta x j).Fits w (s.inputDonorsEnd base))
    (zero : ∀x,(u.zero x).Fits w (s.inputDonorsEnd base))
    (halo : ∀x,(u.halo x).Fits w (s.inputDonorsEnd base))
    (count : s.privates≤2^s.argBits) (roof : s.originalEnd base<2^w) : u.Room base w := by
  obtain ⟨_,a,b,c,d,e⟩:=s.number_cuts base
  have before:=((a.trans b).trans c)
  have reserved: s.privateArgsEnd base<2^w:=(d.trans e).trans_lt roof
  refine ⟨donors,⟨«meta»,z,self,shape,label,cargo,?_,?_,roof⟩,
    ⟨stems,?_,roof⟩,⟨le_rfl,roof,?_,?_,?_,?_⟩,count,a,b,c⟩
  · exact le_rfl
  · exact (b.trans c).trans d
  · exact c.trans d
  · intro i
    exact ProtocolRAMGeneratedWrite.fits_mono _ before (privateMeta _ _)
  · intro i
    exact ProtocolRAMGeneratedWrite.fits_mono _ before (zero _)
  · intro i
    exact ProtocolRAMGeneratedWrite.fits_mono _ before (halo _)
  · intro i
    exact DescentUniformSlotOperands.fits (s.stemFormatEnd base) s.hosts s.groups s.lanes s.argBits
      (finProdFinEquiv.symm i).2 reserved

end OriginalInputs
end
end Hierarchy.DescentDatedAddressBook.CandidateSheets

end OAI
