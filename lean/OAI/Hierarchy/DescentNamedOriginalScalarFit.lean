import OAI.Hierarchy.DescentPhysicalNamedOriginals
import OAI.Hierarchy.DescentResetPeerJointAuxRun

namespace OAI
/-! # Address bounds for the original zero, self rank and shape operands -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (v : ResetOutput) {w : ℕ}

theorem original_scalar_order (b : ℕ) :
    v.jointEnd b ≤ v.originalWordsBase b ∧ v.originalWordsBase b ≤ v.originalDonorBase b ∧
    v.originalDonorBase b ≤ v.sheets.inputDonorsEnd (v.remap b).endAddress := by
  let s := v.sheets
  let r := (v.remap b).endAddress
  have privateRoom := v.privateShape.cuts (v.jointEnd b)
  have compactRoom : v.jointEnd b ≤ r :=
    (privateRoom.1.trans privateRoom.2).trans (Nat.le_add_right (v.privateEnd b) (v.remap b).size)
  have layerRoom (L : DescentResetCandidateDate.Shape) (fieldCount bits : ℕ) :
      L.first ≤ L.endAddress fieldCount bits := by
    obtain ⟨first, scratch, last⟩ := L.ordered fieldCount bits
    exact ((first.trans (Nat.le_add_right _ L.rows)).trans scratch).trans last
  have rankRoom : r ≤ s.metaEnd r :=
    (layerRoom (s.rank r) 5 s.metaBits).trans (layerRoom (s.masks r) 9 s.metaBits)
  have coordinateRoom : s.metaEnd r ≤ v.originalWordsBase b := by
    change s.metaEnd r ≤ s.stemSources.endAddress (s.metaEnd r)
    rw [s.stemSources.extent]
    exact Nat.le_add_right ..
  refine ⟨(compactRoom.trans rankRoom).trans coordinateRoom, ?_, ?_⟩
  · exact (Nat.le_add_right ..).trans (DescentResetOriginalZeroHalo.written_le ..)
  · change s.inputDonorsBase r ≤ s.originalDonors.endAddress (s.inputDonorsBase r)
    rw [s.originalDonors.extent]
    exact Nat.le_add_right ..

theorem originalAux_fits (b : ℕ) (j : Fin 4)
    (roof : v.jointEnd b < 2^w) : (v.originalAux b j).Fits w (v.originalWordsBase b) := by
  have fit := (DescentResetPeerJointPacked.Aux.aux_bank (v.massEnd b) v.sheets.hosts
    v.front.peer.hosts v.sheets.groups v.sheets.lanes v.sheets.metaBits j roof).1
  exact ⟨fit.1, fit.2.1, fit.2.2.trans (v.original_scalar_order b).1⟩

theorem original_scalar_fits (b N : ℕ)
    (roof : v.sheets.inputDonorsEnd (v.remap b).endAddress < 2^w) :
    let endAt := v.sheets.inputDonorsEnd (v.remap b).endAddress
    (∀ x, (v.originalZero b x).Fits w endAt) ∧ (v.originalHalo b).Fits w endAt ∧
    (∀ x, ((v.originalPrior b N).self x).Fits w endAt) ∧
    (∀ x, ((v.originalPrior b N).shape x).Fits w endAt) := by
  intro endAt
  obtain ⟨joint, scalar, done⟩ := v.original_scalar_order b
  have word : v.originalDonorBase b < 2^w := done.trans_lt roof
  have earlier := (joint.trans scalar).trans_lt word
  have fit (k : Fin 3) (j : Fin 4) :
      (DescentResetOriginalZeroHalo.field (v.originalWordsBase b) v.sheets.hosts v.sheets.groups
        v.sheets.lanes v.sheets.metaBits k (v.originalAux b j)).Fits w endAt :=
    ProtocolRAMGeneratedWrite.fits_mono _ done (DescentResetOriginalZeroHalo.field_fits
      _ _ _ _ _ k _ (v.originalAux_fits b j earlier) word)
  exact ⟨fun x => ProtocolRAMGeneratedWrite.fits_mono _ done
    (DescentResetOriginalZeroHalo.zero_fits _ _ _ _ _ x word),
    fit 2 0, fun _ => fit 0 0, fun _ => fit 1 1⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
