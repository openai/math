import OAI.Hierarchy.DescentResetOriginalDonorRate
import OAI.Hierarchy.DescentDatedCandidateSheets
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Uniform address exponent of the candidate, donor, and original-code sheets -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets
open DescentSIMDLookup DescentResetCandidateDate DescentResetMixedWordRAM Filter
noncomputable section
variable {ι : ℕ→Type*} (s : ∀h,ι h→CandidateSheets)

/-- Scalar field bounds and the actual dictionary exponents at an original-cable date. -/
structure ScalarRoom : Prop where
  blocks : Bounded (fun h i=>(s h i).blocks)
  hosts : Bounded (fun h i=>(s h i).hosts)
  groups : Bounded (fun h i=>(s h i).groups)
  lanes : Bounded (fun h i=>(s h i).lanes)
  candidates : Bounded (fun h i=>(s h i).candidates)
  jobs : Bounded (fun h i=>(s h i).jobs)
  contacts : Bounded (fun h i=>(s h i).contacts)
  privates : Bounded (fun h i=>(s h i).privates)
  originalDonors : DescentResetOriginalDonors.Layout.ScalarRoom (fun h i=>(s h i).originalDonors)
  haloDigits : Bounded fun h i=>2^(s h i).metaBits
  originalOperands : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).stemSources.width*(s h i).lanes≤C*h
  oldMatrix : Bounded (fun h i=>2^((s h i).stemDimension*(s h i).stemDimension))
  oldBlocks : Bounded (fun h i=>2^(s h i).stemFine)
  oldResidual : Bounded (fun h i=>2^(s h i).stemResidual)
  pages : ∃C : ℕ,∀ᶠ h : ℕ in atTop,∀i,let a:=s h i
    (a.metaBits*9+a.metaBits)*a.lanes≤C*h ∧
    DescentResetDonorBook.width a.selectorBits a.shortBits a.lanes≤C*h ∧
    Book.unit a.metaBits a.zeroBits a.shortBits a.shortBits*a.lanes≤C*h ∧
    DescentOperandPairBook.unit 6 a.stemBits*a.lanes≤C*h ∧ a.argBits≤C*h ∧
    Book.unit a.metaBits a.zeroBits a.haloBits a.argBits*a.lanes≤C*h

private theorem pack_width {key pitch : ∀h,ι h→ℕ} (width : Bounded (fun h i=>2^(key h i)))
    (padded : Bounded (fun h i=>2^(pitch h i))) : Bounded (fun h i=>2^(max (key h i) (pitch h i))) := by
  apply (width.max' padded).of_le
  intro h i
  rcases le_total (key h i) (pitch h i) with right|left
  · rw [max_eq_right right]
    exact le_max_right ..
  · rw [max_eq_left left]
    exact le_max_left ..

theorem rate (r : ScalarRoom s) : Bounded (fun h i=>(s h i).endAddress 0) := by
  let c (n : ℕ) := Bounded.const (ι:=ι) n
  have batches : Bounded (fun h i=>chunks (s h i).groups (s h i).lanes) :=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows : Bounded (fun h i=>(s h i).rows) := r.hosts.mul batches
  obtain ⟨C,room⟩:=r.pages
  have nine:=Bounded.pow_of_linear (K:=C) (room.mono fun h m i=>(m i).1)
  have five : Bounded (fun h i=>2^(((s h i).metaBits*5+(s h i).metaBits)*(s h i).lanes)) := by
    apply nine.of_le
    intro h i
    exact Nat.pow_le_pow_right (by decide : 0<2)
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by decide : 5≤9)) _))
  have donor:=Bounded.pow_of_linear (K:=C) (room.mono fun h m i=>(m i).2.1)
  have public_:=Bounded.pow_of_linear (K:=C) (room.mono fun h m i=>(m i).2.2.1)
  have stem:=Bounded.pow_of_linear (K:=C) (room.mono fun h m i=>(m i).2.2.2.1)
  have args:=Bounded.pow_of_linear (K:=C) (room.mono fun h m i=>(m i).2.2.2.2.1)
  have private_:=Bounded.pow_of_linear (K:=C) (room.mono fun h m i=>(m i).2.2.2.2.2)
  have rank : Bounded (fun h i=>((s h i).rank 0).endAddress 5 (s h i).metaBits) :=
    ((((c 0).add ((c (5*2+2)).mul (pack_width five rows.padded))).add rows.padded).add
      (((c 3).mul r.jobs).mul rows.padded))
  have masks : Bounded (fun h i=>(s h i).metaEnd 0) :=
    ((rank.add ((c (9*2+2)).mul (pack_width nine rows.padded))).add rows.padded).add (r.jobs.mul rows.padded)
  have selected : Bounded (fun h i=>(s h i).coordinate.endAddress 0) :=by
    apply ((((c 2).mul rows).add (c 1)).add (((c 3).mul (r.oldBlocks.mul r.oldResidual)).mul
      (r.oldMatrix.mul (((c 2).mul batches).add (c 1))))).of_le
    intro h i
    exact (s h i).coordinate.size_le
  obtain ⟨J,fit⟩:=r.originalOperands
  have casts:=(c 3).mul ((c 2).mul (Bounded.pow_of_linear (K:=J) fit))
  have reach : Bounded (fun h i=>(s h i).coordinateEnd 0) :=by
    apply ((masks.add selected).add casts).of_le
    intro h i
    change (s h i).coordinate.endAddress ((s h i).metaEnd 0)+(s h i).stemSources.pages≤_
    rw [(s h i).coordinate.extent]
    exact le_rfl
  have lookup:=((r.lanes.add (c 1)).mul r.haloDigits)
  have count:=((c 3).mul rows).add ((c 3).mul lookup)
  have haloSpan : Bounded (fun h i=>let v:=s h i;DescentResetOriginalZeroHalo.endAddress 0 v.hosts v.groups v.lanes v.metaBits) :=by
    apply (((c 0).add ((c 3).mul count)).add (c 2)).of_le
    intro h i
    exact DescentResetOriginalZeroHalo.extent ..
  have source : Bounded (fun h i=>(s h i).inputDonorsEnd 0) :=by
    apply (reach.add (haloSpan.add (DescentResetOriginalDonors.Layout.rate _ r.originalDonors))).of_le
    intro h i
    rw [(s h i).donors_shift]
  have soFar : Bounded (fun h i=>(s h i).stemFormatEnd 0) :=
    ((source.add (((r.contacts.add (c 1)).mul (c 2)).mul donor)).add ((c 12).mul public_)).add
      ((c (6+2)).mul ((c 2).mul stem))
  have halo : Bounded (fun h i=>DescentResetHaloBroadcast.count (s h i).hosts (s h i).groups (s h i).lanes (s h i).argBits) :=
    ((c 2).mul rows).add ((r.lanes.add (c 1)).mul args)
  have formats : Bounded (fun h i=>(s h i).original 0) :=
    (((soFar.add r.privates).add ((c 2).mul rows)).add (halo.add (c 1)).padded).add ((c 12).mul private_)
  have sheet:=(r.blocks.mul r.candidates).mul rows.padded
  exact ((formats.add sheet).add sheet).add sheet

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets

end OAI
