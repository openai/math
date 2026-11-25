import OAI.Hierarchy.DescentOriginalNumberFormatVolume
import OAI.Hierarchy.DescentResetOriginalDonorFunded
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Population estimate for every physically published original-number page. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
open DescentSIMDLookup DescentResetMixedWordRAM CandidateFront
noncomputable section
variable {s : CandidateSheets} (u : s.OriginalInputs)

def donorFactor (s : CandidateSheets) := (s.contacts+1)*2+1

def numberFactor (U V W : ℕ) :=
  staticCost (3+s.coordinate.count)+staticCost 6+staticCost 6+s.originalDonors.coefficient V+
    formatFactor s.blocks s.contacts u.stems s.privates u.signedSlots U W (donorFactor s)+
    staticCost s.privates+staticCost 3

private theorem static_bound {n K E : ℕ} (one : 1≤E) (nFit : n≤K*E) :
    staticCost n≤ staticCost K*E :=by
  unfold staticCost;nlinarith only [one,nFit]

/-- The calibrated dictionary widths are the numerical words actually looked up by the five passes. -/
theorem volume (base U V W h E : ℕ) (one : 1≤E) (rows : s.rows≤E)
    (shared : (h+1)^3*2^(h/2)≤E) (lanes : 0< s.lanes) (M : s.lanes≤h)
    (blocks : 0< s.blocks)
    (key : s.coordinate.dim*s.coordinate.dim+Nat.clog 2 (chunks s.groups s.lanes)≤h/2)
    (casts : max s.stemSources.width s.metaBits*s.lanes≤h/2)
    (args : s.argBits*s.lanes≤h/2)
    (selectors : max s.selectorBits s.shortBits*(s.blocks+1)*s.lanes≤h/2)
    (donor : DescentResetDonorBook.width s.selectorBits s.shortBits s.lanes≤h/2)
    (pub : (u.publicSide base).date.width≤h/2) (stem : 7*s.stemBits*s.lanes≤h/2)
    (priv : (u.privateSide base).width≤h/2)
    (occ : stemEnvelope h s.sparseHosts s.hosts s.groups s.blocks s.lanes s.lanes≤E) :
    u.invoice base U V W ≤ u.numberFactor U V W*E :=by
  have table : 2^(h/2)≤E:=(Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans shared
  have page (a : ℕ) (bound : a≤h/2) : 2^a≤E:=(Nat.pow_le_pow_right (by decide) bound).trans table
  have hpart : s.lanes+1≤(h+1)^3:=by nlinarith only [M,Nat.zero_le h,Nat.zero_le (h*h),Nat.zero_le (h*h*h)]
  have small (a : ℕ) (bound : a*s.lanes≤h/2) : (s.lanes+1)*2^a≤E :=
    (Nat.mul_le_mul hpart (Nat.pow_le_pow_right (by decide)
      ((Nat.le_mul_of_pos_right a lanes).trans bound))).trans shared
  have inBits : s.stemSources.width*s.lanes≤h/2 :=
    (Nat.mul_le_mul_right _ (le_max_left ..)).trans casts
  have outBits : s.metaBits*s.lanes≤h/2 :=
    (Nat.mul_le_mul_right _ (le_max_right ..)).trans casts
  have chart : s.stemSources.coord.layout.size≤(3+s.coordinate.count)*E :=by
    have pad:=DescentDyadicSpan.span_le s.rows
    have lookup:=Nat.mul_le_mul_left s.coordinate.count (page _ key)
    change 2^(Nat.clog 2 s.rows)+s.coordinate.count*2^(s.coordinate.dim*s.coordinate.dim+
      Nat.clog 2 (chunks s.groups s.lanes))≤_
    rw [Nat.add_mul]
    apply Nat.add_le_add _ lookup
    unfold DescentDyadicSpan.span at pad
    omega
  have converted : s.stemSources.pages≤6*E :=by
    change 3*(2*2^(s.stemSources.width*s.lanes))≤_
    have small_:=page _ inBits;omega
  have scalar : DescentResetOriginalZeroHalo.count s.hosts s.groups s.lanes s.metaBits≤6*E :=by
    change 3*s.rows+3*((s.lanes+1)*2^s.metaBits)≤_
    have light:=small _ outBits;omega
  have sign : s.originalDonors.price V≤ s.originalDonors.coefficient V*E :=by
    have raw : s.stemSignedBits≤ s.stemSources.width :=Nat.le_max_left ..
    have top : max s.originalDonors.fieldBits s.originalDonors.metaBits*s.lanes≤h/2 :=
      (Nat.mul_le_mul_right _ (max_le_max_right s.metaBits raw)).trans casts
    exact (s.originalDonors.funded h s.hosts V blocks lanes M top selectors).trans
      (Nat.mul_le_mul_left _ occ)
  let C:=donorFactor s
  have cp : 1≤C:=by dsimp [C,donorFactor];omega
  have sup (a : ℕ) (bound : a≤h/2) : 2^a≤C*E :=
    (page _ bound).trans (Nat.le_mul_of_pos_left E cp)
  have count : (u.publicSide base).count≤C*E :=by
    change (s.contacts+1)*2*2^(DescentResetDonorBook.width s.selectorBits s.shortBits s.lanes)≤_
    exact Nat.mul_le_mul (by dsimp [C,donorFactor];omega) (page _ donor)
  have fmt:=u.format_volume base U W C E one rows count (sup _ pub) (sup _ stem) (sup _ priv)
  have sharedSlots : DescentResetHaloBroadcast.count s.hosts s.groups s.lanes s.argBits≤3*E :=by
    change 2*s.rows+(s.lanes+1)*2^s.argBits≤_
    have light:=small _ args;omega
  have slot : s.privates≤ s.privates*E:=Nat.le_mul_of_pos_right _ one
  have all:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (static_bound one chart) (static_bound one converted)) (static_bound one scalar)) sign) fmt)
    (static_bound one slot)) (static_bound one sharedSlots)
  dsimp only [invoice,numberFactor,C] at *
  nlinarith only [all]

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
