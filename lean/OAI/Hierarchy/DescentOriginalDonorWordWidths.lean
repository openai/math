import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentNamedResetSheets

namespace OAI
/-! Bits allocated by the actual numbered reset for all three public donor fields. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentDatedAddressBook DescentCompiler DescentColonies DescentResetPublicParentWord DescentDenseHostOrder
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Ht" => GroupStage.depthBound D n f g
local notation "Z" => B.reset
local notation "r" => (Z).k-B.terminals.commonDepth
local notation "count" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)


theorem palette_nonempty {n d : ℕ} (P : NonlinearExpanders.Graph n d) (k height : ℕ) :
    0<(DescentDenseHostOrder.roster P k height).card:=by
  classical
  let code : DescentResetHostSize.Code k:=⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let point : DescentCommonHost.Pool P Unit k height:=(false,(),code,.inl none)
  exact Finset.card_pos.mpr ⟨_,Finset.mem_image.mpr ⟨point,Finset.mem_univ _,rfl⟩⟩

theorem numbered_widths (cap lanes : ℕ) :
    let s:=CandidateSheets.fromBoard S ctl.board k tail i D f g cap lanes
    originalChoices B<2^s.selectorBits ∧
      max (originalChoices B) (input.placement.degree+2)<2^s.shortBits ∧
      input.placement.degree+2<2^s.metaBits :=by
  let s:=CandidateSheets.fromBoard S ctl.board k tail i D f g cap lanes
  let localChoices:=DescentResetLocalRoster.rootSlots k (2^n)*(2^n+2^Ht)
  let shapes:=(DescentDenseHostOrder.roster ctl.board k Ht).card
  let top:=max localChoices (max (D+2) shapes)
  have ch : originalChoices B=localChoices:=original_choices B
  have bnd : max localChoices (D+2)≤top:=max_le (le_max_left ..) ((le_max_left ..).trans (le_max_right ..))
  have pos : 0 < shapes:=palette_nonempty ctl.board k Ht
  have more : 0<Nat.clog 2 (shapes+1):=Nat.clog_pos (by decide) (by omega)
  have a : D+2≤2^Nat.clog 2 (D+2):=Nat.le_pow_clog (by decide) _
  have b : 2^Nat.clog 2 (D+2)<2^(Nat.clog 2 (D+2)+Nat.clog 2 (shapes+1)):=
    Nat.pow_lt_pow_right (by decide) (by omega)
  rw [ch,input.branch]
  refine ⟨(Nat.lt_succ_self localChoices).trans_le (Nat.le_pow_clog (by decide) _),
    bnd.trans_lt ((Nat.lt_succ_self top).trans_le (Nat.le_pow_clog (by decide) _)),?_⟩
  exact (a.trans_lt b).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right ..))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
