import OAI.Hierarchy.DescentFrontOriginalBounds
import OAI.Hierarchy.DescentPeerCatalogFits
import OAI.Hierarchy.DescentCanonicalFrontSources

namespace OAI
/-! # Static fit of the original reset scans from the measured predecessor's bank layout -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentCompiler DescentSixParty DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local.Stage
open DescentResetStemPackedIssue DescentResetPeerUnionRAM DescentContactSenderDate ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section
set_option quotPrecheck false
variable {n h w : ℕ} (S : DescentCompiler.AtomSchedule) (board : NonlinearExpanders.Graph n h)
    (k tail age degree f g M nextM field «meta» C packet : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S board k tail age degree f g M nextM field «meta» C packet calendar
local notation "cap" => (calendar.take age).prod*256
local notation "H" => S.hostSize age
local notation "J" => 2^(S.groupWidth k tail age)
variable (base : ℕ) (old : EarlierBanks degree k ((calendar.take age).prod*256) n) (flags count inverse : Bank)
local notation "o₀" => calendarOriginals S board k tail age degree f g M nextM field «meta» C packet calendar base old
local notation "scene" => (A).fromOriginals base o₀ flags count inverse
local notation "p₀" => (A).peer
local notation "L" => (A).rawTables base
local notation "C₀" => (A).contactLayout base
local notation "d₀" => (A).donorStart base
local notation "d₁" => (A).donorEnd base
local notation "src" => (A).originalPages base old.roots old.actorStarts old.actorData
local notation "visible" => (A).peers base
local notation "out" => (p₀).endAddress visible

set_option maxRecDepth 4096 in
theorem calendar_scene_inputs (safe : old.Bounds H J M w base)
    (small : 4 < 2^w) (hosts : H < 2^w) (degrees : degree+1 < 2^w)
    (packed : M*max (field*8) (p₀).bits ≤ w/2) (endRoom : out < 2^w) :
    (∀q j,((scene).evidence.source q j).Fits w base) ∧
      (A).donor.Space d₀ (scene).donor w ∧
      (C₀).Space (scene).boardReads ((A).sensor base scene) w ∧
      (p₀).Room (scene).peers visible w := by
  have pp:=(p₀).ordered visible
  have pc : visible ≤ out:=pp.1.trans (pp.2.1.trans (pp.2.2.1.trans pp.2.2.2))
  have t : (C₀).endAddress < 2^w:=pc.trans_lt endRoom
  obtain ⟨c₁,c₂,c₃,c₄,c₅⟩:=(C₀).ordered
  have ec : d₁ ≤ visible:=c₁.trans (c₂.trans (c₃.trans (c₄.trans c₅)))
  obtain ⟨d₁₀,d₂,d₃⟩:=(A).donor.ordered d₀
  have ed : d₀ ≤ d₁:=d₁₀.trans (d₂.trans d₃)
  have key : base ≤ (A).oldKeys base:=by
    dsimp [oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start]
    omega
  have er : (L).endAddress=d₀:=(A).tables_end base rfl
  have afterKey : (A).oldKeys base ≤ d₀:=by
    rw [←er,(L).end_eq]
    exact Nat.le_add_right ..
  have pre:=key.trans afterKey
  have donors : (A).donor.Space d₀ (scene).donor w := by
    have limit : d₁+H*chunks J M ≤ visible := by
      have o:=(C₀).old.ordered (C₀).oldFields (C₀).fieldBits
      have bound:=Nat.add_le_add_right o.1 ((C₀).old.rows)
      exact bound.trans (o.2.1.trans (o.2.2.trans (c₂.trans (c₃.trans (c₄.trans c₅)))))
    exact ⟨Layout.prior_fits_before (Ht:=0) (b:=0) safe.sender pre,
      Chooser.bank_before safe.donorRoster pre,safe.donorRows,hosts,degrees,limit.trans_lt t⟩
  have marker : (C₀).Space (scene).boardReads ((A).sensor base scene) w:=
    (A).donor.markerSpace d₀ (p₀).shapes (p₀).bits old.donor donors t packed
  have reads : ∀j chunk,((PeerCatalog.terms L C₀ src).all j chunk).Fits w visible := by
    apply PeerCatalog.term_fits
    · intro j
      exact (A).issued_key_fits base (o₀).evidence (o₀).shape old.roots old.actorStarts old.actorData j
        ((afterKey.trans (ed.trans ec)).trans_lt t)
    · exact fun s r=>Chooser.bank_before (safe.page s r) key
    · exact Chooser.bank_before safe.starts key
    · exact Chooser.bank_before safe.scene key
    · exact er.le.trans ed
    · exact t
  refine ⟨?_,donors,marker,?_,small,endRoom⟩
  · intro q j
    let pair:=((DescentResetStemPackedIssue.ordinal (2^k) cap).symm q).2
    exact DescentResetStemKey.readers_fit old.ports old.window base safe.window safe.tagged pair.1 pair.2 j
  · refine ⟨Chooser.bank_before safe.roster (pre.trans (ed.trans ec)),safe.positions,?_,pp.2.1.trans_lt
      ((pp.2.2.1.trans pp.2.2.2).trans_lt endRoom)⟩
    exact fun j c=>reads (j.cast (o₀).shape.count) (c.cast (o₀).shape.chunks)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
