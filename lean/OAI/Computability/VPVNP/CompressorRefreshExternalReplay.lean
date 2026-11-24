import OAI.Computability.VPVNP.CompressorRefreshFrontFrame
import OAI.Computability.VPVNP.CompressorRecordRefreshInputs

/-!
# Replaying the three ordered external refresh scans

The prepared old incidence data determine the intermediate bundle table and the
initial segment cursor. Uniqueness of each deterministic run identifies these states
in the particular raw reports selected by the complete degree-refresh execution.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.FrontFrame
open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh StageFrame SourceTransport Allocation NewSlots
open RefreshRAM (AtCursor)

variable {w a g : ℕ} (X : State a (a+g)) (T : IncidenceDirectory w) (a₀ dH t stride start : ℕ)
local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P w
local notation "S" => Plan.segments P
local notation "N" => Plan.sites P
local notation "L" => (word (bits := w) (2^g))
local notation "O" => IncidenceDirectory.baseOrder X

/-- Each stage of the actual physical prepass returns consecutive ordinals and
accesses only its proven footprint, before a scheduler installs its own frame. -/
theorem external_scans (before : ∀ c, (T.column c).val+S ≤ start) (room : (P).stop < 2^w)
    (widths : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^w)
    (m : Memory w) (rep : T.Represents X m) (rg rd re : List (Report w))
    (fit : S ≤ 2^w) (raw : ExternalReports X O Q L T.width T.baseOut T.shift m fit rg rd re) :
    (Scanned 0 S rg ∧ Reads (OldCell T S) (eventLog rg) ∧ Writes (LevelCell P) (eventLog rg)) ∧
    (Scanned 0 N rd ∧ Reads (OldCell T S) (eventLog rd) ∧ Writes (LevelCell P) (eventLog rd)) ∧
    (Scanned 0 S re ∧ Reads (LevelCell P) (eventLog re) ∧ Writes (LevelCell P) (eventLog re)) := by
  have layout := prepare_layout X T a₀ dH t stride start before room
  have ns : N ≤ S := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
  have nb := (Nat.le_mul_of_pos_right (Fintype.card X.Base*2^a) (Nat.two_pow_pos g)).trans (ns.trans fit)
  have nl : 2^(a+g) ≤ 2^w := by
    rw [pow_add]
    have lim : Fintype.card X.Base * (2^a * 2^g) ≤ 2^w := by rw [← Nat.mul_assoc]; exact ns.trans fit
    exact (Nat.le_mul_of_pos_left _ Fintype.card_pos).trans lim
  let gw := gatherWords Q L T.width
  let dw := directoryWords Q L T.baseOut T.shift
  have base := rep.refresh_base X T m dw layout.lanes rfl rfl nb nl
  obtain ⟨rg',rd',re',raw',mid,init⟩ := external_phases_stages X O Q L T.width T.baseOut T.shift
    layout.degree layout.lanes layout.regions layout.directory m (rep.refresh_widths X T m gw rfl widths)
    base layout.gather layout.baseApart widths
  obtain ⟨hg,hd,he,_⟩ := raw
  obtain ⟨hg',hd',_,_⟩ := raw'
  have eg : rg' = rg := Option.some.inj (hg'.symm.trans hg)
  subst rg'
  have ed : rd' = rd := Option.some.inj (hd'.symm.trans hd)
  subst rd'
  let ord := bundleOrder g O
  let A : RefreshRAM.Input w := graphInput (splitSlots X) ord (splitWidths X)
  have dir : Directory (splitSlots X) ord (splitWidths X) Q A fit :=
    graphInput_directory (splitSlots X) ord (splitWidths X) Q layout.degree widths
  have leg := directory_legal (splitSlots X) ord (splitWidths X) Q A dir widths
  obtain ⟨vg,_,gg⟩ := gather_scan X T a₀ dH t stride start before room m rg hg
  obtain ⟨vd,_,gd⟩ := bundles_scan X T a₀ dH t stride start before room _ mid rd hd
  obtain ⟨ve,_,ge⟩ := offsets_scan X a₀ dH t stride start room layout.regions A leg _ init re he
  exact ⟨⟨vg,gg⟩,⟨vd,gd⟩,ve,ge⟩

end CompressorRecords.PortRefresh.FrontFrame

end VPVNP
end Computability
end OAI
