import OAI.Hierarchy.DescentResidentDonorPlacement

namespace OAI
/-! # Readable intervals of the issued donor's common rank and hub directories -/
namespace Hierarchy.DescentRawCablePanel.DonorChartBook
open DescentHaloPackedRebase DescentSIMDLookup DescentPackedColony ProtocolRAM DepotRAM
variable (H G M P base : ℕ) (values : Bank)
local notation "rows" => H*chunks G M
local notation "leaf" => pages M P
local notation "roof" => base+2*(words H G M P+1)

theorem room {w stop : ℕ} (placed : roof≤ stop) (space : stop<2^w)
    (value : values.Fits w stop) (size : H*P≤values.size) :
    Fits (tables H G M P base values) H G M w stop := by
  have n:=ceilPage rows
  have d:=ceilPage leaf
  have top : base+2*(rows+(rows+P*leaf)+1)≤ stop:=placed
  refine ⟨value,bankFits _ ?_ space,bankFits _ ?_ space,fun a=>bankFits _ ?_ space,
    size,n.1,n.1,fun _=>d.1⟩
  · change base+2^(Nat.clog 2 rows)≤ stop;omega
  · change base+rows+2^(Nat.clog 2 rows)≤ stop;omega
  · have span:=Nat.mul_le_mul_right leaf (Nat.succ_le_of_lt a.isLt)
    rw [Nat.succ_mul] at span
    have lo : leaf≤P*leaf:=by omega
    change base+rows+rows+a.val*leaf+2^(Nat.clog 2 leaf)≤ stop
    omega

end Hierarchy.DescentRawCablePanel.DonorChartBook

namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement
open DescentPacking.PackedMatch.Local DescentHaloWalkRAM DescentSIMDLookup DescentPackedColony ProtocolRAM
variable (H G M D input base : ℕ) (adj hub : Bank)
local notation "P" => breadth D
local notation "rows" => H*chunks G M
local notation "paths" => H*P
local notation "L" => layout H G M D input base adj hub
local notation "roof" => endAddress H G M D input base
local notation "end₀" => rowEnd H G M D input base
local notation "rp" => rankBase H G M D input base
local notation "hp" => hubBase H G M D input base
local notation "bp" => bookBase H G M D input base
local notation "own" => Owners.Board.venue input M (Dynamic.Layout.ownerBase L) rows

theorem directories {w stop : ℕ} (placed : roof≤ stop) (space : stop<2^w) :
    DescentHaloPackedRebase.Fits (DonorHeaders.shelf H G M D (L).literal (L).rankOut) H G M w stop ∧
    DescentHaloPackedRebase.Fits (DonorHeaders.shelf H G M D (L).literal (L).hubOut) H G M w stop := by
  have levels : rp+page paths≤bp ∧ hp+page paths≤bp:=by
    dsimp [bookBase,hubBase];omega
  have tabs : bp≤ stop:=(Nat.le_add_right ..).trans placed
  have ranked := bankFits (topBank rp paths) (levels.1.trans tabs) space
  have flagged := bankFits (topBank hp paths) (levels.2.trans tabs) space
  exact ⟨DonorChartBook.room H G M P bp _ placed space ranked (ceilPage paths).1,
    DonorChartBook.room H G M P bp _ placed space flagged (ceilPage paths).1⟩

theorem earlier {stop : ℕ} (placed : roof≤ stop) : (L).ownerBase≤ stop := by
  have h₁ : (L).ownerBase≤own :=by
    calc
      (L).ownerBase ≤ Owners.Board.rom (L).ownerBase rows := Nat.le_add_right _ _
      _ ≤ Owners.Board.rom (L).ownerBase rows + 2^(input*M) := Nat.le_add_right _ _
      _ ≤ own := Nat.le_add_right _ _
  have h₂ : own≤end₀ :=Nat.le_add_right ..
  have h₃ : end₀≤roof:=by unfold endAddress bookBase hubBase rankBase;omega
  exact h₁.trans (h₂.trans (h₃.trans placed))

theorem ownerAccessible {w stop : ℕ} (placed : roof≤ stop) (space : stop<2^w)
    (ports : Ports D) (parent : Bank) (previous : Accessible ports parent H G M w (L).ownerBase) :
    Accessible ports (Owners.Board.bank own rows) H G M w stop := by
  have front:=earlier H G M D input base adj hub placed
  have mono (a : Bank) (b : a.Fits w (L).ownerBase) : a.Fits w stop:=⟨b.1,b.2.1,b.2.2.trans front⟩
  have room : end₀≤roof:=by unfold endAddress bookBase hubBase rankBase;omega
  exact ⟨fun j=>mono _ (previous.ids j),previous.idsRoom,mono _ previous.roster,previous.rosterRoom,
    mono _ previous.offsets,previous.offRoom,mono _ previous.chunks,previous.chunkRoom,
    bankFits _ (room.trans placed) space,(ceilPage rows).1⟩

theorem activeRoom {w stop : ℕ} (placed : (L).ownerBase≤ stop) (space : stop<2^w) :
    (RootTables.liveBank H G M D base).Fits w stop ∧ rows≤(RootTables.liveBank H G M D base).size := by
  have rr:=ceilPage rows
  have levels : base+2*(6*paths+rows+1)≤ stop:=placed
  refine ⟨bankFits _ ?_ space,rr.1⟩
  change base+6*paths+2^(Nat.clog 2 rows)≤ stop
  omega


end Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement

end OAI
