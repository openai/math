import OAI.Hierarchy.DescentDatedResetOutput
import OAI.Hierarchy.DescentPhysicalResetPeers
import OAI.Hierarchy.DescentRankPortRoster
import OAI.Hierarchy.DescentRankPortChartSpace

namespace OAI
/-! # Compact ranked-window ports from the actor directory and the four stored sparse peers -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty.Chronology DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput) (base : ℕ)
local notation "h₀" => v.sheets.hosts
local notation "g₀" => v.sheets.groups
local notation "m₀" => v.sheets.lanes
local notation "p₀" => v.front.peer.hosts
local notation "b₀" => v.candidateEnd base
local notation "k₀" => DescentRankPortRoster.roof b₀ h₀
local notation "r₀" => DescentRankPortRoster.bank b₀ h₀

def rankPortRegs : DescentRankPortRoster.Inputs :=
  let dir:=v.actor.directory (v.middle.stop base)
  ⟨dir.count,dir.inverse,dir.ranks,(v.front.peer.ports (v.front.peers (v.actorEnd base))).roster⟩

def rankPorts : Ports 4 := DescentScalarHaloPortROM.chart h₀ g₀ m₀ 4 k₀ r₀

private def literalPorts (w : ℕ) : NativePhase w :=
  ⟨DescentScalarHaloPortROM.program h₀ g₀ m₀ 4 w k₀,4+10*DescentScalarHaloPortROM.length h₀ g₀ m₀ 4,
    DescentScalarHaloPortROM.image h₀ g₀ m₀ 4 k₀,@DescentStaticWordColumn.cheap w k₀ _ _⟩

def rankPortPhase (w : ℕ) : NativePhase w :=
  (DescentRankPortRoster.phase w b₀ h₀ p₀ (v.rankPortRegs base)).seq (v.literalPorts base w)

structure RankPortRoom (w : ℕ) : Prop where
  roster : DescentRankPortRoster.Room w b₀ h₀ p₀ (v.rankPortRegs base)
  limit : v.rankPortEnd base<2^w

private theorem literal_room {w : ℕ} (r : v.RankPortRoom base w) :
    k₀+DescentScalarHaloPortROM.length h₀ g₀ m₀ 4<2^w := by
  exact (Nat.le_add_right _ _).trans_lt r.limit

theorem rankPort_any (w : ℕ) (m : Memory w) (r : v.RankPortRoom base w) :
    (v.rankPortPhase base w).Runs m ∧ ∀z,z<b₀ ∨ v.rankPortEnd base≤z →
      (v.rankPortPhase base w).image m z=m z := by
  obtain ⟨first,frame⟩:=DescentRankPortRoster.any r.roster m
  obtain ⟨second,_,keeps,_⟩:=DescentScalarHaloPortROM.mount h₀ g₀ m₀ 4 k₀ r₀
    (DescentRankPortRoster.image b₀ h₀ p₀ (v.rankPortRegs base) m) (v.literal_room base r)
  have a : b₀≤k₀:=Nat.le_add_right ..
  have b : k₀+DescentScalarHaloPortROM.length h₀ g₀ m₀ 4≤v.rankPortEnd base:=Nat.le_add_right ..
  refine ⟨NativePhase.seq_runs _ _ m first second,?_⟩
  intro z hz
  exact (keeps z (by omega)).trans (frame z (by omega))

/-- The compact roster and packed row-address tables are readable in the same final memory. -/
theorem rankPort_mounted {w : ℕ} (m : Memory w) (r : v.RankPortRoom base w) :
    let o:=(v.rankPortPhase base w).image m
    DescentScalarHaloPortROM.Shape h₀ g₀ m₀ 4 k₀ r₀ o ∧
      ∀(i : Fin h₀) (j : Fin 4),
      (i.val<(m (v.rankPortRegs base).count.base).val → i.val<(v.rankPortRegs base).inverse.size) →
      (i.val<(m (v.rankPortRegs base).count.base).val → (m ((v.rankPortRegs base).inverse.base+i.val)).val<p₀) →
      o ((v.rankPorts base).roster.base+(4*i.val+j.val))=
        DescentRankPortRoster.reported h₀ p₀ (v.rankPortRegs base) m i.val j.val := by
  intro o
  obtain ⟨_,statics,keeps,_⟩:=DescentScalarHaloPortROM.mount h₀ g₀ m₀ 4 k₀ r₀
    (DescentRankPortRoster.image b₀ h₀ p₀ (v.rankPortRegs base) m) (v.literal_room base r)
  refine ⟨statics,?_⟩
  intro i j index valid
  have lt : 4*i.val+j.val<4*h₀:=by have :=i.isLt; have :=j.isLt; omega
  have below := (DescentRankPortRoster.bank_fits r.roster).2.2
  have off := lt.trans_le (DescentRankPortRoster.bank_size b₀ h₀)
  have addr : (r₀).base+(4*i.val+j.val)<k₀ := (Nat.add_lt_add_left off _).trans_le below
  exact (keeps _ (.inl addr)).trans (DescentRankPortRoster.read r.roster m i j index valid)

theorem rankPort_price (w : ℕ) : (v.rankPortPhase base w).ticks+
    7*DescentStaticWordColumn.names (v.rankPortPhase base w).program≤
      5000*(h₀+1)+116*(DescentScalarHaloPortROM.length h₀ g₀ m₀ 4+1) := by
  have old:=DescentRankPortRoster.price w b₀ h₀ p₀ (v.rankPortRegs base)
  simp only [rankPortPhase,NativePhase.seq,literalPorts,DescentScalarHaloPortROM.program,
    DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]
  omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
