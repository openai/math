import OAI.Hierarchy.ProbeSparseParticipantROM
import OAI.Hierarchy.ProbeSparseRoleBankBounds
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbeFixedWidePacketResident

namespace OAI
/-! # Readiness of the full real sparse ballot on the counted enrollment pages -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart Tagged
open HistoryRoles RoleProgram WideCPU
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width ell unitCost : ℕ)
local notation "P" => v.widePlacement h width
local notation "g" => v.wideDated h width ell unitCost
local notation "W" => wordBits h (2^v.W) copies
local notation "dates" => events v.mesh
local notation "bitDepth" => ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h)
local notation "top" => (v.privateArena P h width).endAddress v.mesh

/-- On an actual dated attempted purchase, all candidate and local-party
fields in the complete packet are read from the original calendar,
public role sheets, and ordinary read-only tables of that same Dated
machine. The only memory agreement is the ROM frame for this date. -/
theorem wide_dated_ballot_ready (rom work : ℕ) (_routes : RouteSettlement.Banks) (_src _tab _dst : ℕ) (_owners : Bank)
    (table : Fin (g).siteDirectorySize→ℕ) (transport : Fin (g).rawEdges→Bool) (initial m : Memory W)
    (j : Fin (dates).length) (a : Attempt) (atDate : (dates).get j=.attempt a)
    (fixed : ∀i,(g).ballotROM rom j≤ i→i<(g).ballotROM rom j+((g).ballot j).advice (g).sites→
      m i=(g).words rom table transport initial i)
    (word : top<2^W) (_mass : v.menu.copiesAt v.copyScale width<2^W)
    (placed : top≤work) (gap : 3*(g).romEnd rom+2≤work) (range : (g).workEnd work<2^W) :
    PublicSheet ((g).ballot j) (g).sites ((g).ballotROM rom j) ((g).ballotStart work j) W
      ((g).fields j ((g).siteROM rom) ((g).siteStride rom) ((g).roleStart work j.castSucc) ((g).roleStart work j.succ)) m := by
  have active : Event.attempt a∈dates:=by rw [← atDate];exact List.get_mem dates j
  have datesLong:=attempt_two_dates v.mesh a active
  have d : (g).roleCount≤((g).ballot j).columns := by
    change v.widePacketDegree≤(v.widePacketShape h width ((dates).get j)).columns
    rw [atDate]
    dsimp only [widePacketShape]
    omega
  have candidates : 0<((g).ballot j).candidates := by
    change 0<(v.widePacketShape h width ((dates).get j)).candidates
    rw [atDate]
    exact (Nat.two_pow_pos h).trans_le (v.date_market_rows h P width a)
  have positiveCols : 0<((g).ballot j).columns := by
    change 0<(v.widePacketShape h width ((dates).get j)).columns
    rw [atDate]
    dsimp only [widePacketShape,wideBallotShape]
    omega
  have ⟨parties,cols⟩:=(g).ballot_ordinals work j (Nat.succ_pos _) candidates positiveCols range
  have old:=(g).role_bank_before_ballot work j j.castSucc (by simp) datesLong d range
  have next:=(g).role_bank_before_ballot work j j.succ (by simp) datesLong d range
  have floor : work≤(g).ballotStart work j := by dsimp only [Dated.ballotStart,offset,Dated.rolesEnd];omega
  have workRoom : work<2^W := by
    dsimp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,Dated.controlStart,endOf,Dated.rolesEnd] at range
    omega
  have banks:=(g).global_banks gap workRoom
  apply (g).ballot_public rom work table transport initial m j fixed _ _ parties cols gap range
  change (let f := v.widePacketFields h width bitDepth ((dates).get j) ((g).siteROM rom)
              ((g).siteStride rom) ((g).roleStart work j.castSucc) ((g).roleStart work j.succ)
          ∀i,(f.selected i).Fits W ((g).ballotStart work j+1) ∧ (f.site i).Fits W ((g).ballotStart work j+1) ∧
            ∀c,(f.value i c).Fits W ((g).ballotStart work j+1))
  rw [atDate]
  intro fields i
  exact v.widePacket_resident h width bitDepth a active ((g).ballotStart work j+1) word
    (by omega) ((g).siteROM rom) ((g).siteStride rom) ((g).roleStart work j.castSucc) ((g).roleStart work j.succ)
    ⟨banks.1.1,banks.1.2.1,banks.1.2.2.trans (Nat.add_le_add_right floor 1)⟩
    ⟨banks.2.1,banks.2.2.1,banks.2.2.2.trans (Nat.add_le_add_right floor 1)⟩ old next i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
