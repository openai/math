import OAI.Hierarchy.TaggedWideCalendarSpillRow
import OAI.Hierarchy.TaggedWideTerminalSiteTariff
import OAI.Hierarchy.ProbeFixedWideSignedPartyTariff
import OAI.Hierarchy.TaggedWidePartyTariff

namespace OAI
/-! # Per-site charge of a dated, physically seated spill comparator -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing Tagged Tagged.WideControlJoin Tagged.WideStack
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles HistoryRoles.RoleProgram HistoryRoles.Terminal ReportSockets Probe
open WireTelescope WireTelescope.PassMatrix WireTelescope.PassMatrix.PartyPins WideCPU Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "degree" => v.widePacketDegree
local notation "seats" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "roleBits" => TurnShelf.exponent v.wideShelfRoles

theorem spill_width_cap (unitCost w : ℕ) (hw : 0<w) :
    v.wideNeighborCap w unitCost≤(2*(degree*v.wideHistoryUnit unitCost+1))*w := by
  let z:=degree*v.wideHistoryUnit unitCost*w+1
  have depth : Nat.clog 2 z≤Nat.log 2 z+1 :=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr (Nat.lt_pow_succ_log_self (by decide) z).le
  have rounded:2^(Nat.clog 2 z)≤2*z:=(Nat.pow_le_pow_right (by decide : 0<2) depth).trans
    (TurnShelf.dyadic_room z (by simp [z])).2
  exact rounded.trans (by dsimp [z];ring_nf;omega)

private def sourceRate (D r P : ℕ) :=
  3*(266*D+4616*D*D)+r*2308*2^P*(P+2)

private theorem row_bound (D r P e : ℕ) :
    let cap:=2^e
    D*D*(2308*cap*(cap.log2+2))+
      2*(D*cap+D*(cap*(200*e+65))+D*D*(2308*cap*(cap.log2+2)))+
      r*(2308*TurnShelf.width P e*(e+P+2))≤ sourceRate D r P*(cap*(e+1)) := by
  dsimp only
  simp only [TurnShelf.width,Nat.log2_two_pow,sourceRate]
  ring_nf
  omega

/-- Uniform in the height, the date and its actual site. The role capacity
and the number of turn comparators depend only on the fixed protocol. -/
theorem spillRow_tariff (unitCost : ℕ) :
    ∃C K:ℕ,0<K ∧ ∀ {Ex Se Data:Type} [Fintype Ex] [Fintype Se] [Fintype Data]
      (h w : ℕ) (_hw : 0<w) (G : Gate) {T:ℕ} (g : Dated T) (control : ℕ) (j : Fin T) (i : Fin g.sites)
      (words : Bool→Fin degree→Fin (v.wideNeighborCap w unitCost)→SitePins Ex Se Data G⊕Bool)
      (inside : ∀f:SiteControls.Field degree,controlAddress g control j i f<G.u)
      (capacity : v.wideNeighborDigits w unitCost≤G.W+1) (site : Site h (2^v.W) k) (base : ℕ)
      (seat : Fiber (attempts:=v.wideJobs) v.sampler site→Fin degree),
      let net:=spillRow (F:=F) (slots:=seats) (e:=v.wideNeighborDigits w unitCost)
        G g control j i inside words capacity v.sampler site base (fun a b=>v.wide_shelf_role_fit h a.val b) seat
      net.cells+net.internal≤C*(w+1)*(Nat.log 2 (K*w+1)+2)^3 := by
  let K:=2*(degree*v.wideHistoryUnit unitCost+1)
  let C:=sourceRate degree seats roleBits
  refine ⟨C*K,K,by dsimp [K];omega,?_⟩
  intro Ex Se Data exf sef dataf h w _hw G T g control j i words inside capacity site base seat net
  have small := v.spill_width_cap unitCost w _hw
  have bill:=spillRow_bill (F:=F) (slots:=seats) (e:=v.wideNeighborDigits w unitCost)
    G g control j i inside words capacity v.sampler site base (fun a b=>v.wide_shelf_role_fit h a.val b) seat
  have rent:=bill.trans (row_bound degree seats roleBits (v.wideNeighborDigits w unitCost))
  exact rent.trans ((Nat.mul_le_mul_left C (lane_volume (K:=K) (e:=v.wideNeighborDigits w unitCost) small)).trans_eq
    (by simp only [PacketScale.digits];ring))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
