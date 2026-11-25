import OAI.Hierarchy.DescentEarlyReelScale
import OAI.Hierarchy.DescentStageSnapshotTariff
import OAI.Hierarchy.DescentTerminalHostInvoice

namespace OAI
/-! # Snapshots, old-hub moves and the roster share the original reel's open-host account -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorReplay DescentTerminalCohortArena
open DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM Filter
open ThreeFlat.RAM PhysicalProcedure
open scoped Topology
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
variable (rounds f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate rounds reset+capRate G rounds g)*(rounds+1)+8+cutRate rounds f g
local notation "bits" => fun J => groupBits rounds J (hostRate rounds reset) (capRate G rounds g) (cutRate rounds f g)
local notation "sched" => fun J M => stageNumbers G rounds J f g reset M (tail τ J)
local notation "chart" => fun J => 8+capRate G rounds g*((rounds+1)*J)

/-- A measured chronological interval may be inserted between pre-existing physical programs. -/
def FlightInvoice {w : ℕ} (T fund rate : ℕ) (flight : Procedure w) (ticks : ℕ) : Prop :=
  ∀ (front back : Procedure w) (rest originalRate : ℕ),
    (rest+7*names (front.seq back))*(w+1)*T≤originalRate*fund →
    (rest+ticks+7*names ((front.seq flight).seq back))*(w+1)*T≤(originalRate+rate)*fund

private theorem flight_invoice {w T fund rate : ℕ} (flight : Procedure w) (ticks : ℕ)
    (charge : (ticks+7*names flight)*(w+1)*T≤rate*fund) :
    FlightInvoice T fund rate flight ticks := by
  intro front back rest originalRate paid
  rw [names_seq] at paid
  rw [names_seq,names_seq]
  calc
    _ = (rest+7*(names front+names back))*(w+1)*T+(ticks+7*names flight)*(w+1)*T := by ring
    _ ≤ originalRate*fund+rate*fund := Nat.add_le_add paid charge
    _ = _ := by ring

theorem stage_flight_invoice (large : 20≤B) (reserve : 2*localSocketRate G rounds g≤τ)
    (budget : 2*(localSocketRate G rounds g+(τ+κ+4))+Nat.clog 2 G.b*(rounds+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M E w factor first base scratch : ℕ, let S:=sched J M
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let split:=NativeBranch.binLimit (k:=bits J) S
        let U:=G.b^(rounds*J)*G.b
        let s:=S.firstWidth G.b (split*(h/(16*((2^j*U)*split))))
        let frozen:=bits J*((rounds+1)*J)
        let n:=E*2^frozen
        let H:=S.hostSize S.length
        ∀(A : Snapshots (bits J)) (rank : Fin n→ℕ) (hops : ℕ→Hop) (src : Bank)
          (room : stop first frozen (chart J) n H<2^w),
          A.hosts=S.hostSize → 2^h≤2*(M*S.copies) → 0<w → w≤factor*h →
          let boot:=(A.program w base frozen S.length).seq (Snapshots.seedProgram w scratch rank)
          let fly:=(steps w n (schedule hops S.length)).seq
            (DescentTerminalCohortArena.machine first frozen (chart J) n H room src)
          let clock:=A.clocks frozen S.length+(4+10*n)+
            (clocks n (schedule hops S.length)+ticks first frozen (chart J) n H room src)
          FlightInvoice (2^J) ((S.copies*s)*(M+2^J*E)) (128000*factor) (boot.seq fly) clock := by
  filter_upwards [stage_snapshot_tariff G rounds f g reset τ B (by omega) reserve,
    early_native_packing G rounds f g reset τ B large reserve budget] with h snapshot packing
  intro J M E w factor first base scratch S j split U s frozen n H A rank hops src room issued support positive
    arch boot fly clock
  obtain ⟨_,_,power,_,high⟩:=packing M
  let a:=localSocketRate G rounds g
  have order:j≤a*(J+1):=(native_socket_scale G rounds J f g reset M τ).1
  have index:j≤tail τ J:=order.trans (Nat.mul_le_mul_right _ (by dsimp [a];omega))
  let cap:=2^(capRate G rounds g*((rounds+1)*J)+8+cutRate rounds f g)
  have padding:32≤cap:=by
    change 2^5≤2^_
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have bands:2^j*32≤2^(tail τ J)*cap:=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) index) padding
  have paid:1*h≤ s*(2^(tail τ J)*cap):=calc
    _ ≤ 32*(2^j*s) := by simpa only [one_mul] using high
    _ = s*(2^j*32) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ bands
  have hosted:=terminal_host_price G rounds J f g reset M (tail τ J) h s 1 paid
  have position:H*h*2^J≤M*(S.copies*s):=by simpa only [Nat.mul_one] using hosted
  have actual:=snapshot M E s w factor first base scratch A rank hops src room issued support power arch high position
  let fee:=clock+7*names (boot.seq fly)
  change fee*w*2^J≤64000*factor*((S.copies*s)*(M+2^J*E)) at actual
  apply flight_invoice
  change fee*(w+1)*2^J≤_
  calc
    _ ≤ fee*(w+w)*2^J := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = 2*(fee*w*2^J) := by ring
    _ ≤ _ := (Nat.mul_le_mul_left 2 actual).trans_eq (by ring)

end
end Hierarchy.DescentSixParty

end OAI
