import OAI.Hierarchy.DescentEarlyReelFlight
import OAI.Hierarchy.DescentPreflightOpenPrice
import OAI.Hierarchy.DescentTerminalFixedReplay

namespace OAI
/-! # The literal frozen replay, census and public packet-home program in the original host budget -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorReplay DescentTerminalCohortArena
open DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM Filter
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "bits" => fun J=>groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "sched" => fun J M=>stageNumbers G t J f g reset M (tail τ J)

theorem stage_replay_open_invoice (large : 20≤B) (reserve : 2*localSocketRate G t g≤τ)
    (budget : 2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M E w factor base censusAt : ℕ, let S:=sched J M
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let k:=bits J
        let dim:=S.groupWidth k (tail τ J) 0+k
        let r:=dim-2*j
        let W:=NativeBranch.binLimit (k:=bits J) S
        let U:=G.b^(t*J)*G.b
        let s:=S.firstWidth G.b (W*(h/(16*((2^j*U)*W))))
        ∀(A : Snapshots k) (rank : Fin (E*2^(k*S.length))→ℕ),
          let cal:DescentTerminalFixedReplay.Calendar k:=
            ⟨A,S.length,k*S.length,8+S.capGain*S.length,E,j,r,S.groupWidth k (tail τ J) S.length+k,S.hostSize S.length,rank⟩
          ∀(room : cal.stop censusAt<2^w), A.hosts=S.hostSize → 2^h≤2*(M*S.copies) →
            0<w → w+1≤factor*h →
            FlightInvoice (2^J) ((S.copies*s)*(M+2^J*E)) ((128000+262144)*factor)
              (cal.program base censusAt room) (cal.cost base censusAt room) := by
  filter_upwards [stage_flight_invoice G t f g reset τ B large reserve budget,
    early_native_packing G t f g reset τ B large reserve budget,Filter.eventually_ge_atTop 10] with h air pack hLarge
  intro J M E w factor base censusAt S j k dim r W U s A rank cal room hosts support word arch
  obtain ⟨shape,population,power,_,packed⟩:=pack M
  have small:j≤tail τ J:=
    (native_socket_scale G t J f g reset M τ).1.trans (Nat.mul_le_mul_right _ (by omega))
  have lower : j≤cal.kept := by
    change j≤S.groupWidth k (tail τ J) S.length+k
    simp only [AtomSchedule.groupWidth,Nat.sub_self,Nat.mul_zero,Nat.add_zero]
    omega
  have packedShape : dim=j+(j+r):=shape
  have upper : cal.kept≤j+(j+r) := by
    rw [←packedShape]
    change S.groupWidth k (tail τ J) S.length+k≤S.groupWidth k (tail τ J) 0+k
    simp [AtomSchedule.groupWidth]
  let hop:=A.hop base (k*S.length) (cal.scratch base) cal.cohorts
  let boot:=(A.program w base (k*S.length) S.length).seq (Snapshots.seedProgram w (cal.scratch base) rank)
  let fly:=(steps w cal.cohorts (schedule hop S.length)).seq
    (DescentTerminalCohortArena.machine censusAt (k*S.length) cal.cohortBits cal.cohorts cal.hosts room (cal.lastPage base))
  let airTime:=A.clocks (k*S.length) S.length+(4+10*cal.cohorts)+
    (clocks cal.cohorts (schedule hop S.length)+DescentTerminalCohortArena.ticks censusAt
      (k*S.length) cal.cohortBits cal.cohorts cal.hosts room (cal.lastPage base))
  have rented : FlightInvoice (2^J) ((S.copies*s)*(M+2^J*E)) (128000*factor) (boot.seq fly) airTime :=
    air M E w factor censusAt base (cal.scratch base) A rank hop (cal.lastPage base) room hosts support word
      ((Nat.le_succ _).trans arch)
  intro front back rest prior before
  have first_:=rented front back rest prior before
  have packet:=packet_home_insert M S.copies s (2^J) E j r h w factor (cal.packetStart base) cal.kept
    (cal.lastPage base) lower upper hLarge support power arch population packed (front.seq (boot.seq fly)) back
    (rest+airTime) (prior+128000*factor) first_
  have cost : cal.cost base censusAt room = airTime + (8+38*(E*2^(j+r))) := rfl
  have program : cal.program base censusAt room = (boot.seq fly).seq
      (DescentTerminalPacketHomeRAM.Expansion.fixedProgram w (cal.packetStart base) E j r cal.kept
        (cal.lastPage base)) := rfl
  rw [cost,program]
  simp only [names_seq] at packet ⊢
  convert packet using 1 <;> ring

end
end Hierarchy.DescentSixParty

end OAI
