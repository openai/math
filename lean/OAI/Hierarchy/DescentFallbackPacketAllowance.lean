import OAI.Hierarchy.DescentFallbackPeriodInputs
import OAI.Hierarchy.DescentPackedFallbackAllowance

namespace OAI
/-! # Width of the actual fallback source packet and of its five private output fields -/
noncomputable section
namespace Hierarchy
open scoped Classical

namespace DescentFallbackPeriod
open DescentFallbackShapeTable DescentPackedPrivateMenu

def packetField (D cap n r Ht : ℕ) :=
  max (Ht+2) (max (DescentSignedCableCodec.width D cap) (2+Nat.clog 2 (rows r (2^n))))

/-- This coefficient only uses the fixed board, arity, template height and
width choices of the reset. The current group multiplicity does not enter it. -/
def fixedFloor (D n h Ht C b slots : ℕ) :=
  16+(D+1)+(2^n+1)+(Ht+2)+
    2*((2^n+1)+((2*h+4)*2^n+(2^n+1)*2^(Ht+1)))+
    max (C*b) ((2+2*h*C)*b)+5*slots

private theorem clog_le (x : ℕ) : Nat.clog 2 x≤x :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le : x≤2^x)

/-- Both genuine packed widths, with the exact no-rotor fallback lookup. -/
theorem packet_widths {n h : ℕ} (board : NonlinearExpanders.Graph n h)
    (D cap r Ht C b slots U : ℕ) (params : fixedFloor D n h Ht C b slots≤U)
    (window : 2^r≤U) (capacity : cap≤U) (used : 2^r*(2*cap)≤U) :
    max (packetField D cap n r Ht*inputCount D (2^r) cap n r)
      (fieldBits board r Ht (2^r*(2*cap)) 0 C b*(slots*5)) ≤ U^12 := by
  have components {a b c d e f g : ℕ} (h : a+b+c+d+e+f+g ≤ U) :
      a ≤ U ∧ b ≤ U ∧ c ≤ U ∧ d ≤ U ∧ e ≤ U ∧ f ≤ U ∧ g ≤ U := by omega
  unfold fixedFloor at params
  obtain ⟨big,deg,Y,ht,floor,price,slotsBound⟩ := components params
  have pos : 0<U:=by omega
  have up {a b : ℕ} (ab : a≤b) : U^a≤U^b:=Nat.pow_le_pow_right pos ab
  have one : U≤U^7:=by simpa only [pow_one] using up (by decide : 1≤7)
  have rr : r+1≤U:=(Nat.lt_two_pow_self : r<2^r).trans_le window
  have rowsPaid : rows r (2^n)≤U^3 := by
    unfold rows
    calc
      _ ≤ (U*U)*U := Nat.mul_le_mul (Nat.mul_le_mul rr window) Y
      _ = _ := by ring
  have book : DescentSharedBookScan.width r (2^n) D≤U^7 := by
    unfold DescentSharedBookScan.width
    calc
      _ ≤ U^3*(U*U^3) := Nat.mul_le_mul rowsPaid (Nat.mul_le_mul deg rowsPaid)
      _ = _ := by ring
  have readers : inputCount D (2^r) cap n r≤U^8 := by
    have neighbors : D*2^r≤U^7 :=
      (Nat.mul_le_mul (by omega : D≤U) window).trans (by simpa only [pow_two] using up (by decide : 2≤7))
    have left:=window.trans one
    have right:=used.trans one
    have charged:=Nat.mul_le_mul_right (U^7) (show 4≤U by omega)
    calc
      _ ≤ 4*U^7 := by unfold inputCount;omega
      _ ≤ U*U^7 := charged
      _ = U^8 := by ring
  have two : U≤U^2:=by simpa only [pow_one] using up (by decide : 1≤2)
  have maxField : packetField D cap n r Ht≤U^4 := by
    unfold packetField
    apply max_le ((ht.trans two).trans (up (by decide : 2≤4)))
    apply max_le
    · have dc:=(clog_le (D+1)).trans deg
      have cc:=clog_le (cap+1)
      have pay:=Nat.mul_le_mul_right U (show 8≤U by omega)
      unfold DescentSignedCableCodec.width DescentSharedCableNames.Packed.bits
      have bound : U*U≤U^4:=by simpa only [pow_two] using up (by decide : 2≤4)
      omega
    · have tag:=(clog_le _).trans rowsPaid
      have p:=(Nat.pow_pos pos : 0<U^3)
      have extra:=Nat.mul_le_mul_right (U^3) (show 3≤U by omega)
      rw [pow_succ, Nat.mul_comm (U^3)]
      omega
  have roster : (DescentDenseHostOrder.roster board r Ht).card≤U^3 := by
    have pay:=DescentDenseHostOrder.roster_bound board r Ht
    rw [pow_succ] at pay
    calc
      _ ≤ _ := pay
      _ ≤ U*(U*U) := Nat.mul_le_mul floor (Nat.mul_le_mul window (by omega))
      _ = _ := by ring
  have lim : DescentPackedPrivateMenu.fieldBound board r Ht (2^r*(2*cap)) 0 C b≤U^3 := by
    have u3 : U≤U^3:=by simpa only [pow_one] using up (by decide : 1≤3)
    simp only [DescentPackedPrivateMenu.fieldBound,DescentPackedRotorPanel.ceiling,pow_zero,Nat.one_mul]
    exact max_le (used.trans u3) (max_le (by omega) (max_le roster (price.trans u3)))
  have field : fieldBits board r Ht (2^r*(2*cap)) 0 C b≤U^4 := by
    unfold fieldBits ProtocolRAMPurchaseSampler.bits
    have bits:=Nat.log_le_self 2 (DescentPackedPrivateMenu.fieldBound board r Ht (2^r*(2*cap)) 0 C b+1)
    have positive:=(Nat.pow_pos pos : 0<U^3)
    have extra:=Nat.mul_le_mul_right (U^3) (show 3≤U by omega)
    rw [pow_succ,Nat.mul_comm (U^3)]
    omega
  have slotsPaid : slots*5≤U := Nat.mul_comm slots 5 ▸ slotsBound
  apply max_le
  · calc
      _ ≤ U^4*U^8:=Nat.mul_le_mul maxField readers
      _ = _ := by ring
  · calc
      _ ≤ U^4*U:=Nat.mul_le_mul field slotsPaid
      _ = U^5:=by ring
      _ ≤ _:=up (by decide)
end DescentFallbackPeriod

namespace DescentFallbackPeriod
def boardFloor {n h : ℕ} (board : NonlinearExpanders.Graph n h) (D Ht C b : ℕ) :=
  fixedFloor D n h Ht C b (DescentResetCableSlots.cableCap board Ht)

theorem boardFloor_eq {n n' h : ℕ} (X : NonlinearExpanders.Graph n h) (Y : NonlinearExpanders.Graph n' h)
    (d : n=n') (same : HEq X Y) (D Ht C b : ℕ) :
    boardFloor X D Ht C b=boardFloor Y D Ht C b := by
  subst n'
  rw [eq_of_heq same]
end DescentFallbackPeriod

namespace DescentSixParty.ClosedReset
open DescentCompiler DescentFallbackPeriod DescentPackedPrivateMenu
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (Z : ClosedReset input ctl)
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => Z.reset.k-Z.terminals.commonDepth
local notation "cap" => input.placement.cap

/-- Fixed before any physical age. -/
def packetExponent (ctl : ResetRates G S k D n h C f g cut tail) :=
  max (S.fallbackExponent cut) (Nat.clog 2 (boardFloor ctl.board D Ht C ctl.bitsR))

/-- Exactly the input/output width used by the authentic installed fallback
menu, with zero layer bits on its inactive rotor alternative. -/
def packetWidth :=
  let a:=packetField input.placement.degree cap Z.reset.n r Ht
  let count:=inputCount input.placement.degree (2^r) cap Z.reset.n r
  let output:=fieldBits Z.reset.graph r Ht (2^r*(2*cap)) 0 C Z.reset.width
  max (a*count) (output*((DescentResetCableSlots.cableCap Z.reset.graph Ht)*5))

theorem packetWidth_paid (age : i≤S.length) :
    Z.packetWidth≤S.epochPower^(packetExponent ctl*12) := by
  let e:=packetExponent ctl
  let U:=S.epochPower^e
  have big : 2≤S.epochPower:=Nat.one_lt_two_pow ctl.height.ne'
  have fixed : boardFloor ctl.board D Ht C ctl.bitsR≤U := calc
    _ ≤ 2^Nat.clog 2 (boardFloor ctl.board D Ht C ctl.bitsR) := Nat.le_pow_clog (by decide) _
    _ ≤ S.epochPower^Nat.clog 2 (boardFloor ctl.board D Ht C ctl.bitsR) := Nat.pow_le_pow_left big _
    _ ≤ U := Nat.pow_le_pow_right (by omega) (le_max_right ..)
  have same : boardFloor Z.reset.graph input.placement.degree Ht C Z.reset.width≤U := by
    rw [input.branch,Z.width,boardFloor_eq Z.reset.graph ctl.board Z.dimension Z.graph]
    exact fixed
  have grow : S.epochPower^(S.fallbackExponent cut)≤U :=
    Nat.pow_le_pow_right (by omega) (le_max_left ..)
  have key : r=k:=by rw [Z.keyWidth,Z.commonDepth,Nat.add_sub_cancel_left]
  have used : 2^r*(2*cap)≤U:=(Z.fallbackSlots_paid age).trans grow
  have cells : cap≤U:=calc
    _ ≤ 2*cap := by omega
    _ ≤ 2^r*(2*cap) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    _ ≤ _ := used
  have source : 2^r≤U := by
    rw [key]
    have empty:=S.fallback_slots («cap»:=1) ctl.height age (Nat.two_pow_pos _) ctl.fixed
    exact (by omega : 2^k≤2^k*(2*1)).trans (empty.trans grow)
  have bounded:=packet_widths Z.reset.graph input.placement.degree cap r Ht C Z.reset.width
    (DescentResetCableSlots.cableCap Z.reset.graph Ht) U same source cells used
  exact bounded.trans_eq (pow_mul S.epochPower e 12).symm

theorem packetWidth_at_height (age : i≤S.length) (B physical : ℕ)
    (budget : packetExponent ctl*12≤B) (height : S.height=Nat.log 2 physical/(2*B))
    (large : 2^(2*B+10)≤physical) : 2*Z.packetWidth≤physical := by
  have nz : physical≠0:=((Nat.two_pow_pos _).trans_le large).ne'
  have enough : 2*B+10≤Nat.log 2 physical:=(Nat.le_log_iff_pow_le (by decide) nz).mpr large
  have used : S.height*(2*B)≤Nat.log 2 physical:=by rw [height];exact Nat.div_mul_le_self _ _
  have price : 1+S.height*B≤Nat.log 2 physical:=by nlinarith only [used,enough,Nat.zero_le B]
  have fit : 2*S.epochPower^B≤physical:=by
    change 2^1*(2^S.height)^B≤physical
    rw [←pow_mul,←pow_add]
    exact (Nat.le_log_iff_pow_le (by decide) nz).mp price
  exact (Nat.mul_le_mul_left 2 ((Z.packetWidth_paid age).trans
    (Nat.pow_le_pow_right (Nat.two_pow_pos _) budget))).trans fit

end DescentSixParty.ClosedReset
end Hierarchy
end

end OAI
