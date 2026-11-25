import OAI.Hierarchy.DescentMatcherRatePolynomials
import OAI.Hierarchy.DescentDateBillVolume
import OAI.Hierarchy.DescentPackedCensusIngressBill
import OAI.Hierarchy.DescentPackedLayoutFinish
import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentPackedPhaseFootprint

namespace OAI
/-! # Bit cost of the installed chooser, six births, selected layout and saved rotation -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentPackedColony DescentSIMDLookup DescentPackedPayloadBudget DescentSixParty ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

private theorem log_page (n : ℕ) : 2^(n.log2+1) ≤ 2*(n+1) := by
  by_cases zero : n=0
  · simp [zero]
  · have bound:=Nat.log2_self_le zero
    rw [pow_succ]
    omega

theorem header_words (A : Frame.Chart) {w : ℕ} (k b D quota H G h u origin gap cap : ℕ)
    (hk : 0 < k) (fee : Bool → Cell ((1+b+2*quota)*2^k) → Cell (b*2^k))
    (fixed : A.bits=Frame.pageBits H G k b (lanes h u)) (covered : Phase.recordWidth k b quota ≤ u) :
    let M:=lanes h u
    let c:=Phase.CensusTables.image (w:=w) origin ((1+b+2*quota)*2^k) (b*2^k) M H G fee
    let p:=Phase.Arena.image (w:=w) A hk D H G b (2*Phase.unit k b*M) gap cap
    c.length ≤ 2*words H G h u ∧ p.length ≤ 2*Phase.Arena.sharedTables k D*words H G h u := by
  let M:=lanes h u
  let n:=H*chunks G M
  let V:=words H G h u
  let page:=(2:ℕ)^(h/2)
  have mass : u*M ≤ h/2 := by simpa only [Nat.mul_comm u M] using lanes_fit h u
  have kernel : Phase.unit k b ≤ u := (le_max_left ..).trans covered
  have input : (1+b+2*quota)*2^k ≤ u := (le_max_right ..).trans covered
  have common : DescentPackedColony.unit k b ≤ Phase.unit k b := by
    unfold DescentPackedColony.unit
    apply max_le <;> dsimp [DescentPackedColony.width,Phase.unit] <;> omega
  have low : (1+b+2*quota)*2^k*M ≤ h/2 := (Nat.mul_le_mul_right _ input).trans mass
  have tab := Nat.pow_le_pow_right (by decide : 0 < 2) low
  have mask := log_page n
  have vform : V=1+page+H+n:=rfl
  have top : A.page ≤ 2*V := by
    rw [Frame.Chart.page,fixed]
    change 2^(max ((max H n).log2+1) (DescentPackedColony.unit k b*M)) ≤ 2*V
    rcases le_total ((max H n).log2+1) (DescentPackedColony.unit k b*M) with a|a
    · rw [max_eq_right a]
      have p:=(Nat.mul_le_mul_right M (common.trans kernel)).trans mass
      have t : 2^(DescentPackedColony.unit k b*M) ≤ page:=Nat.pow_le_pow_right (by decide) p
      omega
    · rw [max_eq_left a]
      have high := log_page (max H n)
      have area : max H n ≤ H+n := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
      apply high.trans (Nat.mul_le_mul_left 2 ?_)
      calc
        max H n+1 ≤ (H+n)+1 := Nat.add_le_add_right area 1
        _ ≤ (H+n)+1+page := Nat.le_add_right _ _
        _ = V := by rw [vform]; ac_rfl
  have short : (2*Phase.unit k b*M)/2 ≤ h/2 := by
    have enough:=(Nat.mul_le_mul_right M kernel).trans mass
    rw [Nat.mul_assoc,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact enough
  have phasePage : 2^((2*Phase.unit k b*M)/2) ≤ page:=Nat.pow_le_pow_right (by decide) short
  constructor
  · change (origin+2*(2^((1+b+2*quota)*2^k*M))+2^(n.log2+1))-origin ≤ 2*V
    change 2^((1+b+2*quota)*2^k*M) ≤ page at tab
    omega
  · let a:=(2^k-1)*(D+3+4*k)
    let l:=Phase.Menu.pages k+2^k*((2^k-1)*2^(k+1))
    have head:=Phase.Arena.header_words A H G k b D (2*Phase.unit k b*M)
    change _ ≤ a*A.page+l*(2^((2*Phase.unit k b*M)/2)) at head
    have pageFit : page ≤ 2*V := by omega
    apply head.trans
    rw [show Phase.Arena.sharedTables k D=a+l by simp only [Phase.Arena.sharedTables,a,l,Nat.add_assoc]]
    change a*A.page+l*(2^((2*Phase.unit k b*M)/2)) ≤ 2*(a+l)*V
    calc
      _ ≤ a*(2*V)+l*(2*V) := Nat.add_le_add (Nat.mul_le_mul_left _ top)
        (Nat.mul_le_mul_left _ (phasePage.trans pageFit))
      _ = _ := by ring

theorem extra_words (s : Shape) (H G h u k D K ci pi : ℕ)
    (cost : SixBirths.unit s ≤ u)
    (census : ci ≤ 2*words H G h u)
    (phase : pi ≤ 2*Phase.Arena.sharedTables k D*words H G h u) :
    let M:=lanes h u
    (8+10*(ci+pi))+LayoutSum.Finish.ticks s M ((K*H)*chunks G M)+((4+10*(2^k-1))+30)
      ≤ extraFactor k D K*words H G h u := by
  let V:=words H G h u
  let n:=H*chunks G (lanes h u)
  let page:=(2:ℕ)^(h/2)
  let M:=lanes h u
  have fit : u*M ≤ h/2 := by simpa only [Nat.mul_comm u M] using lanes_fit h u
  have endTime:=LayoutSum.Finish.tick_bound s M ((K*H)*chunks G M) u h cost fit
  have hi : V=1+page+H+n:=rfl
  have one : 1 ≤ V := by omega
  have paged : page ≤ V := by omega
  have streamed : n ≤ V := by omega
  have rot : 2^k-1 ≤ 2^k*V := by
    exact (Nat.sub_le (2^k) 1).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^k) one)
  have data := Nat.mul_le_mul_left K streamed
  have finishBound : LayoutSum.Finish.ticks s M ((K*H)*chunks G M) ≤ 88+40*page+134*(K*n) := by
    simpa only [n,M,page,Nat.mul_assoc] using endTime
  dsimp only
  unfold extraFactor
  change ci ≤ 2*V at census
  change pi ≤ 2*Phase.Arena.sharedTables k D*V at phase
  change _ ≤ (200+20*Phase.Arena.sharedTables k D+134*K+10*2^k)*V
  nlinarith only [census,phase,finishBound,rot,data,paged,one]

/-- Extends the actual preexisting ordinary-stage bit bill by both freshly printed
images and the complete suffix run, keeping the same single half-word dictionary term. -/
theorem total (s : Shape) (H G h u k D K ci pi work core w ratio : ℕ)
    (cost : SixBirths.unit s ≤ u) (pos : 0 < u) (wide : 2*u ≤ h) (cpu : w ≤ ratio*h)
    (census : ci ≤ 2*words H G h u) (phase : pi ≤ 2*Phase.Arena.sharedTables k D*words H G h u)
    (charged : core*w ≤ ratio*(work*volumeBits H G h u)) :
    let M:=lanes h u
    ((((8+10*(ci+pi))+core)+LayoutSum.Finish.ticks s M ((K*H)*chunks G M))+((4+10*(2^k-1))+30))*w ≤
      ratio*((work+2*extraFactor k D K)*volumeBits H G h u) := by
  let V:=volumeBits H G h u
  let tail:=(8+10*(ci+pi))+LayoutSum.Finish.ticks s (lanes h u) ((K*H)*chunks G (lanes h u))+
    ((4+10*(2^k-1))+30)
  have tailWords : tail ≤ extraFactor k D K*words H G h u := extra_words s H G h u k D K ci pi cost census phase
  have tailBits : tail*w ≤ ratio*((2*extraFactor k D K)*V) := by
    apply DescentPackedPayloadBudget.clock cpu
    calc
      tail*h ≤ extraFactor k D K*(words H G h u*h) := by rw [←Nat.mul_assoc];exact Nat.mul_le_mul_right h tailWords
      _ ≤ extraFactor k D K*(2*V) := Nat.mul_le_mul_left _ (words_bits H G h u pos wide)
      _ = _ := by ring
  calc
    _ = core*w+tail*w := by dsimp only [tail];ring
    _ ≤ _ := (Nat.add_le_add charged tailBits).trans_eq (by dsimp only [V];ring)



set_option quotPrecheck false
section Ordinary

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (C : Chooser.Layout)
  (b payload unit ratio profile seats romBase : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "rdx" => 2^k
local notation "cap2" => 2*A.cap
local notation "K" => 2^(k+1)
local notation "panelBits" => max (k+3) (Nat.clog 2 (A.degree+1))
local notation "s" => shape rdx A.degree cap2 profile
variable (P₀ : Ports A.degree) (act : Bank) (wire : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "vals" => C.winners A.degree k b H G M
local notation "base" => Prepare.ROM.sortBase romBase k A.degree A.cap (k+3) M H G
local notation "bits_" => Prepare.bits H G M
local notation "outB" => Prepare.rosterBank base H A.degree
local notation "nextBase" => Prepare.next k H G M A.degree A.cap base
local notation "prep" => Prepare.ROM.chart romBase A.degree (k+3) M bits_ act vals wire
local notation "sort_" => Prepare.ROM.roster romBase k A.degree A.cap (k+3) M H G (Prepare.ROM.headBits H A.degree) P₀.roster
local notation "ps" => Prepare.passes prep sort_ base H G M A.degree
local notation "wins_" => Prepare.gatedBank (k:=k) base H G M A.degree bits_
local notation "marks_" => Prepare.markedBank (k:=k) (cap:=A.cap) base H G M A.degree bits_
local notation "field" => Gather.expr wins_ marks_ {P₀ with roster:=outB} H
local notation "time₀" => C.ticks A.degree k b cap2 H G M w
local notation "time₁" => ((4+10*Prepare.staticWords k A.degree A.cap (k+3) M H G)+ProtocolRAM.clock ps)+
  Gather.ROM.ticks s panelBits rdx A.degree cap2 K H G M unit nextBase seats field

variable (origin : ℕ) (hubBank : Bank) (atom : Fin (2^k)→Expr)
local notation "liveRows" => H*chunks G M
local notation "col" => Census.order rdx A.cap
local notation "startSum" => Census.beginSum origin H G M
local notation "oldBits" => fun i=>(Census.width A.degree A.cap b ((col).symm i))
local notation "src" => fun i=>(Census.expr (Census.Broadcast.result hubBank origin H G M) atom
  (fun x j=>Expr.lookup (wire x j) .row) ((col).symm i))
local notation "outBits" => (1+b+2*cap2)*rdx
local notation "timeInit" => (4+10*(2*liveRows))+DescentPackedColumnSum.ticks startSum unit M H G oldBits src

local notation "CI" => Phase.CensusTables.image (w:=w) C.origin ((1+b+2*cap2)*rdx) (b*rdx) M H G
  (fun fl=>PackedCensus.lookup fl b cap2 k A.wire 256 (A.z*gadget.b) A.hist)
local notation "PI" => Phase.Arena.image (w:=w) C.chart A.fieldBits A.degree H G b
  (2*Phase.unit k b*M) (DescentHostDegree.gap A.degree)
  (2^DescentHostDegree.packExponent 20 A.degree*((A.wire*(A.z*gadget.b))*A.cap))

local notation "N" => (K*H)*chunks G M
local notation "tock" => LayoutSum.Finish.ticks s M N

/-- Exact clock expression returned by the physical ordinary program, including
the initial pair of literal images and the final one-word exterior matrix. -/
theorem rotation_tariff (bound : ℕ) (reads : ∀x,(atom x).work ≤ bound)
    (pos : 0 < unit) (wide : 2*unit ≤ payload) (physical : w ≤ ratio*payload)
    (gate : 2^k+(k+3) ≤ unit) (cable : DescentSignedCableCodec.width A.degree A.cap ≤ unit)
    (phase : Phase.recordWidth k b cap2 ≤ unit)
    (canonical : C.chart.bits=Frame.pageBits H G k b M) (birth : SixBirths.unit s ≤ unit) :
    ((((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁)))+tock)+((4+10*(2^k-1))+30))*w ≤
      ratio*((Census.multiplier k A.degree A.cap K (max 22 bound)+2*extraFactor k A.degree K)*
        volumeBits H G payload unit) := by
  have p:=header_words C.chart k b A.degree cap2 H G payload unit C.origin
    (DescentHostDegree.gap A.degree) (2^DescentHostDegree.packExponent 20 A.degree*((A.wire*(A.z*gadget.b))*A.cap))
    A.fieldBits (fun fl=>PackedCensus.lookup fl b cap2 k A.wire 256 (A.z*gadget.b) A.hist) canonical phase (w:=w)
  apply total s H G payload unit k A.degree K (CI).length (PI).length _ _ w ratio birth pos wide physical p.1 p.2
  exact Census.ordinary_total_tariff s k A.degree A.cap (k+3) panelBits K H G payload w ratio unit seats base nextBase
    b cap2 (max 22 bound) startSum C prep sort_ {P₀ with roster:=outB} wins_ marks_ oldBits src
    (fun i=>Census.source_work k A.cap H G M origin hubBank atom wire bound reads ((col).symm i))
    pos wide physical gate cable

end Ordinary

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
