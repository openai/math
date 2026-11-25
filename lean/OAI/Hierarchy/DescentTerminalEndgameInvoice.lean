import OAI.Hierarchy.DescentTerminalPlacedBudget
import OAI.Hierarchy.DescentTerminalBoot

namespace OAI
/-! # The terminal charge on the same dyadic container as the realized native program -/
namespace Hierarchy.DescentTerminalEmitter.Compact
open scoped BigOperators
theorem capacity {h:ℕ} (c:Columns) (fits:∀f,need (c f)≤2^(h/2)) :
    wordsBought c≤43*2^(h/2) := by
  unfold wordsBought
  calc
    _ ≤ ∑_:Fin 43,2^(h/2) := Finset.sum_le_sum fun i _=>by
      have bound:=fits i
      cases eqn:c i with
      | attained b => simp [size]
      | literal n =>
        rw [eqn] at bound
        exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow bound)
    _ = _ := by simp
/-- Some static ordinal columns (identity or half of an event address) span the
whole paid container; all value-dependent local lookups use the shared short ROM. -/
theorem capacity_with_rows {h n:ℕ} (c:Columns) (fits:∀f,need (c f)≤2^(h/2)+4*n) :
    wordsBought c≤86*2^(h/2)+344*n+43 := by
  have sum: (∑j,need (c j))≤43*(2^(h/2)+4*n) := calc
    _ ≤ ∑_:Fin 43,(2^(h/2)+4*n) := Finset.sum_le_sum (fun i _=>fits i)
    _ = _ := by simp
  have charge:=invoice c
  omega
end Hierarchy.DescentTerminalEmitter.Compact

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn DescentTerminalVertexFields DescentCompiler.TerminalScale DescentSixParty
open DescentTerminalGraphVolume DescentTerminalDenseWindow DescentTerminalBinReaddress
noncomputable section
variable {blocks v B:ℕ} (V:Home.Format) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
variable (T M copies s E rate piece q W homes j r lanes h bw factor:ℕ) (positive:0<homes) (wPos:0<W)
local notation "p" => W*piece
local notation "d" => copies*s
local notation "total_" => integralFrontier T M d E rate
local notation "budget" => rowBudget p q W total_ (d*E) homes 3
local notation "n" => bought budget W
local notation "K" => binCount budget W
local notation "S" => dimensions homes positive budget W total_ (q*p) E j r lanes
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "ba" => afterMeter V S R start
local notation "cpu" => clock V S I R start header short literal (bw:=bw)
local notation "ticks" => time V S I R start header
local notation "cap_" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "sz" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
 (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "cells" => MaskAllocation.marks sz+cap_
local notation "masked" => privateMaskedClock cells cap_ homes blocks V.piece+7*privateMaskedNames cells cap_ blocks V.piece
local notation "fund" => d*(M+T*E)
local notation "ρ" => 2*(6*(32*factor)*(3+4*rate)+2*factor)

include wPos

/-- Charges each static instruction of both the suffix and the final five checks,
all seven interpreter ROM columns, and both original chip and width ROM directories. -/
theorem endgame_price (codes:ℕ) (src:DescentTerminalChipRuntime.Banks)
    (spanFit:W≤2^(h/2)) (large:10≤h) (support:2^h≤2*(M*copies)) (width:T≤ s)
    (arch:bw≤factor*h) (packed:h≤32*(q*p))
    (outside:copies=2^(j+(j+r))) (pack0:h≤32*((2^j)*s))
    (positions:(4+(homes+1)*(26+234*blocks))*h*T≤M*d)
    (privateBill:masked*bw*T≤22491*factor*(M*d))
    (idx:I.indexEvents≤2*n) (fmt:I.formatEvents≤2*n)
    (tables:∀f,DescentTerminalEmitter.Compact.need (I.sources f)≤2^(h/2)+4*n)
    (dense:formatBits q p+2*(q*p)≤h/2) (route:DescentTerminalBinFormat.controlBits W q+sliceWidth W q piece≤h/2)
    (alphabet:codes+1≤2^(h/2)) :
    (ticks+DescentTerminalChipRuntime.clocks n n+
       7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw n n))+
       DescentTerminalBoot.total K W q piece codes)*bw*T≤
      (22491*factor+115*(130*factor+344*ρ)+24*factor+131072*(factor+32*factor+ρ)+8*ρ+36*factor)*fund := by
  have enum:=genuine_caps («p»:=p) (q:=q) (total:=total_) (exterior:=d*E) positive wPos E j r lanes I ba O idx fmt
  have physical:=paid_program V S I R start header short literal n enum src (bw:=bw)
  have bounded:bw≤(32*factor)*(q*p):=calc
    _ ≤ factor*h := arch
    _ ≤ factor*(32*(q*p)) := Nat.mul_le_mul_left _ packed
    _ = _ := by ring
  have rows:=covered_bank T M copies s E rate p q W homes h bw (32*factor) factor blocks
    spanFit large support width bounded arch positions
  have budgetSize:W≤budget:=by unfold rowBudget;omega
  have bound: n*bw*T≤ρ*fund:=calc
    _ ≤ (2*budget)*bw*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (cap_both wPos budgetSize).2)
    _ = 2*(budget*bw*T) := by ring
    _ ≤ 2*((6*(32*factor)*(3+4*rate)+2*factor)*fund) := Nat.mul_le_mul_left _ rows
    _ = _ := by ring
  have table:2^(h/2)*h*T≤M*d:=calc
    _ ≤ (M*copies)*T := Nat.mul_le_mul_right _ (table_fund large support)
    _ ≤ (M*copies)*s := Nat.mul_le_mul_left _ width
    _ = _ := by ring
  have mount:=DescentTerminalEmitter.Compact.capacity_with_rows I.sources tables
  have total:=joined_terminal_bill arch outside pack0 (sockets:=(S).packets) rfl privateBill positions bound table
    mount physical
  have atBoot:=DescentTerminalChipBootWords.room K W q piece codes h dense route alphabet
  have chipOnly: (ticks+DescentTerminalChipRuntime.clocks n n+
       7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw n n))+
       DescentTerminalChipBootWords.total K W q piece codes)*bw*T≤
      (22491*factor+115*(130*factor+344*ρ)+24*factor+131072*(factor+32*factor+ρ)+8*ρ+32*factor)*fund :=
    (Nat.mul_le_mul_right T (Nat.mul_le_mul_right bw (Nat.add_le_add_left atBoot _))).trans total
  have extra:=DescentTerminalDenseHeaderBoot.extent_le (q:=q) («p»:=p) dense
  have overall:M*d≤fund:=by rw [Nat.mul_comm M d,Nat.mul_add];omega
  have extraPaid:DescentTerminalDenseHeaderBoot.extent q p*bw*T≤(4*factor)*fund:=calc
    _ ≤ (4*2^(h/2))*(factor*h)*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul extra arch)
    _ = (4*factor)*(2^(h/2)*h*T) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (table.trans overall)
  rw [DescentTerminalBoot.total,←Nat.add_assoc,Nat.add_mul,Nat.add_mul]
  exact (Nat.add_le_add chipOnly extraPaid).trans_eq (by ring)

theorem endgame_payload_price (codes candidateCells:ℕ) (src:DescentTerminalChipRuntime.Banks)
    (spanFit:W≤2^(h/2)) (large:10≤h) (support:2^h≤2*(M*copies)) (width:T≤ s)
    (arch:bw≤factor*h) (packed:h≤32*(q*p))
    (outside:copies=2^(j+(j+r))) (pack0:h≤32*((2^j)*s))
    (positions:(4+(homes+1)*(26+234*blocks))*h*T≤M*d)
    (privateBill:masked*bw*T≤22491*factor*(M*d))
    (idx:I.indexEvents≤2*n) (fmt:I.formatEvents≤2*n)
    (tables:∀f,DescentTerminalEmitter.Compact.need (I.sources f)≤2^(h/2)+4*n)
    (dense:formatBits q p+2*(q*p)≤h/2) (route:DescentTerminalBinFormat.controlBits W q+sliceWidth W q piece≤h/2)
    (alphabet:codes+1≤2^(h/2)) (candidate:candidateCells≤2*(S).terminal.plane.rawRows+1) :
    (ticks+DescentTerminalChipRuntime.clocks n n+
       7*(names cpu+names (DescentTerminalChipRuntime.program (chip S I ba) src bw n n))+
       DescentTerminalBoot.total K W q piece codes+candidateCells)*bw*T≤
      (22491*factor+115*(130*factor+344*ρ)+24*factor+131072*(factor+32*factor+ρ)+11*ρ+36*factor)*fund := by
  have original:=endgame_price V I R start header short literal T M copies s E rate piece q W homes j r lanes h bw factor
    positive wPos codes src spanFit large support width arch packed outside pack0 positions privateBill idx fmt tables dense route alphabet
  have bounded:bw≤(32*factor)*(q*p):=calc
    _ ≤ factor*h := arch
    _ ≤ factor*(32*(q*p)) := Nat.mul_le_mul_left _ packed
    _ = _ := by ring
  have rows:=covered_bank T M copies s E rate p q W homes h bw (32*factor) factor blocks
    spanFit large support width bounded arch positions
  have enough:W≤budget:=by unfold rowBudget;omega
  have hb:=cap_both wPos enough
  have num:total_≤3*(2*total_+d*E):=by omega
  have div:=Nat.div_le_div_right (c:=q*p) num
  have spare:total_/(q*p)+2≤n:=by
    apply le_trans _ hb.1
    unfold rowBudget
    omega
  have rowCount:candidateCells≤3*n:=by change candidateCells≤2*(total_/(q*p)+1)+1 at candidate;omega
  have addOn:candidateCells*bw*T≤3*ρ*fund:=calc
    _ ≤ (3*(2*budget))*bw*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (rowCount.trans (Nat.mul_le_mul_left 3 hb.2)))
    _ = 6*(budget*bw*T) := by ring
    _ ≤ 6*((6*(32*factor)*(3+4*rate)+2*factor)*fund) := Nat.mul_le_mul_left _ rows
    _ = _ := by ring
  rw [Nat.add_mul,Nat.add_mul]
  exact (Nat.add_le_add original addOn).trans_eq (by ring)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
