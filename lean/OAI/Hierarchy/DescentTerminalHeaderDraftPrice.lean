import OAI.Hierarchy.DescentTerminalHeaderEventLiterals
import OAI.Hierarchy.DescentTerminalPriorNames
import OAI.Hierarchy.DescentTerminalPublicWidthTape

namespace OAI
/-! # Clock and static word invoice for the actual paid-header checkpoint and its predecessors -/
namespace Hierarchy.DescentTerminalHeaderDraft
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentSIMDLookup DescentTerminalRowArena DescentStaticWordColumn DescentColonies.SplitRAM
noncomputable section

variable {B aa:ℕ} (w H G M a b c lo M' next:ℕ) (old:Fin B→Bank) (external:Bank)
    (pick:Fin B→Cell aa→Cell 1) (source:Fin B→Bank)
    (X:DescentTerminalPublicWidthTape.Shape) (q p:ℕ) (A:Arena) (L:DescentTerminalHeaderSockets.Layout) (rom:ℕ)
local notation "prior1" => DescentTerminalPopulation.RAM.issue H G M a b c lo old external w
local notation "prior2" => DescentTerminalActorRepack.program pick H G M' next source w
local notation "paidROM" => DescentTerminalPopulation.RAM.lease H G M a c lo
local notation "actorROM" => DescentTerminalActorRepack.count H G M' aa B next
local notation "publicROM" => Bank.size (DescentTerminalPublicCountRAM.lut X.base X.maxCohorts)+X.widthLayout.entries
local notation "lanes" => chunks G M+chunks G M'
local notation "bits_" => X.program w q p
local notation "clocks₁" => DescentTerminalPopulation.RAM.ticks H G M a c lo old external
local notation "clocks₂" => DescentTerminalActorRepack.ticks (a:=aa) H G M' next source
local notation "core" => Procedure.seq
  (Procedure.seq (Procedure.seq (Procedure.seq prior1 prior2) bits_) (litProc w rom A.rows)) (machine A L 3 w)

theorem public_tariff :
    names bits_≤15*publicROM+449 ∧ X.clocks q p≤31+10*publicROM+176*X.H+26*X.rows := by
  rw [X.names,DescentTerminalWidthRowsRAM.Layout.names_exact]
  have timing:=X.widthLayout.clocks_exact q p
  have count:=DescentTerminalPublicCountRAM.ticks X.base X.maxCohorts X.H X.old
  change X.widthLayout.clocks q p=23+10*X.widthLayout.entries+148*X.H+X.rows*(if X.H=0 then 16 else 26) at timing
  unfold DescentTerminalPublicWidthTape.Shape.clocks
  rw [count,timing]
  change 15*(_+1)+59+(15*(_+1)+(if X.H=0 then 340 else 360))≤_ ∧ _
  split <;> constructor <;> omega

/-- The linked architecture charges each mounted table, actual host scan, and each paid
row once. The separate frozen-cohort sort, when already in the startup, need not be repeated. -/
theorem stated_price :
    names core+clocks₁+clocks₂+X.clocks q p+(4+40*span A.rows)+clocks A L 3≤
    300000*(1+paidROM+actorROM+publicROM+B*(1+lanes)+H*B*(1+lanes)+X.H+X.rows+A.sites+A.rows) := by
  have pr:=DescentTerminalPriorNames.pair w H G M a b c lo M' next old external pick source
  have pu:=public_tariff w X q p
  have dr:=price A L 3 w
  rw [effort_three] at dr
  have lit:=DescentStaticWordColumn.names_mount w rom (literal A.rows) (4*span A.rows)
  have sp:=span_price A.rows
  rw [names_seq,names_seq,names_seq,pr.1]
  simp only [litProc,lit]
  have pt:=pr.2
  nlinarith only [pt,pu.1,pu.2,dr.1,dr.2,sp,
    Nat.zero_le paidROM,Nat.zero_le actorROM,Nat.zero_le (DescentTerminalPublicCountRAM.lut X.base X.maxCohorts).size,
    Nat.zero_le X.widthLayout.entries,Nat.zero_le (B*lanes),Nat.zero_le (H*B*lanes),
    Nat.zero_le B,Nat.zero_le (B*H),Nat.zero_le X.H,Nat.zero_le A.sites,Nat.zero_le A.rows,Nat.zero_le X.rows]

private theorem rounded (n:ℕ) : 2^Nat.clog 2 n≤2*n+1 := by
  cases e:Nat.clog 2 n with
  | zero=>simp
  | succ k=>
    have small:=Nat.pow_lt_of_lt_clog (show k<Nat.clog 2 n by omega)
    simp only [pow_succ];omega

/-- At the chosen packed predecessor pitch the number of incoming pages is
independent of the number of old group lanes. -/
theorem packed_lanes {G M M' B scale:ℕ} (pos:0<M) (pos':0<M') (old:G≤M) (new_:G≤M') (scale_:3*B≤ scale) :
    B*(1+(chunks G M+chunks G M'))≤ scale := by
  have one (m:ℕ) (hm:0< m) (fit:G≤ m) : chunks G m≤1 := by
    change (G+m-1)/m≤1
    have h: (G+m-1)/m<2:=(Nat.div_lt_iff_lt_mul hm).2 (by omega)
    omega
  exact (Nat.mul_le_mul_left B (show 1+(chunks G M+chunks G M')≤3 by
    have a:=one M pos old;have b:=one M' pos' new_;omega)).trans (by simpa [Nat.mul_comm] using scale_)

/-- Explicit menu-room test, split into instruction-independent bit widths.
The two H-entry predecessor index arrays are charged to H. -/
theorem menu_price (h scale:ℕ) (one:0<scale) (rate:B*chunks G M'≤2^(h/4))
    (cells:chunks G M≤2^(h/4)) (pBits:a*M≤h/4) (aBits:aa*M'≤h/4) (cBits:c≤h/2)
    (pc:X.maxCohorts+1≤2^(h/2)) (out:X.maxCohorts*X.rate+1≤2^(h/2)) :
    paidROM+actorROM+publicROM≤12*(2^(h/2)+H*scale) := by
  have pow_ (j k:ℕ) (le:j≤k) : 2^j≤2^k:=Nat.pow_le_pow_right (by decide) le
  have square: 2^(h/4)*2^(h/4)≤2^(h/2):=by rw [←pow_add];exact pow_ _ _ (by omega)
  have payload:= (Nat.mul_le_mul cells (pow_ _ _ pBits)).trans square
  have actors:=(Nat.mul_le_mul rate (pow_ _ _ aBits)).trans square
  have shape_:=pow_ _ _ cBits
  have host:=rounded H
  have cap:=pow_ _ _ (Nat.clog_le_of_le_pow pc)
  have last_:=pow_ _ _ (Nat.clog_le_of_le_pow out)
  have hle:=Nat.le_mul_of_pos_right H one
  have nonzero:=Nat.two_pow_pos (h/2)
  change (2^Nat.clog 2 H+2^c+chunks G M*2^(a*M))+
    (2^Nat.clog 2 H+B*chunks G M'*2^(aa*M'))+
    (2^Nat.clog 2 (X.maxCohorts+1)+2*2^Nat.clog 2 (X.maxCohorts*X.rate+1))≤_
  omega

/-- Conversion to the terminal program's fixed alphabet price. Uniform bounds on the
actual menu extents and the lane packing are the only parameter facts this step uses. -/
theorem calibrated_price (h bw scale paid:ℕ)
    (menus:paidROM+actorROM+publicROM≤12*(2^(h/2)+H*scale))
    (packing:B*(1+lanes)≤ scale) (sites:A.sites≤H) (publicH:X.H≤H)
    (charged:X.rows+A.rows≤paid) (nonempty:0<H) (rate:0<scale) :
    (names core+clocks₁+clocks₂+X.clocks q p+(4+40*span A.rows)+clocks A L 3)*(bw+1)≤
      6000000*((2^(h/2)+H*scale)*(bw+1)+paid*(bw+1)) := by
  have raw:=stated_price w H G M a b c lo M' next old external pick source X q p A L rom
  have host_:=Nat.mul_le_mul_left H packing
  have build:scale≤H*scale:=Nat.le_mul_of_pos_left _ nonempty
  have hle:H≤H*scale:=Nat.le_mul_of_pos_right _ rate
  have pos:=Nat.two_pow_pos (h/2)
  have plain:1+paidROM+actorROM+publicROM+B*(1+lanes)+H*B*(1+lanes)+X.H+X.rows+A.sites+A.rows≤
      20*(2^(h/2)+H*scale+paid) := by rw [Nat.mul_assoc H B] ;omega
  calc
    _ ≤ (300000*(20*(2^(h/2)+H*scale+paid)))*(bw+1) :=
      Nat.mul_le_mul_right _ (raw.trans (Nat.mul_le_mul_left _ plain))
    _ = _ := by ring

end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
