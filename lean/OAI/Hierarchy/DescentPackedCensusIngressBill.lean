import OAI.Hierarchy.DescentMatcherRatePolynomials
import OAI.Hierarchy.DescentPackedCensusIngress
import OAI.Hierarchy.DescentPackedOrdinaryBill

namespace OAI
/-! # Bit price of the physical old-row census issued before the chooser -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentPackedColony DescentPackedPayloadBudget DescentPackedColumnSum DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem source_work (k cap H G M origin : ℕ) (hub : Bank) (atom : Fin (2^k)→Expr)
    (wires : Fin (2^k)→Fin (2*cap)→Bank) (price : ℕ) (bounded : ∀x,(atom x).work≤price) (i : Column (2^k) cap) :
    (expr (Broadcast.result hub origin H G M) atom (fun x j=>.lookup (wires x j) .row) i).work ≤ max 22 price := by
  rcases i with ⟨x,_|(_|j)⟩
  · exact (Broadcast.work ..).le.trans (le_max_left ..)
  · exact (bounded x).trans (le_max_right ..)
  · exact (show 7≤22 by decide).trans (le_max_left ..)

/-- Both initializers are shared at all sites and groups, with one census scan
over the packed rows. The bound counts the literal-write clock and runtime words. -/
theorem bit_price_of_page_bits (N H G payload unit W ratio price original base : ℕ) (b : Fin N→ℕ) (src : Fin N→Expr)
    (bounded : ∀i,(src i).work≤price) (positive : 0<unit) (wide : 2*unit≤payload)
    (cpu : W≤ratio*payload) (fund : 2^(payload/2)*payload≤original) :
    let M:=lanes payload unit
    let n:=H*chunks G M
    ((4+10*(2*n))+ticks base unit M H G b src)*W ≤
      ratio*(12*payload+10*N*original+(26+2*N*(price+6))*(H*payload+4*H*G*unit)) := by
  let M:=lanes payload unit
  let n:=H*chunks G M
  have fit : unit*M≤payload/2:=by simpa only [Nat.mul_comm unit] using lanes_fit payload unit
  have page : 2^(unit*M)*payload≤original :=
    (Nat.mul_le_mul_right payload (Nat.pow_le_pow_right (by decide) fit)).trans fund
  have vol : n*payload≤H*payload+4*H*G*unit := volume H G payload unit positive wide
  have work:=work_le base unit M b src price bounded
  apply DescentPackedPayloadBudget.clock cpu
  change (4+10*(2*n)+(4+10*(N*2^(unit*M))+(4+n*(2*(reads base unit M b src).work+4))))*payload≤_
  nlinarith only [Nat.mul_le_mul_left (10*N) page,Nat.mul_le_mul_left (26+2*N*(price+6)) vol,
    Nat.mul_le_mul_left (2*n*payload) work]

theorem bit_price (N H G payload unit W ratio price original base : ℕ) (b : Fin N→ℕ) (src : Fin N→Expr)
    (bounded : ∀i,(src i).work≤price) (positive : 0<unit) (wide : 2*unit≤payload)
    (cpu : W≤ratio*payload) (fund : 2^payload≤original) :
    let M:=lanes payload unit
    let n:=H*chunks G M
    ((4+10*(2*n))+ticks base unit M H G b src)*W ≤
      ratio*(12*payload+10*N*original+(26+2*N*(price+6))*(H*payload+4*H*G*unit)) :=
  bit_price_of_page_bits N H G payload unit W ratio price original base b src bounded positive wide cpu
    (Prepared.page_bits fund)

/-- Paid program size includes the two initializers even on an empty board. -/
theorem hardware (N w origin out u M width H G : ℕ) (b : Fin N→ℕ) (f : ∀i,Cell (b i)→ℕ)
    (src : Fin N→Expr) (price : ℕ) (bounded : ∀i,(src i).work≤price) :
    let base:=beginSum origin H G M
    let n:=H*chunks G M
    let before:=DescentStaticWordColumn.program w origin (Broadcast.literal H G M) (2*n)
    let emitted:=DescentPackedColumnSum.program w base out u M width H G b f src
    names (before.seq emitted) ≤
      15*(2*n+1)+15*(N*2^(u*M)+1)+15+4*N*(price+6) := by
  dsimp only [DescentPackedColumnSum.program]
  rw [names_seq,names_mount,names_seq,names_mount,names_scan]
  have bound:=work_le (beginSum origin H G M) u M b src price bounded
  rw [Nat.mul_assoc 4 N (price+6)]
  omega

/-- The three phases of the old-row program, including the physical cost of
every lookup page. The page term depends only on half the payload width. -/
theorem ordinary_total_tariff (s : Shape) (k D cap a d K H G payload W ratio unit seats base matcher b quota work origin : ℕ)
    (chooser : Chooser.Layout) (C : Prepare.Chart k cap) (Z : DescentSortedRoster.Chart) (P : Ports D)
    (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
    (bits : Fin (columns (2^k) cap)→ℕ) (source : Fin (columns (2^k) cap)→Expr)
    (price : ∀j,(source j).work≤work) (positive : 0<unit) (wide : 2*unit≤payload)
    (cpu : W≤ratio*payload) (gate : 2^k+a≤unit) (wire : DescentSignedCableCodec.width D cap≤unit) :
    let M:=lanes payload unit
    let _N:=columns (2^k) cap
    let n:=H*chunks G M
    let pageBits:=2^(payload/2)*payload
    let inputTicks:=(4+10*(2*n))+ticks origin unit M H G bits source
    let chooserTicks:=chooser.ticks D k b quota H G M W
    let matchTicks:=((4+10*Prepare.staticWords k D cap a M H G)+ProtocolRAM.clock (Prepare.passes C Z base H G M D))+
      Gather.ROM.ticks s d (2^k) D (2*cap) K H G M unit matcher seats (Gather.expr wins marked P H)
    (inputTicks+(chooserTicks+matchTicks))*W ≤
      ratio*(multiplier k D cap K work*(payload+H*payload+4*H*G*unit+pageBits)) := by
  let _N:=columns (2^k) cap
  let page:=2^(payload/2)*payload
  let scan:=H*payload+4*H*G*unit
  let volume:=payload+H*payload+4*H*G*unit+page
  have old:=bit_price_of_page_bits _N H G payload unit W ratio work page origin bits source price
    positive wide cpu le_rfl
  have rest:=ordinary_bill_of_page_bits s k D cap a d K H G payload W ratio unit seats base matcher page b quota
    chooser C Z P wins marked positive wide cpu le_rfl gate wire
  dsimp only at old rest ⊢
  rw [Nat.add_mul]
  apply (Nat.add_le_add old rest).trans
  rw [←Nat.mul_add]
  apply Nat.mul_le_mul_left
  change 12*payload+10*_N*page+(26+2*_N*(work+6))*scan+ordinaryFactor k D cap K*volume≤
    (12+10*_N+(26+2*_N*(work+6))+ordinaryFactor k D cap K)*volume
  have hp : payload≤volume := by dsimp only [volume];omega
  have hs : scan≤volume := by dsimp only [volume,scan];omega
  have ht : page≤volume := by dsimp only [volume];omega
  nlinarith only [Nat.mul_le_mul_left 12 hp,Nat.mul_le_mul_left (10*_N) ht,
    Nat.mul_le_mul_left (26+2*_N*(work+6)) hs]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
