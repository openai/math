import OAI.Hierarchy.DescentTerminalPrimitiveAny

namespace OAI
/-! # Public field retained by the original primitive row procedure -/
namespace Hierarchy.DescentTerminalPrimitiveArena.Shape
open DescentSIMDLookup DescentTerminalCombinedRole DescentTerminalPointerDigits ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable (s:Shape) (start pop:ℕ) (first second:Shelf)
    (chart:Fin s.columns→Fin s.blocks→Gather.Address) {out0 out7:ℕ}
    (f0:(Fin s.columns→Cell s.pointerBits)→Cell out0) (f7:(Fin s.columns→Cell s.pointerBits)→Cell out7)
    (q hidden nodes args groups p:ℕ) {w:ℕ}
local notation "off" => s.gather start
local notation "rows" => s.rows
local notation "pg" => Gather.dropOff off s.blocks s.shops s.columns chart
local notation "banks" => Gather.banks (L:=s.columns) off rows
local notation "pass" => DescentTerminalPointerFrame.size s.columns s.pointerBits
local notation "draw" => s.public start+rows
local notation "inputs" => s.sources start pop
local notation "issue_" => DescentTerminalPrimitiveNames.program w first second start off s.shops chart f0 f7 inputs
  s.countBits (s.counting start) (s.widths start) q hidden nodes args groups p
local notation "ticks_" => DescentTerminalPrimitiveNames.clocks s.pointerBits s.countBits off s.shops chart

/-- The reference scan and following distinct-word scans preserve the already printed public row. -/
theorem public_frame {occupied:Fin s.blocks→Bank} (m:Memory w) (kit:s.Realized (wb:=w) start pop occupied)
    (_legal:∀j b,(chart j b).Fits off s.shops w) (i:Fin rows) :
    let warm:=memory first second start rows m
    let gathered:=ProtocolRAM.result pg warm
    let pub:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 gathered
    s.primitiveImage start pop first second chart f0 f7 q hidden nodes args groups p m (s.public start+i.val)=
      DescentTerminalPointerFrame.result draw banks rows f7 pub (s.public start+i.val) := by
  let warm:=memory first second start rows m
  let gathered:=ProtocolRAM.result pg warm
  let published:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 gathered
  let refs:=DescentTerminalPointerFrame.result draw banks rows f7 published
  have done:=DescentTerminalCountWidthPair.run (q:=q) (hid:=hidden) (N:=nodes) (A:=args) (p:=p) (groups:=groups)
    inputs (s.counting start) (s.widths start) refs kit.source_room kit.count_later kit.width_limit
  have target:s.public start+i.val<draw:=Nat.add_lt_add_left i.isLt _
  have room_:draw≤ s.counting start:=by
    dsimp only [«public»,counting,pointers,widths]
    omega
  exact done.2.2 _ (.inl (target.trans_le room_))

/-- The private-word scans preserve every operand word written by the pointer pass. -/
theorem reference_frame {occupied:Fin s.blocks→Bank} (m:Memory w) (kit:s.Realized (wb:=w) start pop occupied)
    (i:Fin rows) :
    let warm:=memory first second start rows m
    let gathered:=ProtocolRAM.result pg warm
    let pub:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 gathered
    let refs:=DescentTerminalPointerFrame.result draw banks rows f7 pub
    s.primitiveImage start pop first second chart f0 f7 q hidden nodes args groups p m (s.pointers start+i.val)=
      refs (s.pointers start+i.val) := by
  let warm:=memory first second start rows m
  let gathered:=ProtocolRAM.result pg warm
  let published:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 gathered
  let refs:=DescentTerminalPointerFrame.result draw banks rows f7 published
  have done:=DescentTerminalCountWidthPair.run (q:=q) (hid:=hidden) (N:=nodes) (A:=args) (p:=p) (groups:=groups)
    inputs (s.counting start) (s.widths start) refs kit.source_room kit.count_later kit.width_limit
  apply done.2.2
  left
  unfold counting
  have hi:=i.isLt
  omega

/-- All inputs of the two pointer lookups remain readable from the final
primitive memory, including both freshly materialized scalar role columns. -/
theorem source_frame {occupied:Fin s.blocks→Bank} (m:Memory w) (kit:s.Realized (wb:=w) start pop occupied)
    (legal:∀j b,(chart j b).Fits off s.shops w) (a:ℕ) (lower:a<off) :
    s.primitiveImage start pop first second chart f0 f7 q hidden nodes args groups p m a=
      memory first second start rows m a := by
  let warm:=memory first second start rows m
  let gathered:=ProtocolRAM.result pg warm
  let published:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 gathered
  let refs:=DescentTerminalPointerFrame.result draw banks rows f7 published
  have room:=kit.pointer_limit
  have base₀:off+(s.columns*s.blocks)*s.shops≤ s.rom start:=by
    rw [Nat.mul_assoc]
    change off+s.columns*rows≤off+s.columns*rows+_
    omega
  have ends:s.rom start+pass+rows≤ s.pointers start+rows:=by
    change s.rom start+pass+rows≤ s.rom start+pass+rows+pass+rows
    omega
  have gRoom:off+(s.columns*s.blocks)*s.shops<2^w:=by omega
  have gf:=Gather.fetch_blocks chart warm off s.shops legal gRoom
  have ok:=Gather.banks_fit (L:=s.columns) off rows s.pointerBits kit.pointer_radix (by
    rw [s.gather_rom];omega)
  have ok7:DescentTerminalPointerFrame.Room banks draw s.pointerBits rows w:=
    ⟨fun j=>⟨(ok.source j).1,(ok.source j).2.1,(ok.source j).2.2.trans (by
       change s.rom start≤ s.rom start+pass+rows;omega)⟩,ok.length,kit.pointer_radix,room⟩
  have emit₀:=DescentTerminalPointerFrame.run (s.rom start) banks f0 gathered ok
  have emit₇:=DescentTerminalPointerFrame.run draw banks f7 published ok7
  have done:=DescentTerminalCountWidthPair.run (q:=q) (hid:=hidden) (N:=nodes) (A:=args) (p:=p) (groups:=groups)
    inputs (s.counting start) (s.widths start) refs kit.source_room kit.count_later kit.width_limit
  have gates:=kit.phase_order
  have ordering:off≤ s.rom start ∧ s.rom start≤draw ∧ draw≤ s.counting start:=by
    dsimp only [«public»,pointers,counting,rom]
    omega
  exact (done.2.2 a (.inl (lower.trans_le (ordering.1.trans (ordering.2.1.trans ordering.2.2))))).trans
    ((emit₇.2.2 a (.inl (lower.trans_le (ordering.1.trans ordering.2.1)))).trans
      ((emit₀.2.2 a (.inl (lower.trans_le ordering.1))).trans (gf.2.2.2.1 a (.inl lower))))

end
end Hierarchy.DescentTerminalPrimitiveArena.Shape

end OAI
