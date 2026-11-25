import OAI.Hierarchy.DescentTerminalPrimitiveSchedule

namespace OAI
/-! # The native primitive page issuer terminates at the same clock for every input -/
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

def primitiveImage (m:Memory w) :=
  let words:=ProtocolRAM.result pg (memory first second start rows m)
  let published:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 words
  let references:=DescentTerminalPointerFrame.result draw banks rows f7 published
  DescentTerminalCountWidthPair.final s.countBits q hidden nodes args groups s.blocks s.shops p
      (s.counting start) (s.widths start) inputs references

local notation "image_" => s.primitiveImage start pop first second chart f0 f7 q hidden nodes args groups p

/-- Malformed raw words still select a cell of the bounded ROM. All six phases
preserve the frames of the actual primitive allocation. -/
theorem primitive_frames {occupied:Fin s.blocks→Bank} (m:Memory w) (kit:s.Realized (wb:=w) start pop occupied)
    (one:(emit first).Fits w start) (two:(emit second).Fits w (start+rows))
    (legal:∀j b,(chart j b).Fits off s.shops w) :
    (issue_).Exec m (image_ m) ticks_ ∧ CheapCode issue_ ∧
      (∀a,a<start ∨ s.finish start≤a→image_ m a=m a) ∧
      ∀a,a<off→image_ m a=memory first second start rows m a := by
  let warm:=memory first second start rows m
  let gathered:=ProtocolRAM.result pg warm
  let published:=DescentTerminalPointerFrame.result (s.rom start) banks rows f0 gathered
  let refs:=DescentTerminalPointerFrame.result draw banks rows f7 published
  have roleLimit:=kit.role_first
  have phase₁:=DescentTerminalCombinedRole.run first m start rows one (by omega)
  have phase₂:=DescentTerminalCombinedRole.run second (ProtocolRAM.image start rows (emit first) m)
    (start+rows) rows two roleLimit
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
  have limits:=kit.phase_order
  have high:s.widths start+rows≤ s.finish start:=by unfold finish;omega
  have timeline:start+rows+rows≤off ∧ off≤ s.rom start ∧ s.rom start+pass+rows≤draw ∧
      draw+pass+rows≤ s.counting start ∧ s.counting start≤ s.widths start:=by
    exact ⟨Nat.le_add_right .., (Nat.le_add_right ..).trans (Nat.le_add_right ..), le_rfl,
      Nat.le_add_right .., ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · let run₁ := scan w start rows (emit first)
    let run₂ := scan w (start+rows) rows (emit second)
    let visits := ProtocolRAM.program w pg
    let out₀ := DescentTerminalPointerFrame.program w (s.rom start) banks rows f0
    let out₇ := DescentTerminalPointerFrame.program w draw banks rows f7
    let last := DescentTerminalCountWidthPair.program w s.countBits q hidden nodes args groups s.blocks s.shops p
      (s.counting start) (s.widths start) inputs
    let scanTime := (4+10*pass)+(4+rows*(16+26*s.columns))
    let pairTime := DescentTerminalCountWidthPair.clocks s.countBits s.blocks s.shops
    exact @Procedure.Exec.then w (run₁.seq run₂) (((visits.seq out₀).seq out₇).seq last) m warm (image_ m)
      (steps rows + steps rows) (clock pg + scanTime + scanTime + pairTime)
      (@Procedure.Exec.then w run₁ run₂ m (ProtocolRAM.image start rows (emit first) m) warm
        (steps rows) (steps rows) (@phase₁.1) (@phase₂.1))
      (@Procedure.Exec.then w ((visits.seq out₀).seq out₇) last warm refs (image_ m)
        (clock pg + scanTime + scanTime) pairTime
        (@Procedure.Exec.then w (visits.seq out₀) out₇ warm published refs
          (clock pg + scanTime) scanTime
          (@Procedure.Exec.then w visits out₀ warm gathered published (clock pg) scanTime (@gf.1) (@emit₀.1))
          (@emit₇.1)) (@done.1))
  · exact @DescentTerminalPrimitiveNames.cheap s.columns s.blocks s.pointerBits out0 out7 w first second start off s.shops chart f0 f7 inputs
      s.countBits (s.counting start) (s.widths start) q hidden nodes args groups p
  · intro a outside
    have roleLow:=ProtocolRAMGeneratedWrite.frame_image start rows (emit first) m a (by rcases outside with h|h <;> omega)
    have roleHigh:=ProtocolRAMGeneratedWrite.frame_image (start+rows) rows (emit second)
      (ProtocolRAM.image start rows (emit first) m) a (by rcases outside with h|h <;> omega)
    exact (done.2.2 a (outside.imp (fun h => by omega) (high.trans ·))).trans
      ((emit₇.2.2 a (by rcases outside with h|h <;> omega)).trans
        ((emit₀.2.2 a (by rcases outside with h|h <;> omega)).trans
          ((gf.2.2.2.1 a (by rcases outside with h|h <;> omega)).trans (roleHigh.trans roleLow))))
  · intro a below
    exact (done.2.2 a (.inl (by omega))).trans ((emit₇.2.2 a (.inl (by omega))).trans
      ((emit₀.2.2 a (.inl (by omega))).trans (gf.2.2.2.1 a (.inl below))))

theorem primitive_any {occupied:Fin s.blocks→Bank} (m:Memory w) (kit:s.Realized (wb:=w) start pop occupied)
    (one:(emit first).Fits w start) (two:(emit second).Fits w (start+rows))
    (legal:∀j b,(chart j b).Fits off s.shops w) :
    (issue_).Exec m (image_ m) ticks_ ∧ CheapCode issue_ ∧
      ∀a,a<start ∨ s.finish start≤a→image_ m a=m a := by
  have result:=s.primitive_frames start pop first second chart f0 f7 q hidden nodes args groups p m kit one two legal
  exact ⟨@result.1,@result.2.1,result.2.2.1⟩


end
end Hierarchy.DescentTerminalPrimitiveArena.Shape

end OAI
