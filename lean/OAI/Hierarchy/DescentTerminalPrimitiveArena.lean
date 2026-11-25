import OAI.Hierarchy.DescentTerminalPrimitiveSpace
import OAI.Hierarchy.DescentTerminalPointerGather
import OAI.Hierarchy.DescentTerminalMaskAllocation
import OAI.Hierarchy.DescentTerminalPrivateSourceChannels

namespace OAI
/-! # Concrete primitive-family RAM layout following the last chronological frame -/
namespace Hierarchy.DescentTerminalPrimitiveArena.Shape
open ProtocolRAM DescentTerminalVertexFields DescentTerminalPointerFrame
open DescentTerminalPointerDigits DescentTerminalPrivateSourceChannels
open ThreeFlat.RAM
open scoped Classical
noncomputable section
variable (s:Shape) (start pop:ℕ) (occupied:Fin s.blocks→Bank)

def subrow (base:ℕ) (b:Fin s.blocks) : Bank := ⟨base+b.val*s.shops,Nat.clog 2 s.shops⟩
def wholeRow (base:ℕ) : Bank := ⟨base,Nat.clog 2 s.rows⟩

def channels : MaskAllocation.Channels s.blocks where
  occupied := occupied
  primitive b := ![s.subrow (s.public start) b,occupied b,s.subrow (s.number start) b,s.subrow pop b,
    s.subrow (s.widths start) b,s.subrow start b,s.subrow (start+s.rows) b,s.subrow (s.pointers start) b]

def sources : Fin 3→Bank :=
  ![s.wholeRow pop,s.wholeRow (start+s.rows),s.wholeRow (s.pointers start)]

theorem gather_rom : Gather.rom (s.gather start) s.columns s.rows=s.rom start := rfl
theorem alias_ (b:Fin s.blocks):((s.channels start pop occupied).primitive b 1)=occupied b:=rfl

theorem bounds (b:Fin s.blocks) : b.val*s.shops+s.shops≤ s.rows :=
  by simpa [rows,Nat.succ_mul] using Nat.mul_le_mul_right s.shops (Nat.succ_le_of_lt b.isLt)

theorem capacity (b:Fin s.blocks) (f:Fin 8) (actor:s.shops≤(occupied b).size) :
    s.shops≤((s.channels start pop occupied).primitive b f).size := by
  fin_cases f <;> first | exact actor | exact covered _

theorem source_base (b:Fin s.blocks) (f:Fin 3) :
    ((s.channels start pop occupied).primitive b (family f)).base=(s.sources start pop f).base+b.val*s.shops := by
  fin_cases f <;> rfl

/-- The earlier f3 frame contains its rounded old population column and the active
per-block reads. Selection changes its bits; it never changes this bound. -/
structure Prior : Prop where
  oldPopulation : pop+s.rows+s.guard≤ start
  actorEnd : ∀b,(occupied b).base+(occupied b).size≤ start
  actorSize : ∀b,s.shops≤(occupied b).size

variable (prior:s.Prior start pop occupied)
include prior in
theorem old_frame (b:Fin s.blocks) (f:Fin 8) (field:f=1 ∨ f=3 ∨ f=5 ∨ f=6) :
    let B:=(s.channels start pop occupied).primitive b f
    B.base+B.size≤ s.gather start := by
  have pos:=s.bounds b
  have p:=prior.oldPopulation
  obtain rfl|rfl|rfl|rfl:=field
  · exact (prior.actorEnd b).trans (by unfold gather;omega)
  all_goals change _+b.val*s.shops+pad s.shops≤ s.gather start
  all_goals unfold gather guard at *;omega

include prior in
theorem count_frame (b:Fin s.blocks) (f:Fin 8) (notTwo:f≠2) (notFour:f≠4) :
    let B:=(s.channels start pop occupied).primitive b f
    B.base+B.size≤ s.counting start := by
  have pos:=s.bounds b
  have popEnd:=prior.oldPopulation
  have begin:s.gather start≤ s.counting start := by unfold counting pointers «public» rom;omega
  fin_cases f
  · change s.public start+b.val*s.shops+pad s.shops≤ s.counting start
    unfold counting pointers guard;omega
  · exact (s.old_frame start pop occupied prior b 1 (.inl rfl)).trans begin
  · exact (notTwo rfl).elim
  · exact (s.old_frame start pop occupied prior b 3 (.inr (.inl rfl))).trans begin
  · exact (notFour rfl).elim
  · exact (s.old_frame start pop occupied prior b 5 (.inr (.inr (.inl rfl)))).trans begin
  · exact (s.old_frame start pop occupied prior b 6 (.inr (.inr (.inr rfl)))).trans begin
  · change s.pointers start+b.val*s.shops+pad s.shops≤ s.counting start
    unfold counting guard;omega

include prior in
theorem live_end (b:Fin s.blocks) (f:Fin 8) :
    let B:=(s.channels start pop occupied).primitive b f
    B.base+B.size≤ s.finish start := by
  have pos:=s.bounds b
  by_cases two:f=2
  · subst f
    change s.number start+b.val*s.shops+pad s.shops≤ s.finish start
    unfold finish widths guard;omega
  by_cases four:f=4
  · subst f
    change s.widths start+b.val*s.shops+pad s.shops≤ s.finish start
    unfold finish guard;omega
  · exact (s.count_frame start pop occupied prior b f two four).trans (by unfold finish widths number;omega)

variable {wb:ℕ} (limit:s.finish start<2^wb)
include prior limit in
theorem count_room : Room (s.sources start pop) (s.counting start) s.countBits s.rows wb := by
  have first:=prior.oldPopulation
  have ea:s.counting start≤ s.finish start:=by unfold finish widths number;omega
  have bound (j:Fin 3):(s.sources start pop j).base+(s.sources start pop j).size≤ s.counting start := by
    fin_cases j
    · change pop+pad s.rows≤ s.counting start
      unfold counting pointers «public» rom gather guard at *;omega
    · change start+s.rows+pad s.rows≤ s.counting start
      unfold counting pointers «public» rom gather guard;omega
    · change s.pointers start+pad s.rows≤ s.counting start
      unfold counting guard;omega
  constructor
  · intro j
    have end_:=bound j
    exact ⟨Nat.two_pow_pos _,by omega,end_⟩
  · intro j;fin_cases j <;> exact covered _
  · have off : 2^s.countBits ≤ fee 3 s.countBits := by
      unfold fee
      exact (Nat.le_mul_of_pos_left _ (by decide : 0<3)).trans (Nat.le_add_right ..)
    unfold finish widths number at limit;omega
  · change s.number start+s.rows<2^wb
    unfold finish widths at limit;omega

include prior limit in
/-- All read-only global sources and nine data banks are eligible at the next
mask stage, including every padded tail of an empty host/block array. -/
theorem mask_inputs (b:Fin s.blocks) :
    ((s.channels start pop occupied).occupied b).Fits wb (s.finish start) ∧
    ∀f,((s.channels start pop occupied).primitive b f).Fits wb (s.finish start) := by
  have older:start≤ s.finish start:=by unfold finish widths number counting pointers «public» rom gather;omega
  have a:=prior.actorEnd b
  constructor
  · exact ⟨Nat.two_pow_pos _,by change (occupied b).size<_;omega,a.trans older⟩
  · intro f
    have end_:=s.live_end start pop occupied prior b f
    exact ⟨Nat.two_pow_pos _,by omega,end_⟩

end
end Hierarchy.DescentTerminalPrimitiveArena.Shape

end OAI
