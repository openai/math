import OAI.Hierarchy.DescentTerminalSliceWordRead
import OAI.Hierarchy.DescentTerminalSliceShelf

namespace OAI
/-! # The original physical gather and the six printed role banks -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentTerminalPointerDigits DescentOperandStateBanks DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {L d H blocks w:ℕ} {width:Fin 6→ℕ}
variable (base:ℕ) (chart:Fin L→Fin blocks→Gather.Address)
    (write:(f:Fin 6)→(Fin L→Cell d)→Cell (width f))
local notation "rows" => blocks*H
local notation "sweep" => Gather.dropOff base blocks H L chart
def program (H w:ℕ) := (ProtocolRAM.program w (Gather.dropOff base blocks H L chart)).seq
  («prefix» write (blocks*H) w base 6 le_rfl)
def memory (H:ℕ) (m:Memory w) := after write (blocks*H) base
  (ProtocolRAM.result (Gather.dropOff base blocks H L chart) m) 6 le_rfl
def cost (H d:ℕ) := clock (Gather.dropOff base blocks H L chart)+clocks L d (blocks*H) 6
variable (m:Memory w) (ok:∀j x,(chart j x).Fits base H w) (off:2^d<2^w) (room:fence base L d (blocks*H)<2^w)
include ok off room in
theorem native :
    let stop:=fence base L d rows
    let final:=memory base chart write H m
    (program base chart write H w).Exec m final (cost base chart H d) ∧ CheapCode (program base chart write H w) ∧
    (∀i,i<base ∨ stop≤ i→final i=m i) ∧
    ∀(f:Fin 6)(x:Fin blocks)(h:Fin H),final ((field base L d rows f.val).base+
      (finProdFinEquiv (x,h)).val)=((write f (seen chart m x h)).val:Word w) := by
  have end_:=monotone base L d rows (Nat.zero_le 6)
  have edge:base+L*(blocks*H)≤ stage base L d rows 0:=by simp [stage,Gather.rom,DescentOperandStateBanks.guard]
  have rawSpace:base+(L*blocks)*H<2^w:=by
    rw [Nat.mul_assoc]
    exact edge.trans_lt (end_.trans_lt room)
  let prep:=ProtocolRAM.result sweep m
  obtain ⟨gathered,cheap,printed,frame,_⟩:=Gather.fetch_blocks chart m base H ok rawSpace
  obtain ⟨converted_,cheap',«protected»,pages⟩:=converted base write prep off room 6 le_rfl
  refine ⟨@Procedure.Exec.then w (ProtocolRAM.program w sweep) («prefix» write rows w base 6 le_rfl)
    m prep _ (clock sweep) (clocks L d rows 6) (@gathered) (@converted_), cheap_seq cheap cheap', ?_, ?_⟩
  · intro z side
    rcases side with low|high
    · exact («protected» _ (.inl (low.trans_le ((Nat.le_add_right ..).trans edge)))).trans (frame _ (.inl low))
    · exact («protected» _ (.inr high)).trans (frame _ (.inr (by rw [Nat.mul_assoc];exact edge.trans (end_.trans high))))
  · intro f x h
    refine (pages f f.isLt (finProdFinEquiv (x,h))).trans ?_
    apply congrArg (fun values : Fin L → Cell d => ((write f values).val : Word w))
    funext j
    exact congrArg (fun cell : Word w => (cell.val : Cell d)) (printed j x h)

end
end Hierarchy.DescentTerminalSliceShelf

end OAI
