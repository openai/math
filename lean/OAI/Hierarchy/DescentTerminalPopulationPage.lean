import OAI.Hierarchy.DescentTerminalPopulationRAM
import OAI.Hierarchy.DescentTerminalPointerGather

namespace OAI
/-! # Install and emit the node population for all blocks on the terminal tape -/
namespace Hierarchy.DescentTerminalPopulation.RAM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOperandStateBanks DescentTerminalPointerDigits
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (H G M a b c lo : ℕ) {X w : ℕ} (old : Fin X→Bank) (ext : Bank)
local notation "high" => lo+lease H G M a c lo
local notation "fields" => fun x=>body H G M a c lo (old x) ext
local notation "steps" => Gather.reads high H fields
def issue (w:ℕ) := (setup H G M a b c lo w).seq (ProtocolRAM.program w steps)
def done (m:Memory w) := result steps (ready H G M a b c lo m)
def ticks := (4+10*lease H G M a c lo)+clock steps
def population (x:Fin X) := Gather.banks high H x

theorem run (m:Memory w) (fit:∀x,Fit H G M a c lo (old x) ext high w)
    (space:high+X*H<2^w) :
    (issue H G M a b c lo old ext w).Exec m (done H G M a b c lo old ext m) (ticks H G M a c lo old ext) ∧
    CheapCode (issue H G M a b c lo old ext w) ∧
    ∀i,i<lo ∨ high+X*H≤ i→done H G M a b c lo old ext m i=m i := by
  have room:high<2^w:=(Nat.le_add_right ..).trans_lt space
  obtain ⟨pre,_,_,_,kept⟩:=mount H G M a b c lo m room
  obtain ⟨cpu,cheap,_,hold⟩:=Gather.fetch high H fields (ready H G M a b c lo m)
    (fun x=>clear H G M a c lo _ ext high (fit x)) space
  refine ⟨pre.then cpu,cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) cheap,?_⟩
  intro i away
  rcases away with hi|hi
  · exact (hold i (.inl (hi.trans_le (Nat.le_add_right ..)))).trans (kept i (.inl hi))
  · exact (hold i (.inr hi)).trans (kept i (.inr ((Nat.le_add_right ..).trans hi)))

theorem read (m:Memory w) (fit:∀x,Fit H G M a c lo (old x) ext high w)
    (space:high+X*H<2^w) (paid:Fin X→Fin H→Fin G→Cell a) (counts:Fin H→Cell c)
    (paidAt:∀x,∀j:Row H G M,m ((old x).base+(row H G M j).val)=((data (paid x) j).val:Word w))
    (countsAt:∀h:Fin H,m (ext.base+h.val)=((counts h).val:Word w))
    (x:Fin X) (h:Fin H) :
    done H G M a b c lo old ext m ((population H G M a c lo x).base+h.val)=
       (words (M:=M) b (paid x) (fun z=>(counts z).val) h:Word w) := by
  obtain ⟨_,_,output,_⟩:=Gather.fetch high H fields (ready H G M a b c lo m)
    (fun x=>clear H G M a c lo _ ext high (fit x)) space
  exact (output x h).trans (body_read H G M a b c lo _ ext high (fit x) m (paid x) counts (paidAt x) countsAt h)

theorem price : ticks H G M a c lo old ext≤
    8+10*lease H G M a c lo+X*(4+H*(74+60*chunks G M)) := by
  have cost:=Gather.fetch_price fields (35+30*chunks G M) high H (fun x=>work H G M a c lo _ _)
  unfold ticks
  convert Nat.add_le_add_left cost (4+10*lease H G M a c lo) using 1; ring

end
end Hierarchy.DescentTerminalPopulation.RAM

end OAI
