import OAI.Hierarchy.DescentTerminalPrimitiveArena
import OAI.Hierarchy.DescentTerminalPointerColumns
import OAI.Hierarchy.DescentTerminalRoleTables

namespace OAI
/-! # Exact layout arguments of the native role, public, pointer, count and private-width passes -/
namespace Hierarchy.DescentTerminalPrimitiveArena
open ProtocolRAM DescentTerminalVertexFields DescentTerminalPointerDigits ThreeFlat.RAM
open scoped Classical
noncomputable section

def actual (blocks shops cap nodes slots ptrBits countBits:ℕ):Shape:=
  ⟨blocks,shops,columns cap nodes slots,ptrBits,countBits⟩

namespace Shape
variable (s:Shape) (start pop:ℕ) (occupied:Fin s.blocks→Bank) (prior:s.Prior start pop occupied)
    {wb:ℕ} (limit:s.finish start<2^wb)
local notation "inputs" => s.channels start pop occupied
local notation "fee₀" => fee s.columns s.pointerBits
local notation "fee₂" => fee 3 s.countBits

/-- All parameters that relate the native arena to the wired family chart.
The upper bounds refer to its actual exclusive end, so the next phase can start there. -/
structure Realized : Prop where
  source_room : DescentTerminalPointerFrame.Room (s.sources start pop) (s.counting start) s.countBits s.rows wb
  role_first : start+s.rows+s.rows<2^wb
  pointer_radix : 2^s.pointerBits<2^wb
  pointer_limit : s.pointers start+s.rows<2^wb
  count_later : s.counting start+fee₂+s.rows≤ s.widths start
  width_limit : s.widths start+s.rows<2^wb
  phase_order : start≤ s.gather start ∧ s.gather start≤ s.counting start
  live_inputs : ∀b,((inputs).occupied b).Fits wb (s.finish start) ∧ ∀f,((inputs).primitive b f).Fits wb (s.finish start)
  old_population : ∀b,((inputs).primitive b 3).base+((inputs).primitive b 3).size≤ start
  old_actor : ∀b,((inputs).occupied b).base+((inputs).occupied b).size≤ start
  keep_actor : ∀b,s.shops≤((inputs).occupied b).size
  keep_family : ∀b f,s.shops≤((inputs).primitive b f).size
  from_base : ∀b f,((inputs).primitive b (DescentTerminalPrivateSourceChannels.family f)).base=
      (s.sources start pop f).base+b.val*s.shops
  pointer_prior : ∀b (f:Fin 8),f=1 ∨ f=3 ∨ f=5 ∨ f=6→((inputs).primitive b f).base+((inputs).primitive b f).size≤ s.gather start
  count_prior : ∀b (f:Fin 8),f≠2→f≠4→((inputs).primitive b f).base+((inputs).primitive b f).size≤ s.counting start

include prior limit in
theorem realized (positive:0<s.columns) : s.Realized (wb:=wb) start pop occupied := by
  have covered:2^s.pointerBits≤fee₀ := by
    exact (Nat.le_mul_of_pos_left _ positive).trans (Nat.le_add_right ..)
  have upper:=limit
  unfold finish widths number counting pointers «public» rom gather at upper
  refine ⟨s.count_room start pop occupied prior limit,by omega,by omega,?_,?_,?_,?_,
    s.mask_inputs start pop occupied prior limit,?_,prior.actorEnd,prior.actorSize,
    fun b f=>s.capacity start pop occupied b f (prior.actorSize b),s.source_base start pop occupied,
    s.old_frame start pop occupied prior,s.count_frame start pop occupied prior⟩
  · unfold pointers «public» rom gather;omega
  · unfold widths number;omega
  · unfold finish at limit;omega
  · constructor
    · unfold gather; omega
    · unfold counting pointers «public» rom; omega
  · intro b
    have old:=prior.oldPopulation
    have hb:=s.bounds b
    change pop+b.val*s.shops+pad s.shops≤ start
    unfold guard at old;omega

variable (roleBits:Fin 6→ℕ) (roleInput:Fin 6→Bank) (advice:ℕ)
include limit in
theorem paired_fits (input:∀f,(roleInput f).Fits wb start) (static:advice+DescentTerminalRoleTables.count roleBits≤ start) :
    (DescentTerminalCombinedRole.emit (DescentTerminalRoleTables.role roleBits roleInput advice)).Fits wb start ∧
    (DescentTerminalCombinedRole.emit (DescentTerminalRoleTables.arity roleBits roleInput advice)).Fits wb start := by
  apply DescentTerminalRoleTables.fits roleBits roleInput advice start wb input static
  have h:=limit;unfold finish widths number counting pointers «public» rom gather at h;omega
end Shape
end
end Hierarchy.DescentTerminalPrimitiveArena

end OAI
