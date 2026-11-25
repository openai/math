import OAI.Hierarchy.DescentDatedTicketWords
import OAI.Hierarchy.DescentDatedOperandRootSize
import OAI.Hierarchy.DescentDatedOperandTicketValue
import OAI.Hierarchy.DescentDatedRoutedArguments

namespace OAI
/-! # Side and routing fields of a dated ticket as read by the ordinary operand resolver -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentSIMDLookup DescentPriorOperandColumns DescentRawCablePanel.DepotRAM.Operand
open scoped Classical Fin.CommRing
noncomputable section

private theorem flag_at (k n : ℕ) (small : n≤1) : flagCell k (decide (n=1))=(n:Cell (k+2)) :=by
  apply Fin.ext
  have fits : n < 2^(k+2) := by
    have := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤k+2 by omega)
    omega
  rw [Fin.val_natCast,Nat.mod_eq_of_lt fits]
  interval_cases n <;> rfl

theorem flags_of_material (blocks actor kind rank old key start peer mouth : ℕ) (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ)
    (first : raw 2≤1) (second : raw 3≤1) (mark : raw 5≤1) :
    Flags («fields» blocks actor kind rank old key start peer mouth anchor raw) :=by
  unfold «fields»
  split
  · constructor <;> exact Nat.zero_le 1
  split
  · refine ⟨first,second,?_⟩
    change (if _ then raw 5 else 1)≤1
    by_cases zero : (if actor=2 then mouth else anchor 2)=0
    · simpa only [ite_eq_left zero] using mark
    · simp only [ite_eq_right zero,le_refl]
  · constructor <;> exact Nat.zero_le 1

theorem read_route_table (k : ℕ) (word : Fin 8 → ℕ) (good : Flags word) (f : Fin 8) :
    (if t : f.val<5 then (recordedSide k word).digits ⟨f.val,by omega⟩
       else recordedRole k word ⟨f.val-5,by have:=f.isLt;omega⟩)=(word f:Cell (k+2)) :=by
  fin_cases f <;> first | rfl | exact flag_at k _ good.first | exact flag_at k _ good.second | exact flag_at k _ good.marked

end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPriorOperandColumns DescentPackedZip DescentDatedOperandCoordinates
open DescentDatedOperandReadPipeline DescentDatedPriorOperand DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
set_option hygiene false
local notation "l₀" => v.resolver
local notation "g₀" => v.ticketReadGeometry
variable (words : Fin (l₀).jobs→Fin (l₀).hosts→Fin (l₀).groups→Fin 8→ℕ)

def ticketSides (j h k) := Ticket.recordedSide (l₀).size (words j h k)
def ticketRoles (j : Fin (l₀).jobs) (f : Fin 3) (h : Fin (l₀).hosts) (k : Fin (l₀).groups) :=
  Ticket.recordedRole (l₀).size (words j h k) f

theorem target_at_ticket (flags : ∀j h k,Ticket.Flags (words j h k)) (j f h k) :
    v.routeTarget (v.ticketSides words) (v.ticketRoles words) j f h k=(words j h k f:Cell ((l₀).size+2)) :=
  Ticket.read_route_table _ _ (flags j h k) f

theorem ticket_target_sources {w : ℕ} (m : Memory w) (src : v.OriginSources) (bound : ℕ)
    (held : ∀j f,Held (g₀) bound m (src j f) (fun h k=>(words j h k f:Cell ((l₀).size+2))))
    (flags : ∀j h k,Ticket.Flags (words j h k)) :
    ∀j f,Source (src j f) (v.routeTarget (v.ticketSides words) (v.ticketRoles words) j f) (l₀).lanes m :=by
  intro j f
  have agree : v.routeTarget (v.ticketSides words) (v.ticketRoles words) j f=
      (fun h k=>(words j h k f:Cell ((l₀).size+2))) := funext fun h=>funext fun k=>v.target_at_ticket words flags j f h k
  rw [agree]
  exact (held j f).read

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
