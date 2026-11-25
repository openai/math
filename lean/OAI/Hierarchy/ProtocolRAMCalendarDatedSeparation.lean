import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMCalendarArena

namespace OAI
/-! # The original chronological ordering preserves every earlier machine verdict -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {w q goods : ℕ}

/-- A verdict in its own dated interval is protected from every later write. -/
theorem separated_of_dated (C : Chart w q goods) (A : Arena)
    (floor : ∀e x,x<A.base C.mesh e→protected C x e)
    (limit : ∀a,Event.attempt a∈events C.mesh →
      (repair C a).verdict<A.base C.mesh (.attempt a)+A.stride) :
    separated C (events C.mesh) := by
  have increasing : (events C.mesh).Pairwise (fun e f=>position C.mesh e<position C.mesh f) := by
    apply (List.pairwise_map (f:=position C.mesh) (R:=(·<·))).mp
    rw [positions]
    exact List.pairwise_lt_range
  have go (es : List Event) (sub : ∀e∈es,e∈events C.mesh)
      (sorted : es.Pairwise (fun e f=>position C.mesh e<position C.mesh f)) : separated C es := by
    induction es with
    | nil => trivial
    | cons e es ih =>
      obtain ⟨before,rest⟩:=List.pairwise_cons.mp sorted
      have tail:=ih (fun x hx=>sub x (List.mem_cons_of_mem _ hx)) rest
      cases e with
      | feed _ => exact tail
      | attempt a =>
        refine ⟨?_,tail⟩
        intro x hx
        apply floor x
        exact (limit a (sub _ (by simp))).trans_le (A.apart C.mesh (before x hx))
  exact go _ (fun _ h=>h) increasing

/-- The scan that reads the saved flags fits at the first address after the
last physical event, including calendars with no attempt events. -/
theorem historyFlag_fits_of_dated (C : Chart w q goods) (A : Arena) (wide : 0<w)
    (limit : ∀a,Event.attempt a∈events C.mesh →
      (repair C a).verdict<A.base C.mesh (.attempt a)+A.stride) :
    (historyFlag C (events C.mesh)).Fits w (A.endAddress C.mesh) := by
  have go (es : List Event) (sub : ∀e∈es,e∈events C.mesh) :
      (historyFlag C es).Fits w (A.endAddress C.mesh) := by
    induction es with
    | nil => trivial
    | cons e es ih =>
      have tail:=ih (fun x hx=>sub x (List.mem_cons_of_mem _ hx))
      cases e with
      | feed _ => exact tail
      | attempt a =>
        have here:=sub (.attempt a) (by simp)
        have last:=(limit a here).trans_le (A.within C.mesh _ here)
        have bank : (⟨(repair C a).verdict,0⟩ : Bank).Fits w (A.endAddress C.mesh) := by
          exact ⟨by change 0 < 1; decide,by simpa only [Bank.size,pow_zero] using Nat.one_lt_two_pow wide.ne',by
            change (repair C a).verdict+1≤A.endAddress C.mesh
            omega⟩
        exact ⟨⟨bank,trivial⟩,trivial,tail,trivial⟩
  exact go _ (fun _ h=>h)

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
