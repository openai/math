import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentOrdinarySlotDegree
import OAI.Hierarchy.DescentMaximumDegreeQuota

namespace OAI
/-! The degree stored by the chosen physical date registers. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
open scoped BigOperators Classical
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree)
variable (tags : ∀ c, (traces c).path.kinds = kindCalendar S.rounds S.height)

include tags in
omit [Fintype P] in
theorem issued_degree (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (m : Move w)
    (posted : issued traces b i e a m) :
    m.next.ports.venue.degree = atRound ((i+1) % (S.rounds+1)) := by
  obtain ⟨c, e⟩ := e
  have kind := e.shown
  rw [tags c] at kind
  cases e with
  | ordinary before ticket after cut =>
    obtain ⟨positive, space, rfl⟩ := posted
    obtain ⟨degreeAt, next⟩ := ordinary_slot_degree G.b S.rounds b.gain S.height i G.base_pos kind
    change ordinaryDegree (OrdinaryLink.publicDegree S.rounds G.b
      (((capCalendar G.b S.rounds b.gain S.height).drop i).head?.getD 0)) = _
    rw [degreeAt, next] ; rfl
  | reset before closed after cut =>
    obtain ⟨cap, space, rfl⟩ := posted
    change 3 = _
    rw [reset_slot_successor S.rounds S.height i kind] ; rfl

theorem round_degree_le (t i : ℕ) : atRound (i % (t+1)) ≤ maximumDegree (t+1) :=
  Finset.single_le_sum (f := fun j : Fin (t+1) => atRound j.val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨i % (t+1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (t+1)))

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
