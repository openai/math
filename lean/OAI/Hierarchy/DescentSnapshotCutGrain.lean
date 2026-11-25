import OAI.Hierarchy.DescentDatedBranchEvents
import OAI.Hierarchy.DescentOrdinarySlotDegree
import OAI.Hierarchy.DescentResetSlotIndex

namespace OAI
/-! # The amount on the ordinary state immediately preceding a reset -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler
noncomputable section
variable {F Pin : Type} [Field F] [Fintype Pin] {bits : Pin→ℕ} {d : ℕ} {G : PoweredGadget F}
    {S : AtomSchedule} {p k wire hist : ℕ} {q ε : ℝ}
    {t : RunTrace G q ε S k wire hist S.length bits d}
private theorem reset_grain_succ {i : ℕ} (slot : i%(S.rounds+1)=S.rounds) :
    S.grainAt G.b p i=S.grainAt G.b p (i+1) := by
  let e:=i/(S.rounds+1)
  have split : e*(S.rounds+1)+i%(S.rounds+1)=i := by
    simpa only [e,Nat.mul_comm] using Nat.div_add_mod i (S.rounds+1)
  have before : e*(S.rounds+1)+S.rounds=i := by
    simpa only [slot] using split
  have after : (e+1)*(S.rounds+1)=i+1 := by
    rw [Nat.succ_mul]
    omega
  simpa only [before,after] using S.grain_reset G.b p e

omit [Fintype Pin] in
private theorem snapshot_append_assoc {I A B V : MarkedWorld F d Pin bits}
    {j₀ z₀ D₀ j₁ z₁ D₁ j₂ z₂ D₂ j₃ z₃ D₃ : ℕ}
    {first : Reached I G q ε S k j₀ z₀ D₀ wire hist} {one : Reached A G q ε S k j₁ z₁ D₁ wire hist}
    {two : Reached B G q ε S k j₂ z₂ D₂ wire hist} {last : Reached V G q ε S k j₃ z₃ D₃ wire hist}
    (a : Path first one) (b : Path one two) (c : Path two last) :
    (a.append b).append c = a.append (b.append c) := by
  induction c with
  | here => rfl
  | ordinary prev tick ih => exact congrArg (fun p : Path first _ => p.ordinary tick) ih
  | reset prev closed ih => exact congrArg (fun p : Path first _ => p.reset closed) ih

omit [Fintype Pin] in
/-- Each physical prefix of the named trace has its specified public grain. -/
theorem Path.snapshot_cut_grain (kinds : t.path.kinds=kindCalendar S.rounds S.height)
    (first : t.firstGrain=S.grainAt G.b p 0) {age z D : ℕ} {U : MarkedWorld F d Pin bits}
    {r : Reached U G q ε S k age z D wire hist} (before : Path t.first r)
    (after_ : Path r t.last) (joined : before.append after_=t.path) : z=S.grainAt G.b p age := by
  induction before with
  | here => exact first
  | @ordinary _ i _ _ _ _ src prior _ he T ballot norm dst ticket ih =>
    have tag:=ticket.kind_on_cut prior after_ joined kinds
    have inside:=(ordinary_slot_factor G.b S.rounds 0 S.height i tag).1
    have shorter:=after_.kinds_length
    have active : i<S.length:=by omega
    have live : i/(S.rounds+1)<S.height:=by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      simpa only [AtomSchedule.length,Nat.mul_comm] using active
    have split : (i/(S.rounds+1))*(S.rounds+1)+i%(S.rounds+1)=i := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i (S.rounds+1)
    have next:=S.grain_ordinary G.b p live inside
    rw [split] at next
    have h:=ih ((Path.here.ordinary ticket).append after_)
      ((snapshot_append_assoc prior (Path.here.ordinary ticket) after_).symm.trans joined)
    exact Nat.eq_of_mul_eq_mul_right G.base_pos (ticket.grainStep.symm.trans (h.trans next))
  | @reset _ i _ _ _ _ _ _ _ _ _ src prior ctl B ih =>
    have tag:=reset_kind_on_cut B prior after_ joined kinds
    exact (ih ((Path.here.reset B).append after_)
      ((snapshot_append_assoc prior (Path.here.reset B) after_).symm.trans joined)).trans
      (reset_grain_succ (reset_slot_index S.rounds S.height i tag))

omit [Fintype Pin] in
theorem Path.Event.resetGrain {age z D n h C f g cut tail : ℕ} {U : MarkedWorld F d Pin bits}
    {r : Reached U G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (kinds : t.path.kinds=kindCalendar S.rounds S.height) (first : t.firstGrain=S.grainAt G.b p 0)
    (before : Path t.first r) (B : ClosedReset r ctl) (after_ : Path B.next t.last)
    (joined : (before.reset B).append after_=t.path) : z=S.grainAt G.b p (age+1) :=
  (before.reset B).snapshot_cut_grain kinds first after_ joined

end
end Hierarchy.DescentSixParty.Chronology

end OAI
