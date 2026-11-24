import OAI.Computability.VPVNP.CompressorDirectoryBudget
import OAI.Computability.VPVNP.CompressorRecordsOnlineRun

/-!
# The selected descriptor branch in the online instruction table

This adapter executes the actual dispatcher and data workers, and accounts
for every returned report. The finite phase plan and local work bounds
precede all graph and term choices. A valid online directory supplies the
actual memory evolution through the calendar, recipes and workers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseVisits

open BurstRAM Compression Schedule CursorNetwork CursorBounds

private theorem row_valid {d i j w : ℕ} {C : Catalog d} {Q : Online.Config C i j} {p : Ports w}
    {cap : ℕ} {steps : List (Online.Run.Step d (i+j) w)} {m : Memory w}
    (h : Online.Run.Valid Q p cap m steps) :
    ∀ r ∈ steps.map Online.Run.Step.row, r.Valid C p := by
  induction steps generalizing m with
  | nil => simp
  | cons s ss ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hmem
    · exact h.1.source
    · exact ih h.2 _ hmem

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- The fixed online table, started in calendar state, accepts the selected
tape and stays within the stated local and total communication allowances. -/
theorem selected_online_budget (B : S.Templates) (u : PairExponents B.growthConstant) (P : Plan S)
    (H I q b n : ℕ) (hn : 1 ≤ n) {base lanes : ℕ}
    (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
    (hT : blockCount (u.θ : ℝ) n*S.laneBits ≤ lanes)
    {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
    (z : (B.execute f hf _ hT (pairInput S labels hD)).Choices)
    {d w i j : ℕ} {C : Catalog d} (Q : Online.Config C i j) (p : Ports w)
    (initial : List (Directory.Row d w))
    (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) (pairInput S labels hD).positions v)
    (hinit : calls initial ≤ I*(pairInput S labels hD).positions)
    (steps : List (Online.Run.Step d (i+j) w)) (m : Memory w) (state : Word w) (cap : ℕ)
    (valid : Online.Run.Valid Q p cap m steps)
    (tag : m p.tag.val = LiveStageLink.tagWord w (Online.calendarIndex d (i+j)))
    (fit : Online.N d (i+j) ≤ 2^w)
    (cal : 30+2*(i+j)+2*Online.N d (i+j)+5 ≤ cap)
    (launch : 20+6*(arity C+1)+2*Online.N d (i+j)+5 ≤ cap)
    (clock : cap ≤ H*(n.log2+1)^q) :
    let X := pairInput S labels hD
    let T := blockCount (u.θ : ℝ) n
    let K := (2*(I + (S.steps+1)*max 1 (slotDegree S)*P.levelRate)+1)*H
    steps.map Online.Run.Step.row = branchRows P X.positions (executeLevels B f hf T hT X z) initial groups →
    let rs := Online.Run.reports Q p m steps
    runSegment (Online.program Q p) cap (some state) m (Online.Run.choices steps) = some rs ∧
      after m (eventLog rs) = Online.Run.finalMemory (C := C) p m steps ∧ endState (some state) rs = none ∧
      (∀ r ∈ rs, r.events.length < cap ∧ r.probes < cap) ∧
      RAMBuckets.cost Report.probes rs ≤ K * initialPositions b n * (n.log2+1)^(q+1) := by
  intro X T K hs rs
  have run := Online.Run.execute Q p steps m state cap tag fit cal launch valid
  have eff := Online.Run.effect Q p steps m state valid
  have same : Online.Run.choices steps =
      (branchRows P X.positions (executeLevels B f hf T hT X z) initial groups).flatMap Online.rowChoices ++ [[]] := by
    rw [← hs,Online.Run.choices,List.flatMap_map]
  refine ⟨run,eff.1,eff.2,online_run_budget B u P H I q b n hn labels hD hT f hf z C p initial groups hinit
    _ state m cap rs ?_ clock (same ▸ run)⟩
  change ∀ r ∈ branchRows P X.positions (executeLevels B f hf T hT X z) initial groups, r.Valid C p
  rw [← hs]
  exact row_valid valid

end CompressorRecords.PhaseVisits

end VPVNP
end Computability
end OAI
