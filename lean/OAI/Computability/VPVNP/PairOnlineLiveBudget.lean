import OAI.Computability.VPVNP.CompressorOnlineBudget
import OAI.Computability.VPVNP.CursorBranchCommunication
import OAI.Computability.VPVNP.PairLinkSlack

/-!
# Live caps of the online descriptor program

The calendar, recipe, and data-worker calls are the reports of the
fixed online table. Its local clock is chosen from fixed catalog
parameters, and the global bound holds before the input assignment,
term choices and online memory are selected.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseVisits

open BurstRAM Compression Schedule CursorNetwork CursorBounds Filter

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- Choose a local clock covering the finite controller and worker link.
At large input lengths all reports fit the physical burst and private
clock, with any fixed margins for the enclosing live instruction table. -/
theorem eventually_selectedOnline (B : S.Templates) (u : PairExponents B.growthConstant)
    (P : Plan S) (H I q b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {d i j : ℕ} {C : Catalog d} (Q : Online.Config C i j)
    (probeMargin tickMargin : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let K := H + 30 + 2*(i+j) + 20 + 6*(arity C+1) + 2*Online.N d (i+j) + 5
    ∀ᶠ n : ℕ in atTop,
      let cap := K*(n.log2+1)^q
      let w := wordBits b n
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        ∀ (z : (B.execute f hf T hT X).Choices) (p : Ports w) (initial : List (Directory.Row d w))
          (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) X.positions v)
          (steps : List (Online.Run.Step d (i+j) w)) (m : Memory w) (state : Word w),
          calls initial ≤ I*X.positions → Online.Run.Valid Q p cap m steps →
          m p.tag.val = LiveStageLink.tagWord w (Online.calendarIndex d (i+j)) →
          steps.map Online.Run.Step.row = branchRows P X.positions
            (executeLevels B f hf T hT X z) initial groups →
          let rs := Online.Run.reports Q p m steps
          runSegment (Online.program Q p) cap (some state) m (Online.Run.choices steps) = some rs ∧
          after m (eventLog rs) = Online.Run.finalMemory (C := C) p m steps ∧
          endState (some state) rs = none ∧
          (∀ r ∈ rs, 1+r.probes+probeMargin ≤ liveBucket u.δ n ∧ r.events.length+tickMargin ≤ n) ∧
          (RAMBuckets.cost Report.probes rs : ℝ) < ε * processorCount b n * liveBucket u.δ n := by
  intro K
  let rate := (2*(I + (S.steps+1)*max 1 (slotDegree S)*P.levelRate)+1)*K
  have hlocal := eventually_absorb_polylog (K : ℝ) q
    (show (0 : ℝ) < 1/2 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [hlocal, eventually_pairBurstSlack u (probeMargin+1),
    BurstRAM.eventually_polylog_le (K+tickMargin) q, eventually_ge_atTop 1,
    CursorRAM.eventual_word_room b hb' (PolynomiallyBounded.const (Online.N d (i+j))),
    eventually_pairAccesses B u b hb rate (q+1) hε]
    with n hlocal hburst hticks hn hfit hbudget
  intro cap w base lanes labels hD hT A _ f hf X T z p initial groups
    steps m state hinit valid tag rows rs
  have hL : 1 ≤ (n.log2+1)^q := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hcap : K ≤ cap := Nat.le_mul_of_pos_right _ hL
  have hc := selected_online_budget B u P K I q b n hn labels hD hT f hf z Q p initial groups hinit
    steps m state cap valid tag hfit.le (by dsimp only [K] at hcap; omega)
    (by dsimp only [K] at hcap; omega) le_rfl rows
  have hsmall : (cap : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
    dsimp only [cap]
    push_cast
    simpa only [Real.rpow_zero, mul_one, one_mul] using hlocal
  have htime : cap + tickMargin ≤ n := by
    apply le_trans _ hticks
    exact (Nat.add_le_add_left (Nat.le_mul_of_pos_right tickMargin hL)
      (K*(n.log2+1)^q)).trans_eq (Nat.add_mul ..).symm
  refine ⟨hc.1,hc.2.1,hc.2.2.1,fun r hr => ?_,?_⟩
  · obtain ⟨he, hp⟩ := hc.2.2.2.1 r hr
    have h : (cap : ℝ)+(probeMargin+1 : ℕ) ≤ liveBucket u.δ n :=
      (add_le_add_left hsmall ((probeMargin+1 : ℕ) : ℝ)).trans hburst
    have hh : cap+(probeMargin+1) ≤ liveBucket u.δ n := by exact_mod_cast h
    omega
  · let Y := (B.execute f hf T hT X).finalState z
    let c := (B.execute f hf T hT X).termChain (B.records f hf T hT X) z
    have he : rate*initialPositions b n*(n.log2+1)^(q+1) ≤ branchAccesses X Y c rate (q+1) n := by
      rw [← pairInput_positions S labels hD]
      unfold branchAccesses
      apply le_trans _ (Nat.le_add_right _ _)
      exact (Nat.mul_assoc ..).le.trans (Nat.mul_le_mul_left rate (Nat.le_add_right _ _))
    exact (Nat.cast_le.mpr (hc.2.2.2.2.trans he)).trans_lt (hbudget labels hD hT A f hf z).1

end CompressorRecords.PhaseVisits

end VPVNP
end Computability
end OAI
