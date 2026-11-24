import OAI.Computability.VPVNP.RAMProcessorCallStartup
import OAI.Computability.VPVNP.RAMProcessorPhysicalClock

/-!
# Linking the per-instruction call simulation to the bucket loop

The startup unit is charged before execution. A site with no remaining
credit rejects at startup. Successful startup resets the registers and log,
and the segment simulation then follows the real instruction table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

private theorem startup_graph (T : Template p r k) (first : Bool) (s : Snapshot w p r k)
    {ys} (h : CallReady hw H F first s ys) (hlt : s.cost.val < s.cap.val) (hs : 0 < s.siteLeft) :
    ∃ t ≤ (16*w+7+s.startTicks) + (r*(8*w+3)+3*(s.cfg.writes.length*(w+1)+1)+2),
      StackRuns (table T) t (atLabel T (startLabel first)) s.bank
        (atLabel T (.segment T.entry)) (s.prepared T hlt).bank := by
  have hH : 0 < s.publicH := h.publicH ▸ h.positive
  have hc := (Nat.succ_le_of_lt hlt).trans_lt s.cap.isLt
  obtain ⟨b, hb, fresh⟩ := fresh_run T (s.afterStart (s.cap-s.cost) hc)
  change b ≤ r*(8*w+3)+3*(s.cfg.writes.length*(w+1)+1)+2 at hb
  cases first with
  | true =>
    have run := first_run T s hH hs hlt
    exact ⟨_, by omega, run.trans fresh⟩
  | false =>
    have hg := h.global rfl
    have hgv := CallCredit.GlobalCredit.remaining_val s.cap s.cost hlt.le
    have he : s.globalLeft = s.cap-s.cost := Fin.ext (by omega)
    have run := newCall_run T s hH hs (by omega) hc
    rw [he] at run
    exact ⟨_, by omega, run.trans fresh⟩

/-- Fold the concrete call induction through both startup labels. -/
theorem startRuns_of_segments (T : Template p r k)
    (segments : ∀ (s : Snapshot w p r k) (ys : List (WordRecord w)) (start ord : Word w),
      InCall hw H F s ys start ord → ∃ t ≤ (s.fuel+1)*segmentWork w F,
        SegmentRun T hw H F s ys start ord t) :
    StartRuns T (CallReady hw H F) (perCallEstimate r w H F) := by
  intro first s ys hadm hd
  have hlt := hadm.cost_lt hd
  have bound := hadm.start_and_call_le
  by_cases hs : s.siteLeft = 0
  · have hf : first = false := by
      cases first with
      | false => rfl
      | true => have := hadm.firstCredit rfl; omega
    subst first
    have run := newCall_reject T s (Or.inr (Or.inl hs))
    have ht := Charges.failureTicks_le s.publicH s.siteLeft s.globalLeft
    have he : nativeCall T s = none := by simp [nativeCall, runChargedCall, hs]
    rw [he]
    refine ⟨_, ?_, run⟩
    unfold Snapshot.startTicks at bound
    omega
  · have hpos := Nat.pos_of_ne_zero hs
    let z := s.prepared T hlt
    obtain ⟨a, ha, run⟩ := startup_graph T first s hadm hlt hpos
    obtain ⟨b, hb, result⟩ := segments z ys s.cost 0 (hadm.prepared T hlt hpos)
    have hbf : b ≤ callWork w F := by
      change b ≤ (s.publicFuel+1)*segmentWork w F at hb
      exact hadm.publicFuel ▸ hb
    have he := nativeCall_prepared T s (hadm.publicH ▸ hadm.positive) hpos hlt
    rw [he]
    change (match z.localResult T with
      | none => RejectRun (table T) b (atLabel T (.segment z.cfg.pc)) z.bank
      | some (rep,tail) => ∃ u new, CallReady hw H F false u new ∧ CallReturn z u ys new s.cost 0 rep tail ∧
          StackRuns (table T) b (atLabel T (.segment z.cfg.pc)) z.bank (atLabel T .iteration) u.bank) at result
    cases hr : z.localResult T with
    | none =>
      rw [hr] at result
      exact ⟨_, by omega, run.thenReject result⟩
    | some pair =>
      obtain ⟨rep,tail⟩ := pair
      rw [hr] at result
      obtain ⟨u,new,hready,hprog,hret⟩ := result
      exact ⟨_, by omega, u,new,hready,hprog.startProgress T hlt,run.trans hret⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
