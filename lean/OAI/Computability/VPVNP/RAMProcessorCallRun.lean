import OAI.Computability.VPVNP.RAMProcessorProbeContinue

/-!
# Correctness of the physical call loop

Strong induction on unspent private instruction fuel follows every sequence
of adaptive reads and writes. At each callback the proof uses the actual
site table, the three remaining allowances, and the single physical record
emitted for the probe. It covers malformed guesses and every cap rejection.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k H F : ℕ} {hw : 2 ≤ w}

theorem segment_correct (T : Template p r k) (s : Snapshot w p r k) (ys : List (WordRecord w))
    (start ord : Word w) (hin : InCall hw H F s ys start ord) :
    ∃ t ≤ (s.fuel+1)*segmentWork w F, SegmentRun T hw H F s ys start ord t := by
  suffices allFuel : ∀ n (s : Snapshot w p r k) ys start ord, s.fuel = n →
      InCall hw H F s ys start ord →
      ∃ t ≤ (n+1)*segmentWork w F, SegmentRun T hw H F s ys start ord t by
    exact allFuel s.fuel s ys start ord rfl hin
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s ys start ord hf hin
    let y := LocalProcessor.scan T s.pub s.fuel s.cfg s.choices
    let z := s.afterLocal y
    have hz : InCall hw H F z ys start ord := hin.afterLocal T
    obtain ⟨t, ht, run⟩ := segment_run T s F hin.privateClock
    have hpos (hn : y.exit ≠ .reject) : z.fuel < n := by
      rw [← hf]; exact LocalProcessor.scan_fuel_lt T s.pub s.fuel s.cfg s.choices hn
    have probe (a : ProbeStep w p r) (ha : a.callback = y.exit)
        (haPos : 0 < allowance z) (hbits : a.accepts z) :
        ∃ d ≤ 200*(w+1)+n*segmentWork w F,
          Meets T hw H F z ys start ord (.callback y.exit) (pending T z y.exit) d := by
      have hy : z.fuel < n := hpos (by rw [← ha]; cases a <;> simp [ProbeStep.callback])
      obtain ⟨d, hd, hp⟩ := a.continue_run T hz haPos hbits (by
        dsimp only
        intro hnext
        let u := a.finish z hw start ord (hz.costRoom haPos) hz.ordRoom
        exact ih u.fuel (by simpa only [u, a.finish_fuel] using hy) u _ _ _ rfl hnext)
      rw [ha] at hp
      exact ⟨d, hd.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hy) _), hp⟩
    have cb : ∃ d ≤ 200*(w+1)+n*segmentWork w F,
        Meets T hw H F z ys start ord (.callback y.exit) (pending T z y.exit) d := by
      cases he : y.exit with
      | next j | choose j l =>
        have hterminal := (LocalProcessor.scan_bounds T s.pub s.fuel s.cfg s.choices).2.2.1
        change LocalProcessor.externalOrTerminal y.exit at hterminal
        rw [he] at hterminal
        exact False.elim hterminal
      | reject => exact ⟨1, by omega, pending_reject T z ys start ord⟩
      | accept => exact ⟨3, by omega, pending_accept T hz⟩
      | returnState src => exact ⟨8*w+6, by omega, pending_return T hz src⟩
      | read dst addr pc =>
        by_cases hc : allowance z = 0
        · obtain ⟨d, hd, hr⟩ := read_no_credit T z ys start ord dst addr pc hc (hw := hw) (H := H) (F := F)
          exact ⟨d, by omega, hr⟩
        · cases hg : takeWord w z.choices with
          | none =>
            obtain ⟨d, hd, hr⟩ := read_no_guess T hz dst addr pc (by omega) hg
            exact ⟨d, by omega, hr⟩
          | some pair =>
            obtain ⟨v,tail⟩ := pair
            have h := probe (.read dst addr pc v tail) he.symm (by omega)
              ((takeWord_eq_some_iff ..).mp hg)
            simpa only [he] using h
      | write addr src pc =>
        by_cases hc : allowance z = 0
        · obtain ⟨d, hd, hr⟩ := write_no_credit T z ys start ord addr src pc hc (hw := hw) (H := H) (F := F)
          exact ⟨d, by omega, hr⟩
        · have h := probe (.write addr src pc) he.symm (by omega) trivial
          simpa only [he] using h
    obtain ⟨d, hd, hr⟩ := cb
    refine ⟨t+d, ?_, scan_then_pending T s run hr⟩
    have hbudget := hin.privateClock
    have hm : s.fuel*(ISA.prepareBound w F+4) ≤ F*(ISA.prepareBound w F+4) :=
      Nat.mul_le_mul_right _ (by omega)
    have overhead : segmentWork w F = F*(ISA.prepareBound w F+4) + (ISA.prepareBound w F+4) + 200*(w+1) := by
      simp only [segmentWork, Nat.add_mul, Nat.one_mul]
    rw [Nat.succ_mul]
    omega

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
