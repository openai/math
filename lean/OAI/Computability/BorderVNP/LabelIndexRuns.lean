import OAI.Computability.BorderVNP.LabelIndexRow
import Mathlib.Tactic.IntervalCases

/-! # Exact memory image and time of the compressed label-index initialization -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA VPVNP.BurstRAM

private theorem frame_eval (d : Reg) (f : Word 8) (pub : Arg → ℕ) (z : NatState) :
    (readFrame d 62 63 f).fixedEval pub z = ⟨Function.update (Function.update
      (Function.update z.reg 63 f.val) 62 (pub 0+f.val)) d (z.mem (pub 0+f.val)),z.mem⟩ := by
  simp (config := { decide := true }) [readFrame, Code.block,Code.fixedEval,Code.evalNat,addressOp,
    Function.update_comm (show (62 : Reg) ≠ 63 by decide)]

private theorem frame_safe (d : Reg) (f : Word 8) (pub : Arg → ℕ) (z : NatState) (w : ℕ)
    (h : pub 0+f.val < 2^w) : (readFrame d 62 63 f).fixedSafe w pub z := by
  simp (config := { decide := true }) [readFrame, Code.block,Code.fixedSafe,Code.fixedEval,
    Code.safeReadOnly,Code.evalNat,addressOpFits]
  omega

set_option maxHeartbeats 4000000 in
/-- Configuration is obtained from the public words without altering memory. -/
theorem setup_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hf : (pub 0).val+56 < 2^w)
    (hz : let l := layout (pub 0).val (readings m); l.labels*l.labels < 2^w) :
    BoundedRun pub macros setup s m setup.slots
      (Ready (layout (pub 0).val (readings m)) ⟨readings m,0,0⟩) := by
  let z := NatState.ofWords s m
  have safe (d : Reg) (f : Word 8) (z' : NatState) (h : f.val ≤ 56) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z' := frame_safe d f _ z' w (by
    change (pub 0).val+f.val < 2^w; omega)
  apply (setup.runFixed pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    constructor
    · rintro ⟨j,hj⟩ hj'
      change j < 18 at hj'
      interval_cases j <;>
        simp (config := { decide := true }) [setup,Code.block,Code.fixedEval,frame_eval,Code.evalNat,
          addressOp,layout,Layout.param,NatState.ofWords,readings]
    · simp (config := { decide := true }) [setup,Code.block,Code.fixedEval,frame_eval,Code.evalNat,
          NatState.ofWords]
  · change setup.fixedSafe w (readings pub) z
    change readings m ((pub 0).val+56)*readings m ((pub 0).val+56) < 2^w at hz
    simp (config := { decide := true }) [setup,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,frame_eval,safe,z,NatState.ofWords,readings]
    exact ⟨fun he => by subst w; simp at hf, by omega, by omega, by omega, by omega, hz⟩

/-- Bound register of the physical pass holds precisely its number of rows. -/
theorem Phase.bound_eq (p : Phase) {l : Layout} {a : Acc} {z : NatState}
    (h : Ready l a z) : z.reg p.boundReg = p.count l := by
  cases p <;> exact h.1 _ (by decide)

/-- One tick for each guard and advance, the row slots, and two ticks at the ends. -/
def Phase.ticks (p : Phase) (l : Layout) := p.count l*(p.row.slots+2)+2

/-- Under natural address and volume bounds, the physical counted pass has exactly
the specified memory and volumes at its last iteration. -/
theorem Phase.scan_runs {w : ℕ} (p : Phase) (l : Layout) (a : Acc) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (h : Ready l a (.ofWords s m)) (fit : ∀ i < p.count l, p.room l w i (p.prefix l a i)) :
    BoundedRun pub macros p.scan s m (p.ticks l) (Ready l (p.prefix l a (p.count l))) := by
  let P (i : ℕ) (z : NatState) := Ready l (p.prefix l a i) z ∧ z.reg 20 = i
  let body := Code.seq p.row (.binary .add 20 20 1)
  have hr (i : ℕ) (z : NatState) (hp : P i z) :
      z.reg 20 = i ∧ z.reg p.boundReg = p.count l := ⟨hp.2,p.bound_eq hp.1⟩
  have bound : p.count l < 2^w := (p.bound_eq h) ▸ (s p.boundReg).isLt
  have step (i : ℕ) (hi : i < p.count l) (u : Bank w) (mu : Memory w)
      (hu : P i (.ofWords u mu)) : BoundedRun pub macros body u mu (p.row.slots+1) (P (i+1)) := by
    have row := p.row_eval l _ _ (readings pub) i hu.1 hu.2
    let t := p.row.fixedEval (readings pub) (.ofWords u mu)
    change Ready l _ t ∧ t.reg 20 = i at row
    have one : t.reg 1 = 1 := row.1.1 1 (by decide)
    have safe : body.fixedSafe w (readings pub) (.ofWords u mu) :=
      ⟨p.row_safe l w i _ _ _ hu.1 hu.2 (fit i hi), show t.reg 20+t.reg 1 < 2^w by rw [row.2,one]; omega⟩
    apply (body.runFixed pub macros u mu safe).mono le_rfl
    rintro y rfl
    refine ⟨⟨?_,?_,?_,row.1.2.2.2⟩,?_⟩
    · intro j hj
      exact (Function.update_of_ne (show j ≠ (20:Reg) by intro eq; subst j; exact (by decide : ¬ (20 : Reg).val < 18) hj) ..).trans (row.1.1 j hj)
    · exact row.1.2.1
    · exact row.1.2.2.1
    · change (Function.update t.reg 20 (t.reg 20+t.reg 1)) 20 = _
      simp [row.2,one]
  have init := (Code.constant 20 0).runFixed pub macros s m (by
    change (0 : Word 8).val < 2^w; simp)
  have run := init.seq (b := .whileLt 20 p.boundReg body)
    (t := (p.count l-0)*((p.row.slots+1)+1)+1) (Q := P (p.count l)) (fun u mu hu =>
      run_counted_loop pub macros 20 p.boundReg body _ _ P hr step 0 (Nat.zero_le _) u mu (by
        rw [hu]
        refine ⟨⟨?_,?_,?_,h.2.2.2⟩,?_⟩
        · intro j hj
          exact (Function.update_of_ne (show j ≠ (20:Reg) by intro eq; subst j; exact (by decide : ¬ (20 : Reg).val < 18) hj) ..).trans (h.1 j hj)
        · exact h.2.1
        · exact h.2.2.1
        · rfl))
  exact run.mono (by unfold Phase.ticks; change 1+_ ≤ _; simp only [Nat.sub_zero, Nat.add_assoc, show 1 + 1 = (2 : ℕ) by decide]; omega) fun _ hp => hp.1

/-- Concrete address and cumulative width conditions in all five passes. -/
def room (l : Layout) (w : ℕ) (m : ℕ → ℕ) : Prop :=
  let a : Acc := ⟨m,0,0⟩
  let b := Phase.clear.prefix l a l.cells
  let c := Phase.cable.prefix l b l.cableCount
  let d := Phase.delivery.prefix l c l.deliveryCount
  let e := Phase.cableBins.prefix l d (l.labels*l.labels)
  (∀ i < l.cells, Phase.clear.room l w i (Phase.prefix .clear l a i)) ∧
    (∀ i < l.cableCount, Phase.cable.room l w i (Phase.prefix .cable l b i)) ∧
    (∀ i < l.deliveryCount, Phase.delivery.room l w i (Phase.prefix .delivery l c i)) ∧
    (∀ i < l.labels*l.labels, Phase.cableBins.room l w i (Phase.prefix .cableBins l d i)) ∧
    (∀ i < l.labels, Phase.dataBins.room l w i (Phase.prefix .dataBins l e i))

/-- The complete native initialization takes linear time in the descriptors, cells
and mean bins, regardless of the bit width represented by any one descriptor. -/
theorem program_runs {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    let l := layout (pub 0).val (readings m)
    (pub 0).val+56 < 2^w → l.labels*l.labels < 2^w → room l w (readings m) →
    BoundedRun pub macros program s m
      (setup.slots + (Phase.clear.ticks l + (Phase.cable.ticks l + (Phase.delivery.ticks l +
        (Phase.cableBins.ticks l + Phase.dataBins.ticks l)))))
      (Ready l (image l (readings m))) := by
  intro l hf hz fit
  obtain ⟨h0,h1,h2,h3,h4⟩ := fit
  exact (setup_runs pub macros s m hf hz).seq fun u mu hu =>
    (Phase.clear.scan_runs l _ pub macros u mu hu h0).seq fun v mv hv =>
    (Phase.cable.scan_runs l _ pub macros v mv hv h1).seq fun t mt ht =>
    (Phase.delivery.scan_runs l _ pub macros t mt ht h2).seq fun z mz hh =>
    (Phase.cableBins.scan_runs l _ pub macros z mz hh h3).seq fun k mk hk =>
    Phase.dataBins.scan_runs l _ pub macros k mk hk h4

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
