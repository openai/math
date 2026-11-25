import OAI.Computability.BorderVNP.CubeGroupWeightRead

/-! # Counted native loops constructing the joint group weights -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Initialize one word of the histogram. -/
def initWeight : Code := .block [.binary .add 27 8 20,.store 27 13]

/-- Scale the read width by a million and add it to its symbol's physical word. -/
def addWeight : Code := .block [.binary .mul 26 2 26,.binary .add 27 8 21,
  .load 28 27,.binary .add 28 28 26,.store 27 28]

/-- One output update and cursor advance in a public pass. -/
def Phase.body (p : Phase) : Code := .seq (if p = .init then initWeight else p.readRow.seq addWeight)
    (.binary .add 20 20 1)

/-- Register containing the actual length of a pass. -/
def Phase.boundReg : Phase → Reg | .init => 3 | .shared => 14 | .data => 9

/-- Native scan of a single input interval. -/
def Phase.scan (p : Phase) : Code := .seq (.copy 20 0) (.whileLt 20 p.boundReg p.body)

/-- Exact instruction allowance including both loop boundary guards. -/
def Phase.ticks (p : Phase) (l : Layout) := p.count l*(p.body.slots+1)+2

/-- The three pass loops read the shape registers left by the setup. -/
theorem Phase.bound {l : Layout} {z : NatState} (p : Phase) (h : l.Ready z) :
    z.reg p.boundReg = p.count l := by
  cases p <;> exact h _ (by decide)

private theorem update_run {p : Phase} {w : ℕ} (pub : Arg → ℕ) (l : Layout)
    (orig : ℕ → ℕ) (z : NatState) (i : ℕ) (hi : i < p.count l)
    (fit : l.Fits w orig) (ready : l.Ready z) (im : Image p l orig z.mem i) (hc : z.reg 20 = i) :
    let c := if p = .init then initWeight else p.readRow.seq addWeight
    c.fixedSafe w pub z ∧ (c.fixedEval pub z).mem = p.step l orig z.mem i ∧
      (c.fixedEval pub z).reg 20 = i ∧ l.Ready (c.fixedEval pub z) := by
  have r8 : z.reg 8 = l.weights := ready 8 (by decide)
  by_cases hp : p = .init
  · subst p
    have r13 : z.reg 13 = l.raw := ready 13 (by decide)
    have hw := fit.weights i hi
    refine ⟨?_,?_,?_,fun j hj => (initWeight.fixedEval_protected _ _ (by decide) j hj).trans (ready j hj)⟩ <;>
      simp (config := {decide := true}) [initWeight,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.evalNat,Code.safeReadOnly,addressOp,addressOpFits,r8,r13,hc,hw,Phase.step,Phase.target]
  · rw [ite_eq_right hp]
    obtain ⟨safe,target,delta,mem⟩ := p.readRow_sound hp pub l orig z i hi fit ready im hc
    let mid := p.readRow.fixedEval pub z
    have kept (a : Reg) (ha : a.val < 21) : mid.reg a = z.reg a :=
      p.readRow.fixedEval_protected _ z (by cases p <;> decide) a ha
    have r2 : mid.reg 2 = 1000000 := (kept 2 (by decide)).trans (ready 2 (by decide))
    have r8' : mid.reg 8 = l.weights := (kept 8 (by decide)).trans r8
    have r20 : mid.reg 20 = i := (kept 20 (by decide)).trans hc
    change mid.reg 21 = p.target l orig i at target
    change 1000000*mid.reg 26 = p.delta l orig i at delta
    change mid.mem = z.mem at mem
    have ht := p.target_lt (orig := orig) fit.positive hi
    have haddr := fit.weights _ ht
    have inc := im.incrementFits fit hp hi
    have hdelta : p.delta l orig i < 2^w := by omega
    change (_ ∧ addWeight.fixedSafe w pub mid) ∧ (addWeight.fixedEval pub mid).mem = _ ∧
      (addWeight.fixedEval pub mid).reg 20 = _ ∧ l.Ready (addWeight.fixedEval pub mid)
    refine ⟨⟨safe,?_⟩,?_,?_,fun j hj =>
      (addWeight.fixedEval_protected _ mid (by decide) j hj).trans ((kept j (by omega)).trans (ready j hj))⟩ <;>
      simp (config := {decide := true}) [addWeight,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,Phase.step,hp,r8',r20,r2,
        target,delta,mem,hdelta,haddr,inc]

/-- Execute an entire real histogram pass with its physical loop counter and bound. -/
theorem Phase.run_scan {w : ℕ} (p : Phase) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (orig : ℕ → ℕ) (s : Bank w) (m : Memory w) (fit : l.Fits w orig)
    (ready : l.Ready (.ofWords s m)) (init : Image p l orig (readings m) 0) :
    BoundedRun pub macros p.scan s m (p.ticks l)
      (fun z => l.Ready z ∧ Image p l orig z.mem (p.count l)) := by
  let P (i : ℕ) (z : NatState) := l.Ready z ∧ z.reg 20 = i ∧ Image p l orig z.mem i
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 20 = i ∧ z.reg p.boundReg = p.count l :=
    ⟨h.2.1,p.bound h.1⟩
  have step (i : ℕ) (hi : i < p.count l) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros p.body u mu p.body.slots (P (i+1)) := by
    let z := NatState.ofWords u mu
    let c := if p = .init then initWeight else p.readRow.seq addWeight
    let mid := c.fixedEval (readings pub) z
    obtain ⟨safe,mem,r20,hr⟩ := update_run (readings pub) l orig z i hi fit h.1 h.2.2 h.2.1
    change mid.reg 20 = i at r20
    have r1 : mid.reg 1 = 1 := hr 1 (by decide)
    have inc : i+1 < 2^w := Nat.lt_of_le_of_lt hi (p.bound h.1 ▸ (u p.boundReg).isLt)
    have safe' : p.body.fixedSafe w (readings pub) z :=
      ⟨safe,show mid.reg 20 + mid.reg 1 < 2^w by rwa [r20,r1]⟩
    apply (p.body.runFixed pub macros u mu safe').mono le_rfl
    rintro y rfl
    let c' := Code.binary .add 20 20 1
    change P (i+1) (c'.fixedEval (readings pub) mid)
    refine ⟨fun j hj => (c'.fixedEval_protected _ mid (by decide) j hj).trans (hr j hj), ?_, ?_⟩
    · simp [c',Code.fixedEval,Code.evalNat,addressOp,r20,r1]
    · change Image p l orig mid.mem (i+1)
      rw [mem]
      exact h.2.2.advance fit.positive hi
  have run := ((Code.copy 20 0).runFixed pub macros s m trivial).seq
    (b := .whileLt 20 p.boundReg p.body) (t := (p.count l-0)*(p.body.slots+1)+1) (Q := P (p.count l))
    (fun u mu hu => run_counted_loop pub macros 20 p.boundReg p.body (p.count l) p.body.slots P regs
      step 0 (by omega) u mu (by
        rw [hu]
        refine ⟨fun j hj => (Code.fixedEval_protected _ _ _ (by decide) j hj).trans (ready j hj),?_,init⟩
        simpa [Code.fixedEval,Code.evalNat,Layout.param] using ready 0 (by decide)))
  exact run.mono (by
    change 1+((p.count l-0)*(p.body.slots+1)+1) ≤ p.count l*(p.body.slots+1)+2
    rw [Nat.sub_zero]; omega) fun _ h => ⟨h.1,h.2.2⟩

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
