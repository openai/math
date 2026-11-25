import OAI.Computability.BorderVNP.PrivatePlacementImage
import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # Native execution and cost of the original-site placement pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.PrivatePlacement

open VPVNP.BurstRAM

private def ready (l : Layout) (z : NatState) : Prop :=
  z.reg 1 = 1 ∧ z.reg 2 = 2 ∧ z.reg 3 = l.raw ∧ z.reg 4 = l.entries ∧ z.reg 5 = l.desc ∧
    z.reg 6 = l.supplied ∧ z.reg 7 = l.scratch ∧ z.reg 9 = l.gap

private def state (l : Layout) (before : ℕ → ℕ) (i : ℕ) (z : NatState) : Prop :=
  ready l z ∧ z.reg 10 = i ∧ l.Image before i z.mem

set_option maxHeartbeats 1200000 in
private theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (frame : (pub 0).val = l.frame) (h : l.Fields (readings m))
    (zero : ∀ c < l.cells, readings m (l.scratch+c) = 0) :
    BoundedRun pub macros setup s m setup.slots (state l (readings m) 0) := by
  have hp : readings pub 0 = l.frame := frame
  have read (d : Reg) (f : Word 8) (z : NatState) (small : f.val ≤ 92) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by rw [hp]; have := fit.frame; omega)
  obtain ⟨⟨hraw,hn,hd⟩,⟨hinc,hc,hm⟩,hgap⟩ := h
  have hcap := fit.base
  dsimp only [Layout.scratch,Layout.supplied] at hcap
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,readFrame_fixedEval,NatState.ofWords,hp,addressOpFits,addressOp,hinc,hc,hm,
      read _ _ _ (by decide : (64 : Word 8).val ≤ 92),read _ _ _ (by decide : (66 : Word 8).val ≤ 92),
      read _ _ _ (by decide : (69 : Word 8).val ≤ 92),read _ _ _ (by decide : (87 : Word 8).val ≤ 92),
      read _ _ _ (by decide : (92 : Word 8).val ≤ 92),
      read _ _ _ (by decide : (11 : Word 8).val ≤ 92),read _ _ _ (by decide : (7 : Word 8).val ≤ 92)]
    have := fit.control
    have := fit.frame
    have hw : w ≠ 0 := by rintro rfl; simp at this
    omega
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro z rfl
  have img : l.Image (readings m) 0 (readings m) := ⟨by simpa [prefixCounts] using zero,by simp,by simp⟩
  simpa (config := {decide := true}) [state,ready,setup,Code.block,Code.fixedEval,Code.evalNat,
    readFrame_fixedEval,NatState.ofWords,hp,addressOp,hraw,hn,hd,hinc,hc,hm,hgap,Layout.scratch,Layout.supplied] using img

set_option maxHeartbeats 1200000 in
private theorem run_step {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.entries)
    (s : Bank w) (m : Memory w) (hs : state l before i (.ofWords s m)) :
    BoundedRun pub macros step s m step.slots (state l before (i+1)) := by
  let z := NatState.ofWords s m
  change state l before i z at hs
  obtain ⟨hr,idx,img⟩ := hs
  obtain ⟨one,two,raw,entries,desc,supplied,scratch,gap⟩ := hr
  let c := l.owner before i
  let n := prefixCounts (l.owner before) l.desc i c
  have owner : z.mem (l.raw+2*i) = c := img.owner_eq fit hi
  have hc : c < l.cells := fit.owners i hi
  have total : z.mem (l.supplied+c) = before (l.supplied+c) := img.supplied_eq fit hi.le hc
  have seen : z.mem (l.scratch+c) = n := img.counters c hc
  obtain ⟨slotFit,nextFit⟩ := fit.values i hi
  change before (l.supplied+c)+l.gap+n < 2^w at slotFit
  change n+l.desc < 2^w at nextFit
  have rawFit := fit.raw
  have countsFit := fit.counts
  have totalFit : l.supplied+c < 2^w := by dsimp only [Layout.scratch] at countsFit; omega
  have safe : step.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [step,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,one,two,raw,desc,supplied,scratch,gap,idx,owner,total,seen]
    omega
  apply (step.runFixed pub macros s m safe).mono le_rfl
  rintro u rfl
  have stable (r : Reg) (h : r.val < 10) := step.fixedEval_protected (readings pub) z (by decide) r h
  refine ⟨?_,?_,?_⟩
  · exact ⟨(stable 1 (by decide)).trans one,(stable 2 (by decide)).trans two,
      (stable 3 (by decide)).trans raw,(stable 4 (by decide)).trans entries,
      (stable 5 (by decide)).trans desc,(stable 6 (by decide)).trans supplied,
      (stable 7 (by decide)).trans scratch,(stable 9 (by decide)).trans gap⟩
  · change (step.fixedEval (readings pub) z).reg 10 = i+1
    simp (config := {decide := true}) [step,Code.block,Code.fixedEval,Code.evalNat,addressOp,one,idx]
  · change l.Image before (i+1) (step.fixedEval (readings pub) z).mem
    simpa (config := {decide := true}) [step,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      one,two,raw,desc,supplied,scratch,gap,idx,owner,total,seen] using img.step fit hi

/-- Starting at an arbitrary register bank with the geometry publisher's zero counters,
the actual pass writes the complete ordered private placement and returns within a
fixed setup charge plus fifteen ticks per original site and the exit guard. -/
theorem run_program {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w (readings m))
    (frame : (pub 0).val = l.frame) (fields : l.Fields (readings m))
    (zero : ∀ c < l.cells, readings m (l.scratch+c) = 0) :
    BoundedRun pub macros program s m (setup.slots + (l.entries*15+1))
      (fun z => l.Image (readings m) l.entries z.mem) := by
  apply (run_setup pub macros l s m fit frame fields zero).seq
  intro u mu init
  apply (run_counted_loop pub macros 10 4 step l.entries step.slots (state l (readings m))
    (fun _ _ h => ⟨h.2.1,h.1.2.2.2.1⟩) (fun _ hi b v h => run_step pub macros l _ fit hi b v h)
    0 (Nat.zero_le _) u mu init).mono
  · simp only [Nat.sub_zero]; exact le_rfl
  · exact fun _ h => h.2.2

end RoutingISA.PrivatePlacement

end BorderVNP
end Computability
end OAI
