import OAI.Computability.BorderVNP.DiagonalTallyRAMEvaluation

/-! # Installing count-dependent tally pointers by native word arithmetic -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- The runtime count in slot 35 comes from the current operand schedule. All five
derived pointer and width fields are calculated and stored after that count is available. -/
def allocateTallies : Code := .block [
  readFrame 48 60 61 34,readFrame 49 60 61 35,readFrame 50 60 61 33,
  readFrame 51 60 61 38,readFrame 52 60 61 101,.constant 53 1,
  .binary .add 54 49 49,.binary .add 54 48 54,.binary .add 55 54 50,
  .binary .mul 56 51 50,.binary .add 56 55 56,.binary .add 56 56 50,
  .binary .add 57 56 50,.binary .add 57 57 53,
  writeFrame 54 60 61 32,writeFrame 55 60 61 37,writeFrame 56 60 61 41,
  writeFrame 57 60 61 42,writeFrame 52 60 61 43]

/-- Initial scalar words supplied by the earlier packet, cell, and broadcast phases. -/
def Arena.seed {w : ℕ} (a : Arena) (pub : Arg → Word w) (m : Memory w) (p : ℕ) : Prop :=
  let d := (pub 0).val
  (m (d+33)).val=a.dim ∧ (m (d+34)).val=a.fresh ∧ (m (d+35)).val=a.count ∧
    (m (d+36)).val=a.raw ∧ (m (d+38)).val=a.teams ∧ (m (d+39)).val=a.team ∧
    (m (d+40)).val=a.width ∧ (m (d+44)).val=p ∧ (m (d+101)).val=w

/-- The five shared-memory updates performed by the allocator. -/
def Arena.installed (a : Arena) (w d : ℕ) (m : ℕ → ℕ) : ℕ → ℕ :=
  let m₁ := Function.update m (d+32) a.frame.localBase
  let m₂ := Function.update m₁ (d+37) a.frame.claims
  let m₃ := Function.update m₂ (d+41) a.frame.totals
  let m₄ := Function.update m₃ (d+42) (a.bitFrame w).dst
  Function.update m₄ (d+43) w

/-- Every source outside the tally pointer slots survives installation. -/
theorem Arena.installed_outside (a : Arena) (w d : ℕ) (m : ℕ → ℕ) (q : ℕ)
    (hq : q≠d+32 ∧ q≠d+37 ∧ q≠d+41 ∧ q≠d+42 ∧ q≠d+43) :
    a.installed w d m q=m q := by
  simp [Arena.installed,Function.update_of_ne,hq]

variable {w : ℕ}

set_option maxRecDepth 6000 in
/-- Genuine fixed table execution writes the current count-dependent arena allocation,
including the final Fourier bit-buffer address and the actual machine word width. -/
theorem allocateTallies_runs (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (p : ℕ) (hseed : a.seed pub m p)
    (fit : a.Fits w (pub 0).val) (hdir : (pub 0).val+101<2^w) :
    ∃ es t m', Runs pub mac allocateTallies s m es t m' ∧ traceCost es ≤ allocateTallies.slots ∧
      readings m' = a.installed w (pub 0).val (readings m) ∧
      a.frame.resident pub m' ∧ serializeFrame pub m' (a.bitFrame w) a.dim ∧
      (m' ((pub 0).val+44)).val=p := by
  obtain ⟨hd,hfresh,he,hraw,hR,hi,hb,hp,hw⟩ := hseed
  let z := NatState.ofWords s m
  have room := fit.room
  simp only [Arena.bitFrame,Arena.frame] at room
  have hw' : w ≠ 0 := by rintro rfl; simp at hdir
  have safe : allocateTallies.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [allocateTallies,readFrame,writeFrame,Code.block,Code.fixedSafe,
      Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,Function.update,
      z,NatState.ofWords,readings,hd,hfresh,he,hR,hw']
    omega
  obtain ⟨es,t,mt,r,hc,eq⟩ := allocateTallies.runFixed pub mac s m safe
  have heq := congrArg NatState.mem eq
  have himage : readings mt = a.installed w (pub 0).val (readings m) := by
    simpa (config := {decide := true}) [Arena.installed,Arena.bitFrame,Arena.frame,
      allocateTallies,readFrame,writeFrame,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update,
      NatState.ofWords,readings,hd,hfresh,he,hR,hw,two_mul] using heq
  have lookup (k : ℕ) : (mt ((pub 0).val+k)).val = a.installed w (pub 0).val (readings m) ((pub 0).val+k) :=
    congrFun himage _
  refine ⟨es,t,mt,r,hc,himage,?_,?_,?_⟩
  all_goals
    simp (config := {decide := true}) [Frame.resident,serializeFrame,lookup,Arena.installed,
      Arena.bitFrame,Arena.frame,Function.update,readings,hd,hfresh,he,hraw,hR,hi,hb,hp]

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
