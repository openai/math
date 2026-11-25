import OAI.Computability.BorderVNP.CubeLabelISAFramePass
import OAI.Computability.BorderVNP.CubeLabelISAProgram
import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # Public frame, score, and reference images for the native label chooser -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM

/-- Load the alphabet, arrays and cell count, and start at cell zero. -/
def setup : Code := .block [
  readFrame 0 62 63 56, readFrame 19 62 63 11, readFrame 21 62 63 48,
  readFrame 28 62 63 49, readFrame 29 62 63 50, readFrame 34 62 63 51,
  readFrame 35 62 63 52, readFrame 36 62 63 53, .constant 1 0, .constant 23 0,
  .constant 20 1, .constant 30 4, .binary .mul 38 0 0, .binary .add 39 38 0]

/-- Score one candidate, including a fresh zero accumulator. -/
def candidate : Code := .seq (.constant 16 0) (pass false binContrib)

/-- Commit the winning candidate by replacing each scaled cache word. -/
def commit : Code := pass true binContrib

/-- Complete finite instruction table after the linked incidence index has been built. -/
def program : Code := .seq setup (assign candidate commit)

/-- The fixed label program contains only ordinary deterministic operations. -/
theorem program_deterministic : program.deterministic = true := by decide

set_option maxHeartbeats 600000 in
/-- Loading the allocated frame preserves shared memory and produces every static
parameter of the chooser. Only the last frame address and the bin count need room. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hf : (pub 0).val + 56 < 2^w)
    (hz : let p := Frame.decode (pub 0).val (readings m); p.Z^2+p.Z < 2^w) :
    let p := Frame.decode (pub 0).val (readings m)
    ∃ tr t, Runs pub macros setup s m tr t m ∧ traceCost tr ≤ setup.slots ∧
      p.loaded (.ofWords t m) ∧ (t 1).val = 0 := by
  intro p
  let z := NatState.ofWords s m
  have fs (d : Reg) (f : Word 8) (z' : NatState) (h : f.val ≤ 56) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z' :=
    readFrame_fixedSafe d f _ _ w (by change (pub 0).val+f.val < _; omega)
  have safe : setup.fixedSafe w (readings pub) z := by
    change (readings m ((pub 0).val+56))^2 + readings m ((pub 0).val+56) < 2^w at hz
    simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,readFrame_fixedEval,fs,z,
      NatState.ofWords,readings,pow_two] at hz ⊢
    have hw : w ≠ 0 := by rintro rfl; simp at hf
    simp_all
    omega
  obtain ⟨tr,t,mt,r,hcost,he⟩ := setup.runFixed pub macros s m safe
  have eqmem : mt = m := funext fun a => Fin.ext (congrFun (congrArg NatState.mem he) a)
  subst mt
  refine ⟨_,t,r,hcost,?_,?_⟩
  · intro k hk
    rw [he]
    simp only [params,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst k <;>
      simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,
        readFrame_fixedEval,Frame.param,Frame.decode,p,addressOp,NatState.ofWords,readings,pow_two]
  · change (NatState.ofWords t m).reg 1 = 0
    rw [he]
    simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,readFrame_fixedEval]

/-- Score computed from the true old means and the new incident contributions. -/
def Frame.score (p : Frame) (c : ℕ) (m : ℕ → ℕ) (rows : List Incident) (v : ℕ) :=
  (p.bins c v m rows).score m (p.Z^2+p.Z)

/-- The first minimizing label in public numeric order. -/
def Frame.winner (p : Frame) (z c : ℕ) (m : ℕ → ℕ) (rows : List Incident) : Fin (z+1) :=
  Cube.firstMinimum (fun v => p.score c m rows v.val)

/-- Full committed mean table before writing the cell label. -/
def Frame.updated (p : Frame) (z c : ℕ) (m : ℕ → ℕ) (rows : List Incident) : ℕ → ℕ :=
  (p.bins c (p.winner z c m rows).val m rows).image m (p.Z^2+p.Z)

/-- The mathematical memory image after the first `c` decisions. The recurrence
takes its minimizer over unbounded natural scores. -/
def Frame.prefix (p : Frame) (z : ℕ) (rows : ℕ → List Incident) (m : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => m
  | c+1 => let t := p.prefix z rows m c
           Function.update (p.updated z c t (rows c)) (p.labels+c) (p.winner z c t (rows c)).val

/-- Conditions on physical addresses and natural arithmetic at the bin probes of a pass. -/
structure PassRoom (p : Frame) (w c v : ℕ) (m : ℕ → ℕ) (rows : List Incident) (change : Bool) : Prop where
  /-- The incidence links are valid and all of their address computations fit. -/
  room : ∀ i < p.Z^2+p.Z, p.room w c v i ((p.bins c v m rows).memory change m i) rows
  /-- Earlier cache writes preserve the row data and labels used by this bin. -/
  same : ∀ i < p.Z^2+p.Z, p.incident c v i ((p.bins c v m rows).memory change m i) rows =
    p.incident c v i m rows
  /-- Each visited bin and the accumulated integer score fit the selected word width. -/
  fit : ∀ i < p.Z^2+p.Z, (p.bins c v m rows).fits change w m 0 i

/-- Native cost of one whole pass excluding the optional score-accumulator reset. -/
def Frame.passTicks (p : Frame) (rows : List Incident) :=
  (p.Z^2+p.Z)*(24*rows.length+18)+2

/-- Static register invariant independent of memory. -/
def Frame.registers {w : ℕ} (p : Frame) (s : Bank w) := ∀ k ∈ params, (s k).val = p.param k.val

/-- Assigning a scratch register preserves the fixed layout parameters. -/
theorem Frame.registers_update {w : ℕ} {p : Frame} {s : Bank w} (h : p.registers s)
    {r : Reg} (off : r ∉ params) (u : Word w) : p.registers (Function.update s r u) := by
  intro k hk
  have ne : k ≠ r := by rintro rfl; exact off hk
  rw [Function.update_of_ne ne]
  exact h k hk

/-- A run that does not overwrite any layout parameter preserves the static frame. -/
theorem Frame.registers_run {w : ℕ} {p : Frame} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m c tr t mt} (h : p.registers s) (r : Runs pub macros c s m tr t mt)
    (kept : ∀ k ∈ params, c.keeps k = true) : p.registers t := by
  intro k hk
  rw [r.keepsReg (kept k hk)]
  exact h k hk

/-- The fitted native trial fragment computes its score from the physical old means
and all incident-after sums, leaving shared memory unchanged. -/
theorem candidate_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (p : Frame) (c v : ℕ) (s : Bank w) (m : Memory w) (rows : List Incident)
    (h : p.registers s) (hc : (s 1).val = c) (hv : (s 2).val = v)
    (room : PassRoom p w c v (readings m) rows false) :
    ∃ tr t, Runs pub macros candidate s m tr t m ∧ traceCost tr ≤ p.passTicks rows+1 ∧
      p.registers t ∧ (t 1).val = c ∧ (t 16).val = p.score c (readings m) rows v := by
  let u := Function.update s 16 (0 : Word w)
  have init : Runs pub macros (.constant 16 0) s m [tick w] u m := Runs.localStep m rfl rfl
  have hu := p.registers_update h (r := 16) (by decide) (0 : Word w)
  have u16 : (u 16).val = 0 := by simp [u]
  obtain ⟨fs,t,mt,run,cost,_,score,mem⟩ := framePass_run pub macros false p c v u m rows hu
    (by simpa (config := {decide := true}) [u] using hc)
    (by simpa (config := {decide := true}) [u] using hv) room.room room.same
    (by simpa only [u16] using room.fit)
  have mt' : mt = m := funext fun j => Fin.ext (congrFun mem j)
  subst mt
  have rr : Runs pub macros candidate s m _ t m := init.seq run
  refine ⟨_,_,rr,?_,p.registers_run h rr (by decide),?_,?_⟩
  · change 1+traceCost fs ≤ _; unfold Frame.passTicks; omega
  · rw [rr.keepsReg (k := 1) (by decide)]; exact hc
  · simpa only [PassBins.total,u16,Frame.score,Bool.false_eq_true,ite_false,Nat.zero_add] using score

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
