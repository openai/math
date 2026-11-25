import OAI.Computability.BorderVNP.CubeTeamOwnedGroups
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost

/-! # Publishing the owned vertex count from the actual record cursor

The native directory uses three words for each vertex. The start fragment
reads its base from frame field 78. The finish fragment measures the distance
from that base and publishes its quotient by three in field 46. Both routines
run with a unique unsigned trace of fixed length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.Owned VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

/-- Store the directory count in its public frame word. -/
def publishVertexCount {w : ℕ} (m : Memory w) (frame count : ℕ) : Memory w :=
  Function.update m (frame+46) (Fin.ofNat (2^w) count)

/-- The directory count can be read back at the actual frame address. -/
theorem publishVertexCount_here {w : ℕ} (m : Memory w) (frame count : ℕ) (fit : count < 2^w) :
    readings (publishVertexCount m frame count) (frame+46) = count := by
  simp [publishVertexCount,readings,Fin.ofNat,Nat.mod_eq_of_lt fit]

/-- Every word outside the directory count is preserved. -/
theorem publishVertexCount_other {w : ℕ} (m : Memory w) (frame count x : ℕ) (hx : x ≠ frame+46) :
    publishVertexCount m frame count x = m x := Function.update_of_ne hx ..

/-- The directory startup has four real opcode slots. -/
theorem startVertices_slots : startVertices.slots = 4 := rfl

/-- The two frame accesses and three arithmetic instructions occupy eleven slots. -/
theorem finishVertices_slots : finishVertices.slots = 11 := rfl

variable {w : ℕ}

private def straight : Code → Bool
  | .seq a b => straight a && straight b
  | c => c.isAtom

private theorem straight_length {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub mac c s m es t mt)
    (h : straight c = true) : es.length = c.slots := by
  induction run with
  | @atom c _ _ _ _ _ _ hc _ _ => cases c <;> simp_all [Code.isAtom,Code.slots]
  | seq _ _ ih jh =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    rw [List.length_append,Code.slots,ih a,jh b]
  | ifEq | ifLt | choose | whileDone | whileStep => contradiction

private theorem exactReturn {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} {k : ℕ} {P : Bank w → Memory w → Prop}
    (r : TraceRun pub mac c s m [] k P) (run : Runs pub mac c s m es t mt)
    (det : c.deterministic = true) (line : straight c = true) :
    TraceOK es [] c.slots ∧ traceCost es = c.slots ∧ P t mt := by
  obtain ⟨_,_,_,first,good,_,post⟩ := r
  obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic det run
  have size := straight_length first line
  exact ⟨size ▸ good,(first.deterministic_cost det).trans size,post⟩

/-- Start the owned-vertex directory by reading field 78 into the word cursor. -/
theorem startVertices_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame base : ℕ) (hf : readings pub 0 = frame)
    (fit : frame+78 < 2^w) (ptr : readings m (frame+78) = base) :
    TraceRun pub mac startVertices s m [] 4 (fun t mt => readings t 7 = base ∧ mt = m) := by
  have safe := readFrame_fixedSafe 7 78 (readings pub) (.ofWords s m) w (by simpa [hf] using fit)
  apply (traceRun_unsigned (startVertices.runFixed pub mac s m safe) (by decide)).mono le_rfl
  intro t mt eqn
  have value := congrArg (fun z : NatState => z.reg 7) eqn
  have memory := congrArg NatState.mem eqn
  simp (config := {decide := true}) [startVertices,readFrame_fixedEval,NatState.ofWords,hf,ptr] at value memory
  exact ⟨value,funext fun j => Fin.ext (congrFun memory j)⟩

/-- Every actual return of the start routine has exactly four ordinary ticks,
no choice bits, and the register and memory described by the directory frame. -/
theorem startVertices_return {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} {frame base : ℕ} {es t mt}
    (hf : readings pub 0 = frame) (fit : frame+78 < 2^w) (ptr : readings m (frame+78) = base)
    (run : Runs pub mac startVertices s m es t mt) :
    TraceOK es [] 4 ∧ traceCost es = 4 ∧ readings t 7 = base ∧ mt = m :=
  exactReturn (startVertices_run pub mac s m frame base hf fit ptr) run (by decide) (by decide)

private theorem finish_raw (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame base : ℕ) (hf : readings pub 0 = frame)
    (fit : frame+78 < 2^w) (ptr : readings m (frame+78) = base) (hlo : base ≤ readings s 7) :
    TraceRun pub mac finishVertices s m [] 11 (fun t mt => readings t 7 = readings s 7 ∧
      mt = publishVertexCount m frame ((readings s 7-base)/3)) := by
  let n := (readings s 7-base)/3
  have nf : n < 2^w := (Nat.div_le_self ..).trans_lt ((Nat.sub_le ..).trans_lt (s 7).isLt)
  have val : (Fin.ofNat (2^w) n).val = n := Nat.mod_eq_of_lt nf
  have safeR := fun z => readFrame_fixedSafe 54 78 (readings pub) z w (by simpa [hf] using fit)
  have cap46 : frame+46 < 2^w := by omega
  have c3 : 3 < 2^w := by omega
  have safe : finishVertices.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [finishVertices,Code.block,Code.fixedSafe,Code.fixedEval,
      readFrame_fixedEval,writeFrame,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,
      NatState.ofWords,hf,ptr,safeR,c3,hlo,cap46]
    omega
  apply (traceRun_unsigned (finishVertices.runFixed pub mac s m safe) (by decide)).mono le_rfl
  intro t mt eqn
  have cursor := congrArg (fun z : NatState => z.reg 7) eqn
  have memory := congrArg NatState.mem eqn
  simp (config := {decide := true}) [finishVertices,Code.block,Code.fixedEval,readFrame_fixedEval,
    writeFrame,Code.evalNat,addressOp,NatState.ofWords,hf,ptr] at cursor memory
  refine ⟨cursor,funext fun j => Fin.ext ?_⟩
  have atJ := congrFun memory j
  by_cases same : j = frame+46
  · subst j
    change (mt (frame+46)).val = (publishVertexCount m frame n (frame+46)).val
    rw [publishVertexCount,Function.update_self,val]
    simpa [n,readings] using atJ
  · simpa [readings,publishVertexCount,same] using atJ

/-- An exact number of appended vertex triples is recorded in field 46. -/
theorem finishVertices_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame base count : ℕ) (hf : readings pub 0 = frame)
    (fit : frame+78 < 2^w) (ptr : readings m (frame+78) = base)
    (cursor : readings s 7 = base+3*count) :
    TraceRun pub mac finishVertices s m [] 11 (fun t mt =>
      readings t 7 = readings s 7 ∧ mt = publishVertexCount m frame count) := by
  have lo : base ≤ readings s 7 := by omega
  have quotient : (readings s 7-base)/3 = count := by omega
  simpa only [quotient] using finish_raw pub mac s m frame base hf fit ptr lo

/-- On a complete triple boundary the published word reconstructs the final cursor,
including an empty directory. Only the count word changes. -/
theorem finish_count (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame base : ℕ) (hf : readings pub 0 = frame)
    (fit : frame+78 < 2^w) (ptr : readings m (frame+78) = base)
    (hlo : base ≤ readings s 7) (aligned : 3 ∣ readings s 7-base) :
    TraceRun pub mac finishVertices s m [] 11 (fun t mt =>
      readings t 7 = base+3*readings mt (frame+46) ∧
      mt = publishVertexCount m frame ((readings s 7-base)/3)) := by
  obtain ⟨n,hn⟩ := aligned
  have cur : readings s 7 = base+3*n := by omega
  have q : (readings s 7-base)/3 = n := by omega
  have nf : n < 2^w := by have := (s 7).isLt; change readings s 7 < 2^w at this; omega
  apply (finishVertices_run pub mac s m frame base n hf fit ptr cur).mono le_rfl
  rintro t mt ⟨h, rfl⟩
  exact ⟨by rw [publishVertexCount_here m frame n nf,h,cur], by rw [q]⟩

/-- Invert any returning finish routine on a directory of exactly `count` triples. -/
theorem finishVertices_return {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} {frame base count : ℕ} {es t mt}
    (hf : readings pub 0 = frame) (fit : frame+78 < 2^w) (ptr : readings m (frame+78) = base)
    (cursor : readings s 7 = base+3*count) (run : Runs pub mac finishVertices s m es t mt) :
    TraceOK es [] 11 ∧ traceCost es = 11 ∧ readings t 7 = readings s 7 ∧
      mt = publishVertexCount m frame count :=
  exactReturn (finishVertices_run pub mac s m frame base count hf fit ptr cursor) run (by decide) (by decide)

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
