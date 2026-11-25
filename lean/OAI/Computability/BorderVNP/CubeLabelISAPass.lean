import OAI.Computability.BorderVNP.CubeLabelISAPassImage
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Scoring and committing a label by traversing the physical bin directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- After a bin query, consume its old and new contributions in registers 26 and 27
and the cache address in register 31. Register 9 is scratch and 37 is the cursor. -/
def passUpdate : Bool → Code
  | false => .block [.load 9 31, .binary .mul 9 9 27, .binary .add 16 16 9,
      .binary .add 37 37 20]
  | true => .block [.load 9 31, .binary .sub 9 9 26, .binary .add 9 9 27,
      .store 31 9, .binary .add 37 37 20]

/-- Reset the bin ordinal and traverse exactly the directory size in register 39. -/
def pass (commit : Bool) (bin : Code) : Code := .seq (.constant 37 0)
  (.whileLt 37 39 (.seq bin (passUpdate commit)))

/-- Prefix memory is the input cache on a trial and the updated cache on a commit. -/
def PassBins.memory (b : PassBins) (commit : Bool) (m : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  if commit then b.image m i else m

/-- Register 16 accumulates the trial sum and is preserved during commit. -/
def PassBins.total (b : PassBins) (commit : Bool) (m : ℕ → ℕ) (score i : ℕ) : ℕ :=
  if commit then score else score + b.score m i

/-- Arithmetic requirements of the cache-update instructions at the current bin. -/
def PassBins.fits (b : PassBins) (commit : Bool) (w : ℕ) (m : ℕ → ℕ) (score i : ℕ) : Prop :=
  if commit then
    b.before i ≤ b.image m i (b.addr i) ∧
      b.image m i (b.addr i) - b.before i + b.after i < 2^w
  else score + b.score m i + m (b.addr i) * b.after i < 2^w

private theorem update_result (b : PassBins) (commit : Bool) (env : Arg → ℕ)
    (m : ℕ → ℕ) (z : NatState) (w score i : ℕ)
    (hm : z.mem = b.memory commit m i) (hs : z.reg 16 = b.total commit m score i)
    (hi : z.reg 37 = i) (ho : z.reg 20 = 1) (ha : z.reg 31 = b.addr i)
    (hb : z.reg 26 = b.before i) (hn : z.reg 27 = b.after i)
    (fit : b.fits commit w m score i) (inc : i+1 < 2^w) :
    (passUpdate commit).fixedSafe w env z ∧
    let out := (passUpdate commit).fixedEval env z
    out.reg 37 = i+1 ∧ out.reg 16 = b.total commit m score (i+1) ∧
      out.mem = b.memory commit m (i+1) := by
  cases commit <;> simp only [PassBins.fits, PassBins.total, PassBins.memory,
    Bool.false_eq_true, ite_false, ite_true] at hm hs fit ⊢
  · have prod : m (b.addr i) * b.after i < 2^w := by omega
    simp (config := {decide := true}) [passUpdate, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, hm,hs,hi,ho,ha,hn,fit,inc,
      prod,PassBins.score_succ,← Nat.add_assoc]
  · simp (config := {decide := true}) [passUpdate, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, hm,hs,hi,ho,ha,hn,hb,
      fit.1,fit.2,inc,PassBins.image]

private theorem pass_kept (commit : Bool) (bin : Code) (k : Reg) (keep : (pass commit bin).keeps k) :
    k ≠ 37 ∧ bin.keeps k = true ∧ (passUpdate commit).keeps k = true := by
  simpa [pass,Code.keeps] using keep

/-- Register 20 supplies one and register 39 supplies the directory length. -/
theorem pass_control_keeps (commit : Bool) (bin : Code) (k : Reg)
    (which : k = 20 ∨ k = 39) (hb : bin.keeps k = true) : (pass commit bin).keeps k = true := by
  rcases which with rfl | rfl <;> cases commit <;> simp (config := {decide := true})
    [pass,passUpdate,Code.block,Code.keeps,hb]

/-- Execute the physical bin pass from a word bank. The bin evaluator is invoked only
with the actual memory image of the previously visited ordinals. -/
theorem pass_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (commit : Bool) (bin : Code) (b : PassBins) (s : Bank w) (m : Memory w)
    (G cost : ℕ) (bound : (s 39).val = G) (one : (s 20).val = 1)
    (control : ∀ k ∈ ([16,20,37,39] : List Reg), bin.keeps k = true)
    (kernel : ∀ i < G, ∀ (t : Bank w) (mt : Memory w),
      (∀ k, (pass commit bin).keeps k = true → t k = s k) →
      (t 37).val = i → readings mt = b.memory commit (readings m) i →
      ∃ es u, Runs pub macros bin t mt es u mt ∧ traceCost es ≤ cost ∧
        (u 26).val = b.before i ∧ (u 27).val = b.after i ∧ (u 31).val = b.addr i)
    (fit : ∀ i < G, b.fits commit w (readings m) (s 16).val i) :
    ∃ es t mt, Runs pub macros (pass commit bin) s m es t mt ∧
      traceCost es ≤ G*(cost+6)+2 ∧ (t 37).val = G ∧
      (t 16).val = b.total commit (readings m) (s 16).val G ∧
      readings mt = b.memory commit (readings m) G := by
  let P i (z : NatState) := (∀ k, (pass commit bin).keeps k = true → z.reg k = (s k).val) ∧
    z.reg 37 = i ∧ z.reg 16 = b.total commit (readings m) (s 16).val i ∧
    z.mem = b.memory commit (readings m) i
  have regs i z (h : P i z) : z.reg 37 = i ∧ z.reg 39 = G :=
    ⟨h.2.1,(h.1 39 (pass_control_keeps commit bin _ (by simp) (control _ (by decide)))).trans bound⟩
  let body := Code.seq bin (passUpdate commit)
  have step (i : ℕ) (hi : i < G) (t : Bank w) (mt : Memory w) (h : P i (.ofWords t mt)) :
      BoundedRun pub macros body t mt (cost+5) (P (i+1)) := by
    obtain ⟨es,u,ru,cu,ub,un,ua⟩ := kernel i hi t mt (fun k hk => Fin.ext (h.1 k hk)) h.2.1 h.2.2.2
    have kept (k : Reg) (hk : k ∈ ([16,20,37,39] : List Reg)) : u k = t k :=
      ru.keepsReg (control k hk)
    have tOne := (h.1 20 (pass_control_keeps commit bin _ (by simp) (control _ (by decide)))).trans one
    have inc : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt (bound ▸ (s 39).isLt)
    obtain ⟨safe,next⟩ := update_result b commit (readings pub) (readings m) (.ofWords u mt) w (s 16).val i
      h.2.2.2 ((congrArg Fin.val (kept 16 (by decide))).trans h.2.2.1)
      ((congrArg Fin.val (kept 37 (by decide))).trans h.2.1)
      ((congrArg Fin.val (kept 20 (by decide))).trans tOne) ua ub un (fit i hi) inc
    obtain ⟨fs,v,mv,rv,cv,ev⟩ := (passUpdate commit).runFixed pub macros u mt safe
    have rr : Runs pub macros body t mt (es++fs) v mv := ru.seq rv
    refine ⟨_,v,mv,rr,?_,?_,?_⟩
    · have slots : (passUpdate commit).slots ≤ 5 := by cases commit <;> decide
      exact (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add cu (cv.trans slots))
    · intro k hk
      have keep := pass_kept commit bin k hk
      exact (congrArg Fin.val (rr.keepsReg (Bool.and_eq_true_iff.mpr keep.2))).trans (h.1 k hk)
    · rw [ev]
      exact next
  let init := Function.update s (37 : Reg) (0 : Word w)
  have initRun : Runs pub macros (.constant 37 0) s m [tick w] init m := Runs.localStep m rfl rfl
  have initState : P 0 (.ofWords init m) := by
    refine ⟨fun k hk => congrArg Fin.val (Function.update_of_ne (pass_kept commit bin k hk).1 ..),?_,?_,?_⟩
    · simp [init,NatState.ofWords,readings]
    · cases commit <;> simp (config := {decide := true})
        [init,NatState.ofWords,readings,PassBins.total,PassBins.score]
    · cases commit <;> rfl
  obtain ⟨es,t,mt,run,hc,h⟩ := run_counted_loop pub macros 37 39 body G (cost+5)
    P regs step 0 (Nat.zero_le _) init m initState
  refine ⟨_,t,mt,initRun.seq run,?_,h.2⟩
  change 1 + traceCost es ≤ _
  simp only [Nat.sub_zero] at hc
  change traceCost es ≤ G*(cost+6)+1 at hc
  omega

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
