import OAI.Computability.BorderVNP.CubeScatterSingletonLoop
import OAI.Computability.BorderVNP.CubeDirectedIntervalInit
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Native scatter from a classified singleton row

The chosen symbol row is diagonal precisely when its singleton bits are
private to one group. Otherwise the shared suffix supplies the bits. A row
contains the runtime block count times the fixed block width, and the native
setup calculates its destination from the two actual label codes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The endpoint label codes occupy registers 24 and 25, and 21 holds the interval length.
The product alphabet and singleton bank are read from their physical frame positions. -/
def startSingle : Code := .block [
  readFrame 55 62 63 56,readFrame 56 62 63 88,.constant 59 1,
  .binary .mul 38 24 55,.binary .add 38 38 25,.binary .mul 38 38 21,
  .binary .add 38 38 56,.binary .add 57 38 21]

/-- Row-major destination of the entire singleton family. -/
def singleBase (bank alphabet len u v : ℕ) := bank+(u*alphabet+v)*len

private theorem frame_safe (d : Reg) (f : Word 8) (pub : Arg → ℕ) (st : NatState)
    (w : ℕ) (hf : pub 0+f.val < 2^w) :
    (readFrame d 62 63 f).fixedSafe w pub st := by
  simp (config := {decide := true}) [readFrame,Code.block,Code.fixedSafe,Code.fixedEval,
    Code.safeReadOnly,Code.evalNat,addressOpFits,hf]
  omega

private theorem frame_eval (d : Reg) (f : Word 8) (pub : Arg → ℕ) (st : NatState) :
    (readFrame d 62 63 f).fixedEval pub st = ⟨Function.update
      (Function.update (Function.update st.reg 63 f.val) 62 (pub 0+f.val)) d
        (st.mem (pub 0+f.val)), st.mem⟩ := by
  simp (config := {decide := true}) [readFrame,Code.block,Code.fixedEval,Code.evalNat,addressOp,
    Function.update_comm (show (62 : Reg) ≠ 63 by decide)]

/-- The concrete frame reads and mixed-radix multiplication produce the exact start/end sentinels. -/
theorem startSingle_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w)
    (bank alphabet len u v : ℕ) (ru : readings r 24 = u) (rv : readings r 25 = v) (rl : readings r 21 = len)
    (alphabetAt : readings m ((pub 0).val+56) = alphabet) (bankAt : readings m ((pub 0).val+88) = bank)
    (frameFit : (pub 0).val+88 < 2^w) (keyFit : u*alphabet+v < 2^w)
    (destFit : singleBase bank alphabet len u v+len < 2^w) :
    ∃ es t, Runs pub mac startSingle r m es t m ∧ traceCost es ≤ startSingle.slots ∧
      t 38 = word w (singleBase bank alphabet len u v) ∧
      t 57 = word w (singleBase bank alphabet len u v+len) ∧ t 59 = 1 ∧
      ∀ j : Reg, j ∉ ([38,55,56,57,59,62,63] : List Reg) → t j = r j := by
  let st := NatState.ofWords r m
  have hz : readings m (readings pub 0 + 56) = alphabet := alphabetAt
  have hb : readings m (readings pub 0 + 88) = bank := bankAt
  have ha (z : NatState) := frame_safe (55 : Reg) (56 : Word 8) (readings pub) z w (by change (pub 0).val+56 < _; omega)
  have ha' (z : NatState) := frame_safe (56 : Reg) (88 : Word 8) (readings pub) z w frameFit
  have hdest : bank+(u*alphabet+v)*len+len < 2^w := destFit
  have safe : startSingle.fixedSafe w (readings pub) st := by
    simp (config := {decide := true}) [startSingle,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.evalNat,Code.safeReadOnly,addressOpFits,addressOp,ha,ha',frame_eval,st,NatState.ofWords,hz,hb,
      ru,rv,rl]
    have small : w ≠ 0 := by rintro rfl; simp at frameFit
    omega
  obtain ⟨es,t,mt,run,cost,post⟩ := startSingle.runFixed pub mac r m safe
  have out : readings mt = readings m := by
    have hm := congrArg NatState.mem post
    simpa (config := {decide := true}) [startSingle,Code.block,Code.fixedEval,frame_eval,NatState.ofWords] using hm
  have eq : mt = m := funext fun j => Fin.ext (congrFun out j)
  subst mt
  have bankRead (j : Reg) := congrArg (fun z : NatState => z.reg j) post
  have read38 : (t 38).val = singleBase bank alphabet len u v := by
    change readings t 38 = _
    have eq := bankRead 38
    simp (config := {decide := true}) [startSingle,Code.block,Code.fixedEval,Code.evalNat,
      frame_eval,addressOp,NatState.ofWords,hz,hb,ru,rv,rl] at eq
    simpa only [singleBase,Nat.add_comm bank] using eq
  have read57 : (t 57).val = singleBase bank alphabet len u v+len := by
    change readings t 57 = _
    have eq := bankRead 57
    simp (config := {decide := true}) [startSingle,Code.block,Code.fixedEval,Code.evalNat,
      frame_eval,addressOp,NatState.ofWords,hz,hb,ru,rv,rl] at eq
    simpa only [singleBase,Nat.add_comm bank] using eq
  have read59 : (t 59).val = 1 := by
    change readings t 59 = 1
    simpa (config := {decide := true}) [startSingle,Code.block,Code.fixedEval,Code.evalNat,frame_eval,NatState.ofWords] using bankRead 59
  refine ⟨es,t,run,cost,Fin.ext (read38.trans (word_val _ _ (by omega)).symm),
    Fin.ext (read57.trans (word_val _ _ destFit).symm),Fin.ext (read59.trans (word_val _ 1 (by omega)).symm),?_⟩
  intro j hj
  simp at hj
  apply Fin.ext
  change readings t j = readings r j
  simpa [startSingle,Code.block,Code.fixedEval,Code.evalNat,frame_eval,Function.update,hj,NatState.ofWords] using bankRead j

/-- The native branch uses one private bit per singleton on a diagonal symbol row and
copies the crossing suffix in the same ordinal order on an off-diagonal row. -/
def singleBody : Code := .ifEq 14 15 (.whileLt 38 57 Mode.privateBit.code) (.whileLt 38 57 Mode.crossing.code)

/-- Scatter one classified singleton family into its actual bank interval. -/
def scatterSingle : Code := .seq startSingle singleBody

/-- Both the forward and reverse descriptions of the singleton family use the
same native chronological trace. The shared interval contributes no private choices. -/
theorem singleBody_iff (len start : ℕ) (r : Bank w) (m : Memory w)
    (one : r 59 = 1) (cur : r 38 = word w start) (stop : r 57 = word w (start+len))
    (fits : start+len < 2^w) {es t mt} :
    Runs pub mac singleBody r m es t mt ↔
      ∃ ds : List Digit, ds.map Digit.mode = List.replicate len
        (if r 14 = r 15 then Mode.privateBit else Mode.crossing) ∧
        es = tick w :: walkTrace ds r m ∧ t = (result ds r m).bank ∧ mt = (result ds r m).mem := by
  by_cases same : r 14 = r 15
  all_goals
    simp only [same,ite_true,ite_false]
    constructor
    · intro run
      cases run with
      | atom ha _ _ => cases ha
      | ifEq branch =>
        simp only [same,ite_true,ite_false] at branch
        obtain ⟨ds,hs,rfl,ht,hm⟩ := (walk_iff _ len start r m one cur stop fits).mp branch
        exact ⟨ds,hs,rfl,ht,hm⟩
    · rintro ⟨ds,hs,rfl,ht,hm⟩
      apply Runs.ifEq
      simp only [same,ite_true,ite_false]
      exact (walk_iff _ len start r m one cur stop fits).mpr ⟨ds,hs,rfl,ht,hm⟩

end Cube.Scatter

end BorderVNP
end Computability
end OAI
