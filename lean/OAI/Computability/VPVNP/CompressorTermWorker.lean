import OAI.Computability.VPVNP.CompressorFlowRebase
import OAI.Computability.VPVNP.CompressorTermRecord
import OAI.Computability.VPVNP.PrimedCounterCallPaths
import OAI.Computability.VPVNP.RAMChoicePrefix
import OAI.Computability.VPVNP.CompressorRecordsSchedule

/-!
# A fixed native worker for a strided motif scan

One call starts at the current motif ordinal. Its address prelude multiplies
the ordinal by each of the two strides. The grid search, repetition routine
and payload writer have disjoint reset register banks. Between them two native
stores save the grid and repetition results in the row just computed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TermWorker

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter
open scoped Fin.CommRing

variable {w n g r k : ℕ}

/-- Total private register count for the address prelude, grid search, repetition routine, and
payload writer. -/
abbrev Registers (n : ℕ) := 7 + (8 + (8 + (6+n)))
/-- Total public operand count for the address, grid, repetition, and payload banks. -/
abbrev Ports (g r k : ℕ) := 4 + (g + (r+k))

/-- Embed the address prelude's seven registers at the start of the fused worker's register
bank. -/
def headReg (n : ℕ) := Fin.castAddEmb (8+(8+(6+n))) (n := 7)
/-- Embed the grid search's eight registers immediately after the address prelude's registers. -/
def gridReg (n : ℕ) := (Fin.castAddEmb (8+(6+n)) (n := 8)).trans (Fin.natAddEmb 7)
/-- Embed the repetition routine's eight registers after the grid search's register bank. -/
def repReg (n : ℕ) := ((Fin.castAddEmb (6+n) (n := 8)).trans (Fin.natAddEmb 8)).trans (Fin.natAddEmb 7)
/-- Embed the payload writer's registers in the final block of the fused worker's register
bank. -/
def payloadReg (n : ℕ) := ((Fin.natAddEmb 8 (m := 6+n)).trans (Fin.natAddEmb 8)).trans (Fin.natAddEmb 7)

/-- Index the two base addresses and two strides in the worker's public operand bank. -/
def addrPort : Fin 4 → Fin (Ports g r k) := Fin.castAdd _
/-- Index the grid-search operands immediately after the four address operands. -/
def gridPort : Fin g → Fin (Ports g r k) := Fin.natAdd 4 ∘ Fin.castAdd _
/-- Index the repetition routine's operands after the address and grid operands. -/
def repPort : Fin r → Fin (Ports g r k) := Fin.natAdd 4 ∘ Fin.natAdd g ∘ Fin.castAdd k
/-- Index the payload writer's operands in the final block of public words. -/
def payloadPort : Fin k → Fin (Ports g r k) := Fin.natAdd 4 ∘ Fin.natAdd g ∘ Fin.natAdd r

/-- Assemble the four public operand banks in the order used by the fused term worker. -/
def words (addr : Fin 4 → Word w) (grid : Fin g → Word w) (reps : Fin r → Word w) (payload : Fin k → Word w) :
    Fin (Ports g r k) → Word w := Fin.append addr (Fin.append grid (Fin.append reps payload))

private theorem addr_words (a : Fin 4 → Word w) (x : Fin g → Word w) (y : Fin r → Word w) (z : Fin k → Word w) :
    words a x y z ∘ addrPort = a := by funext i; simp [words,addrPort]
private theorem grid_words (a : Fin 4 → Word w) (x : Fin g → Word w) (y : Fin r → Word w) (z : Fin k → Word w) :
    words a x y z ∘ gridPort = x := by funext i; simp [words,gridPort]
private theorem rep_words (a : Fin 4 → Word w) (x : Fin g → Word w) (y : Fin r → Word w) (z : Fin k → Word w) :
    words a x y z ∘ repPort = y := by funext i; simp [words,repPort]
private theorem payload_words (a : Fin 4 → Word w) (x : Fin g → Word w) (y : Fin r → Word w) (z : Fin k → Word w) :
    words a x y z ∘ payloadPort = z := by funext i; simp [words,payloadPort]

/-- Address of motif `j`'s input demand row computed from the input base and stride. -/
def source (addr : Fin 4 → Word w) (j : Word w) := j * addr 1 + addr 0
/-- Address of motif `j`'s output term record computed from the output base and stride. -/
def base (addr : Fin 4 → Word w) (j : Word w) := j * addr 3 + addr 2

/-- Compute the demand and term addresses, output field addresses, and next motif ordinal from
the persistent cursor. -/
def prelude : Flow 7 4 :=
  .seq (.line (.stateWord 0)) <|
  .seq (.line (.publicWord 1 1)) <|
  .seq (.line (.binary .mul 1 0 1)) <|
  .seq (.line (.publicWord 6 0)) <|
  .seq (.line (.binary .add 1 1 6)) <|
  .seq (.line (.publicWord 2 3)) <|
  .seq (.line (.binary .mul 2 0 2)) <|
  .seq (.line (.publicWord 6 2)) <|
  .seq (.line (.binary .add 2 2 6)) <|
  .seq (.line (.constant 6 1)) <|
  .seq (.line (.binary .add 3 2 6)) <|
  .seq (.line (.binary .add 4 3 6)) (.line (.binary .add 5 0 6))

private theorem prelude_exec (a : Fin 4 → Word w) (j : Word w) (m : Memory w) :
    ∃ out, Flow.Exec a j prelude (fun _ => 0) m (List.replicate 13 .tick) out m ∧
      out 1 = source a j ∧ out 2 = base a j ∧ out 3 = base a j + 1 ∧
      out 4 = base a j + 2 ∧ out 5 = j+1 := by
  let dst := base a j
  let out : Regs w 7 := ![j,source a j,dst,dst+1,dst+2,j+1,1]
  refine ⟨out,?_,rfl,rfl,rfl,rfl,rfl⟩
  unfold prelude
  repeat' apply Flow.Exec.seq (.line rfl)
  apply Flow.Exec.line
  simp (config := {decide := true}) [Op.effect,BinaryOp.eval,Function.update,source,base,out,dst]
  funext i
  fin_cases i <;> simp (config := {decide := true}) [Function.update]
  ring

/-- Assemble the fixed stages and choose their private register locations. -/
def headerCode (n : ℕ) (grid : Flow 8 g) (reps : Flow 8 r) (k : ℕ) : Flow (Registers n) (Ports g r k) :=
  .seq (renameFlow (headReg n) addrPort prelude) <|
  .seq (Rebased.code (gridReg n) gridPort (headReg n 1) grid) <|
  .seq (.line (.write (headReg n 2) (gridReg n 1))) <|
  .seq (Rebased.code (repReg n) repPort (headReg n 1) reps)
    (.line (.write (headReg n 3) (repReg n 2)))

/-- Combine the strided address prelude, grid and repetition stores, and payload writer in one
worker. -/
def code (grid : Flow 8 g) (reps : Flow 8 r) (payload : Flow (6+n) k) : Flow (Registers n) (Ports g r k) :=
  .seq (headerCode n grid reps k) (Rebased.code (payloadReg n) payloadPort (headReg n 4) payload)

/-- Schedule the fused worker with the successor motif ordinal as its return word. -/
def pass (grid : Flow 8 g) (reps : Flow 8 r) (payload : Flow (6+n) k) : Schedule.Pass :=
  ⟨_,_,_,(code grid reps payload).template (some (headReg n 5))⟩

private theorem head_left {j : Fin 7} {i : Fin 8} : gridReg n i ≠ headReg n j := by
  intro h; have := congrArg Fin.val h; change 7+i.val = j.val at this; omega

private theorem grid_left {i j : Fin 8} : repReg n i ≠ gridReg n j := by
  intro h; have := congrArg Fin.val h; change 7+(8+i.val) = 7+j.val at this; omega

private theorem head_rep {i : Fin 8} {j : Fin 7} : repReg n i ≠ headReg n j := by
  intro h; have := congrArg Fin.val h; change 7+(8+i.val) = j.val at this; omega

private theorem payload_head {i : Fin (6+n)} {j : Fin 7} : payloadReg n i ≠ headReg n j := by
  intro h; have := congrArg Fin.val h; change 7+(8+(8+i.val)) = j.val at this; omega

private theorem payload_grid {i : Fin (6+n)} {j : Fin 8} : payloadReg n i ≠ gridReg n j := by
  intro h; have := congrArg Fin.val h; change 7+(8+(8+i.val)) = 7+j.val at this; omega

private theorem payload_rep {i : Fin (6+n)} {j : Fin 8} : payloadReg n i ≠ repReg n j := by
  intro h; have := congrArg Fin.val h; change 7+(8+(8+i.val)) = 7+(8+j.val) at this; omega

private theorem outRange {a b : Type*} {f : a → b} {y : b} (h : ∀ i, f i ≠ y) :
    y ∉ Set.range f := fun ⟨i,hi⟩ => h i hi

/-- The only external writes beyond the payload are the row index and the
repetition header. The thirteen address operations consume private ticks. -/
def headerLog (dst row u : Word w) (gs rs : List (Event w)) :=
  List.replicate 13 .tick ++ gs ++ [.write dst row] ++ rs ++ [.write (dst+1) u]

private theorem prepared {grid : Flow 8 g} {reps : Flow 8 r} (n : ℕ)
    (a : Fin 4 → Word w) (x : Fin g → Word w) (y : Fin r → Word w) (z : Fin k → Word w)
    (j : Word w) (m mg mr : Memory w) (gs rs : List (Event w))
    (G R : Regs w 8)
    (hg : Flow.Exec x (source a j) grid (fun _ => 0) m gs G mg)
    (hr : Flow.Exec y (source a j) reps (fun _ => 0) (writeMemory mg (base a j) (G 1)) rs R mr) :
    ∃ out, Flow.Exec (words a x y z) j (headerCode n grid reps k) (fun _ => 0) m
      (headerLog (base a j) (G 1) (R 2) gs rs) out (writeMemory mr (base a j+1) (R 2)) ∧
      out ∘ payloadReg n = (fun _ => 0) ∧ out (headReg n 4) = base a j+2 ∧ out (headReg n 5) = j+1 := by
  let pub := words a x y z
  obtain ⟨h,hpre,hs,hd,hd1,hd2,hn⟩ := prelude_exec a j m
  obtain ⟨h',hinit,hH,oH⟩ := liftExec (headReg n) addrPort pub ((addr_words a x y z) ▸ hpre)
    (fun _ => 0) rfl
  have hHi i : h' (headReg n i) = h i := congrFun hH i
  have h0 i : h' (gridReg n i) = 0 := oH _ (outRange fun _ => head_left.symm)
  obtain ⟨g',hgrid,hG,oG⟩ := Rebased.liftExec (state := j) (gridReg n) gridPort (headReg n 1)
    (outRange fun _ => head_left) pub ((grid_words a x y z) ▸ hg) h' (funext h0) ((hHi 1).trans hs)
  have gHead i : g' (headReg n i) = h i := (oG _ (outRange fun _ => head_left)).trans (hHi i)
  have g₁ : g' (gridReg n 1) = G 1 := congrFun hG 1
  have store₁ : Flow.Exec pub j (.line (.write (headReg n 2) (gridReg n 1))) g' mg
      [.write (base a j) (G 1)] g' (writeMemory mg (base a j) (G 1)) := by
    apply Flow.Exec.line; simp only [Op.effect,gHead,hd,g₁]
  have g0 i : g' (repReg n i) = 0 :=
    (oG _ (outRange fun _ => grid_left.symm)).trans (oH _ (outRange fun _ => head_rep.symm))
  obtain ⟨r',hreps,hR,oR⟩ := Rebased.liftExec (state := j) (repReg n) repPort (headReg n 1)
    (outRange fun _ => head_rep) pub ((rep_words a x y z) ▸ hr) g' (funext g0) ((gHead 1).trans hs)
  have rHead i : r' (headReg n i) = h i := (oR _ (outRange fun _ => head_rep)).trans (gHead i)
  have r₂ : r' (repReg n 2) = R 2 := congrFun hR 2
  have store₂ : Flow.Exec pub j (.line (.write (headReg n 3) (repReg n 2))) r' mr
      [.write (base a j+1) (R 2)] r' (writeMemory mr (base a j+1) (R 2)) := by
    apply Flow.Exec.line; simp only [Op.effect,rHead,hd1,r₂]
  have r0 i : r' (payloadReg n i) = 0 := (oR _ (outRange fun _ => payload_rep.symm)).trans
    ((oG _ (outRange fun _ => payload_grid.symm)).trans (oH _ (outRange fun _ => payload_head.symm)))
  refine ⟨r',?_,funext r0,(rHead 4).trans hd2,(rHead 5).trans hn⟩
  simpa only [headerCode,headerLog,List.append_assoc] using
    (Flow.Exec.seq hinit (.seq hgrid (.seq store₁ (.seq hreps store₂))))

private theorem fixedPrefix {R K : ℕ} {pub : Fin K → Word w} {st : Word w} {a : Flow R K}
    {start m es rs m' fs out last}
    (he : Flow.Exec pub st a start m es rs m') (bits : choiceBits es = [])
    (other : Flow.Exec pub st a start m fs out last) : fs = es ∧ out = rs ∧ last = m' := by
  have reports (res : Option (Fin R)) :
      (⟨es,res.map rs⟩ : Report w) = ⟨fs,res.map out⟩ := by
    have one := (Flow.template_execute_iff a res pub st (fun _ => 0) start m (es.length+1) []
      ⟨es,res.map rs⟩).mpr ⟨rs,m',he,rfl,Nat.lt_succ_self _,bits⟩
    have two := (Flow.template_execute_iff a res pub st (fun _ => 0) start m (fs.length+1) (choiceBits fs)
      ⟨fs,res.map out⟩).mpr ⟨out,last,other,rfl,Nat.lt_succ_self _,rfl⟩
    exact (execute_prefix_unique (suffix := choiceBits fs) one two).2
  have logs := (congrArg Report.events (reports none)).symm
  refine ⟨logs,funext fun i => Option.some.inj (congrArg Report.result (reports (some i))).symm,?_⟩
  exact (Call.exec_memory other).symm.trans ((congrArg (after m) logs).trans (Call.exec_memory he))

/-- After the empty-choice prefix, the payload is executed on reset ordinary
registers with its computed base. Conversely every execution restricts to
one payload derivation with exactly its tape and memory effect. -/
theorem execute_iff {grid : Flow 8 g} {reps : Flow 8 r} (payload : Flow (6+n) k)
    (a : Fin 4 → Word w) (x : Fin g → Word w) (y : Fin r → Word w) (z : Fin k → Word w)
    (j : Word w) (m mg mr : Memory w) (gs rs : List (Event w)) (G R : Regs w 8)
    (hg : Flow.Exec x (source a j) grid (fun _ => 0) m gs G mg) (hgb : choiceBits gs = [])
    (hr : Flow.Exec y (source a j) reps (fun _ => 0) (writeMemory mg (base a j) (G 1)) rs R mr)
    (hrb : choiceBits rs = []) (cap : ℕ) (bs : List Bool) (rep : Report w) :
    let dst := base a j
    let pre := headerLog dst (G 1) (R 2) gs rs
    let mid := writeMemory mr (dst+1) (R 2)
    let T := ((pass grid reps payload).table.instantiate w (words a x y z)).program
    execute T cap (T.start j) m bs = some rep ↔
      ∃ vs V mv, Flow.Exec z (dst+2) payload (fun _ => 0) mid vs V mv ∧
        rep = ⟨pre++vs,some (j+1)⟩ ∧ pre.length+vs.length < cap ∧ choiceBits vs = bs := by
  dsimp only
  let pub := words a x y z
  let dst := base a j
  let pre := headerLog dst (G 1) (R 2) gs rs
  let mid := writeMemory mr (dst+1) (R 2)
  obtain ⟨prep,he,hzero,harg,hnext⟩ := prepared n a x y z j m mg mr gs rs G R hg hr
  have hn : choiceBits pre = [] := by simp [pre,headerLog,Flow.choiceBits_append,hgb,hrb,choiceBits,List.replicate_succ]
  change choiceBits (headerLog (base a j) (G 1) (R 2) gs rs) = [] at hn
  have core := Flow.template_execute_iff (code grid reps payload) (some (headReg n 5)) pub j (fun _ => 0)
    (fun _ => 0) m cap bs rep
  apply core.trans
  constructor
  · rintro ⟨out,last,run,result,size,tape⟩
    obtain ⟨fs,q,mq,vs,hfirst,hvs,hlog⟩ : ∃ fs q mq vs, Flow.Exec pub j (headerCode n grid reps k) (fun _ => 0) m fs q mq ∧
        Flow.Exec pub j (Rebased.code (payloadReg n) payloadPort (headReg n 4) payload) q mq vs out last ∧
        rep.events = fs++vs := by
      generalize h : rep.events = es at run
      cases run with | seq h₁ h₂ => exact ⟨_,_,_,_,h₁,h₂,rfl⟩
    obtain ⟨rfl,rfl,rfl⟩ := fixedPrefix he hn hfirst
    obtain ⟨pay,away⟩ := Rebased.restrictExec (payloadReg n) payloadPort (headReg n 4)
      (outRange fun _ => payload_head) pub payload hvs
    rw [payload_words a x y z,harg,hzero] at pay
    refine ⟨vs,_,_,pay,?_,?_,?_⟩
    · cases rep with | mk es res =>
        simp only [Report.mk.injEq]; exact ⟨hlog,result.trans (congrArg some ((away _ (outRange fun _ => payload_head)).trans hnext))⟩
    · simpa only [hlog,List.length_append] using size
    · simpa only [hlog,Flow.choiceBits_append,hn,List.nil_append] using tape
  · rintro ⟨vs,V,mv,pay,rfl,size,tape⟩
    obtain ⟨out,body,_,away⟩ := Rebased.liftExec (state := j) (payloadReg n) payloadPort (headReg n 4)
      (outRange fun _ => payload_head) pub ((payload_words a x y z) ▸ pay) prep hzero harg
    refine ⟨out,mv,.seq he body,congrArg some ((away _ (outRange fun _ => payload_head)).trans hnext).symm,?_,?_⟩
    · simpa only [List.length_append] using size
    · simpa only [Flow.choiceBits_append,hn,List.nil_append] using tape

end CompressorRecords.TermWorker

end VPVNP
end Computability
end OAI
