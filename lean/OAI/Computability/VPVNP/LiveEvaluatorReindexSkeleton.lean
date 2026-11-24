import OAI.Computability.VPVNP.LiveEvaluatorReindex
import OAI.Computability.VPVNP.LiveEvaluatorInitializeStages

/-!
# Writing the zero-exponent evaluator input on the live tape

The runtime suffix consists of three unary width fields and one exponent
field, with a zero terminator after each field. The exponent payload symbols
start at zero and are overwritten by the subsequent coordinate scatter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorReindexSkeleton

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Evaluator.InputBank
open scoped Fin.CommRing

variable {w t Z : ℕ}

/-- Characterization of the zero-exponent runtime input by absolute address.
The exponent field begins at an odd offset, so its tags have odd addresses. -/
def skeletonBit (Z T j : ℕ) : Bool :=
  if j = 2*Z ∨ j = 2*Z+1+2*T ∨ j = 4*Z+2+2*T ∨ j+1 = 2*T+6*Z+4 then false
  else if 2*Z < j ∧ j < 2*Z+1+2*T then decide (j%2 = 1) else true

private theorem constant_field (n j : ℕ) (b : Bool) (hj : j < 2*n+1) :
    (fieldBits (List.replicate n b))[j]? =
      some (if j = 2*n then false else if j%2 = 0 then true else b) := by
  let xs := List.replicate n b
  have hx : xs.length = n := List.length_replicate ..
  rw [List.getElem?_eq_getElem (by rw [length_fieldBits, List.length_replicate]; omega)]
  apply congrArg some
  by_cases h : j = 2*n
  · subst j
    simpa [hx, xs] using fieldBits_end xs
  let i : Fin xs.length := ⟨j/2, by omega⟩
  by_cases he : j%2 = 0
  · have hi : 2*i.val = j := by dsimp [i]; omega
    simpa [hi,h,he] using fieldBits_tag xs i
  · have hi : 2*i.val+1 = j := by dsimp [i]; omega
    simpa [hi,h,he,xs] using fieldBits_payload xs i

private theorem zero_array (t Z : ℕ) :
    List.ofFn (RAMSerialization.arrayBits t Z (fun _ => 0)) = List.replicate (t*Z) false := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_ofFn, List.getElem_replicate]
    obtain ⟨⟨a,b⟩,he⟩ := finProdFinEquiv.surjective (⟨j,by simpa using hj⟩ : Fin (t*Z))
    rw [← he, RAMSerialization.arrayBits_at, RAMSerialization.wordBits_zero]

/-- Every generated symbol is the corresponding byte of the actual serialized
evaluator input for the zero exponent vector. -/
theorem runtime_zero_at (t Z j : ℕ) (hj : j < 2*(t*Z)+6*Z+4) :
    (EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z)))[j]? =
      some (skeletonBit Z (t*Z) j) := by
  let T := t*Z
  let U := fieldBits (List.replicate Z true)
  let E := fieldBits (List.replicate T false)
  have hU : U.length = 2*Z+1 := by simp [U, length_fieldBits]
  have hE : E.length = 2*T+1 := by simp [E, length_fieldBits]
  change j < 2*T+6*Z+4 at hj
  rw [EvaluatorProgramRawInput.runtime, zero_array, List.append_assoc, List.append_assoc]
  change (U ++ (E ++ (U ++ U)))[j]? = some (skeletonBit Z T j)
  by_cases h₀ : j < U.length
  · rw [List.getElem?_append_left h₀, constant_field Z j true (by omega)]
    simp only [skeletonBit]; split_ifs <;> first | rfl | omega
  rw [List.getElem?_append_right (Nat.le_of_not_gt h₀)]
  by_cases h₁ : j-U.length < E.length
  · rw [List.getElem?_append_left h₁, constant_field T _ false (by omega)]
    simp only [skeletonBit]; split_ifs <;> simp_all <;> omega
  rw [List.getElem?_append_right (Nat.le_of_not_gt h₁)]
  by_cases h₂ : j-U.length-E.length < U.length
  · rw [List.getElem?_append_left h₂, constant_field Z _ true (by omega)]
    simp only [skeletonBit]; split_ifs <;> first | rfl | omega
  rw [List.getElem?_append_right (Nat.le_of_not_gt h₂), constant_field Z _ true (by omega)]
  simp only [skeletonBit]; split_ifs <;> first | rfl | omega


/-- Public words give the unary width, total number of exponent bits, first
destination symbol address, and total length of the runtime suffix. -/
def setupOps : List (Op 32 4) :=
  [.constant 1 1, .constant 2 2, .stateWord 3, .publicWord 4 0, .publicWord 5 1,
   .publicWord 6 2, .publicWord 7 3, .binary .add 8 4 4, .binary .add 9 5 5,
   .binary .add 9 9 8, .binary .add 9 9 1, .binary .add 10 8 9,
   .binary .add 10 10 1, .binary .add 11 3 1, .binary .add 12 6 3,
   .binary .mod 13 3 2, .binary .add 13 13 1]

/-- Every active path uses eight local control instructions after setup to
select the tape symbol, one write, and one last-cursor test. -/
def skeletonStage : Template 38 32 4 where
  literalWidth := 2
  entry := 0
  code i := if h : i.val < setupOps.length then
      setupOps[i.val].emit ⟨i.val+1, by have : setupOps.length = 17 := rfl; omega⟩ 31
    else match i.val with
    | 17 => .jumpLt 3 7 18 31
    | 18 => .jumpEq 3 8 32 19
    | 19 => .jumpEq 3 9 33 20
    | 20 => .jumpEq 3 10 34 21
    | 21 => .jumpEq 11 7 35 22
    | 22 => .jumpLt 8 3 23 24
    | 23 => .jumpLt 3 9 25 26
    | 24 => .copy 15 15 26
    | 25 => .copy 15 13 27
    | 26 => .copy 15 2 27
    | 27 => .writeExternal 12 15 28
    | 28 => .jumpEq 11 7 29 30
    | 29 => .accept
    | 30 => .returnState 11
    | 32 => .copy 15 1 33
    | 33 => .copy 15 1 34
    | 34 => .copy 15 1 35
    | 35 => .copy 15 1 36
    | 36 => .copy 15 1 37
    | 37 => .copy 15 1 27
    | _ => .reject

private def end₀ (pub : Fin 4 → Word w) := pub 0 + pub 0
private def end₁ (pub : Fin 4 → Word w) := (pub 1 + pub 1) + end₀ pub + 1
private def end₂ (pub : Fin 4 → Word w) := end₀ pub + end₁ pub + 1

private def selected (pub : Fin 4 → Word w) (j : Word w) : Word w :=
  if j = end₀ pub ∨ j = end₁ pub ∨ j = end₂ pub ∨ j+1 = pub 3 then 1
  else if end₀ pub < j ∧ j < end₁ pub then BinaryOp.mod.eval j 2 + 1 else 2

private theorem setup_trace (pub : Fin 4 → Word w) (j : Word w) (regs : Regs w 32) (m : Memory w) :
    ∃ out, trace pub j setupOps regs m = some (List.replicate 17 .tick, out, m) ∧
      out 1 = 1 ∧ out 2 = 2 ∧ out 3 = j ∧ out 7 = pub 3 ∧ out 8 = end₀ pub ∧
      out 9 = end₁ pub ∧ out 10 = end₂ pub ∧ out 11 = j+1 ∧ out 12 = pub 2 + j ∧
      out 13 = BinaryOp.mod.eval j 2 + 1 := by
  simp (config := {decide := true}) [setupOps, trace, Op.effect, Function.update,
    BinaryOp.eval, end₀, end₁, end₂]

private theorem contains_setup (pub : Fin 4 → Word w) :
    Contains (skeletonStage.instantiate w pub) 31 0 setupOps 17 := by
  iterate 17 apply Contains.cons rfl
  exact .nil _

private def regSymbol (r : Regs w 32) : Word w :=
  if r 3 = r 8 ∨ r 3 = r 9 ∨ r 3 = r 10 ∨ r 11 = r 7 then r 1
  else if r 8 < r 3 ∧ r 3 < r 9 then r 13 else r 2

private abbrev SkelMachine (w : ℕ) := Machine w 38 32 4
private abbrev SkelPC := Fin 38
private abbrev SkelReg := Fin 32

private theorem execLt (M : SkelMachine w) (pc yes no : SkelPC) (a b : SkelReg)
    (h : M.code pc = .jumpLt a b yes no) (j : Word w) (r : Regs w 32) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute M.program (f+1) ⟨pc,j,r,fun _ => 0⟩ m bits =
      (execute M.program f ⟨if r a < r b then yes else no,j,r,fun _ => 0⟩ m bits).map (Report.prepend .tick) := by
  simp only [execute, Machine.program, h, Instr.run]

private theorem execEq (M : SkelMachine w) (pc yes no : SkelPC) (a b : SkelReg)
    (h : M.code pc = .jumpEq a b yes no) (j : Word w) (r : Regs w 32) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute M.program (f+1) ⟨pc,j,r,fun _ => 0⟩ m bits =
      (execute M.program f ⟨if r a = r b then yes else no,j,r,fun _ => 0⟩ m bits).map (Report.prepend .tick) := by
  simp only [execute, Machine.program, h, Instr.run]

private theorem execCopy (M : SkelMachine w) (pc next : SkelPC) (src : SkelReg)
    (h : M.code pc = .copy 15 src next) (j : Word w) (r : Regs w 32) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute M.program (f+1) ⟨pc,j,r,fun _ => 0⟩ m bits =
      (execute M.program f ⟨next,j,Function.update r 15 (r src),fun _ => 0⟩ m bits).map (Report.prepend .tick) := by
  simp only [execute, Machine.program, h, Instr.run, Config.put]

private theorem execWrite (pub : Fin 4 → Word w) (j : Word w) (r : Regs w 32)
    (m : Memory w) (bits : List Bool) (f : ℕ) :
    let M := skeletonStage.instantiate w pub
    execute M.program (f+3) ⟨27,j,r,fun _ => 0⟩ m bits = if bits = [] then
      some ⟨[.write (r 12) (r 15),.tick], if r 11 = r 7 then none else some (r 11)⟩ else none := by
  let M := skeletonStage.instantiate w pub
  have h27 : M.code 27 = .writeExternal 12 15 28 := rfl
  have h28 : M.code 28 = .jumpEq 11 7 29 30 := rfl
  have h29 : M.code 29 = .accept := rfl
  have h30 : M.code 30 = .returnState 11 := rfl
  change execute M.program (f+3) _ m bits = _
  by_cases he : r 11 = r 7 <;> cases bits <;>
    simp only [execute, Machine.program, h27,h28,h29,h30, Instr.run, he, ↓reduceIte,
      reduceCtorEq, Option.map_some, Option.map_none, Report.prepend]

private theorem control_exec (pub : Fin 4 → Word w) (j : Word w) (r : Regs w 32) (m : Memory w)
    (f : ℕ) (bits : List Bool) (active : r 3 < r 7) :
    let M := skeletonStage.instantiate w pub
    execute M.program (f+11) ⟨17,j,r,fun _ => 0⟩ m bits = if bits = [] then
      some ⟨List.replicate 8 .tick ++ [.write (r 12) (regSymbol r),.tick],
        if r 11 = r 7 then none else some (r 11)⟩ else none := by
  let M := skeletonStage.instantiate w pub
  change execute M.program (f+11) _ m bits = _
  have op17 := execLt M 17 18 31 3 7 (by rfl)
  have op18 := execEq M 18 32 19 3 8 (by rfl)
  have op19 := execEq M 19 33 20 3 9 (by rfl)
  have op20 := execEq M 20 34 21 3 10 (by rfl)
  have op21 := execEq M 21 35 22 11 7 (by rfl)
  have op22 := execLt M 22 23 24 8 3 (by rfl)
  have op23 := execLt M 23 25 26 3 9 (by rfl)
  have op24 := execCopy M 24 26 15 (by rfl)
  have op25 := execCopy M 25 27 13 (by rfl)
  have op26 := execCopy M 26 27 2 (by rfl)
  have op32 := execCopy M 32 33 1 (by rfl)
  have op33 := execCopy M 33 34 1 (by rfl)
  have op34 := execCopy M 34 35 1 (by rfl)
  have op35 := execCopy M 35 36 1 (by rfl)
  have op36 := execCopy M 36 37 1 (by rfl)
  have op37 := execCopy M 37 27 1 (by rfl)
  have write := execWrite pub j
  change ∀ (r : Regs w 32) (m : Memory w) (bs : List Bool) (f : ℕ), execute M.program (f+3) _ m bs = _ at write
  rw [op17, ite_eq_left active, op18]
  by_cases h₀ : r 3 = r 8
  · rw [ite_eq_left h₀, op32, op33, op34, op35, op36, op37, write]
    cases bits <;> simp (config := {decide := true}) [regSymbol,h₀,Function.update,Report.prepend]
  rw [ite_eq_right h₀, op19]
  by_cases h₁ : r 3 = r 9
  · rw [ite_eq_left h₁, op33, op34, op35, op36, op37, write]
    cases bits <;> simp (config := {decide := true}) [regSymbol,h₁,Function.update,Report.prepend]
  rw [ite_eq_right h₁, op20]
  by_cases h₂ : r 3 = r 10
  · rw [ite_eq_left h₂, op34, op35, op36, op37, write]
    cases bits <;> simp (config := {decide := true}) [regSymbol,h₂,Function.update,Report.prepend]
  rw [ite_eq_right h₂, op21]
  by_cases h₃ : r 11 = r 7
  · rw [ite_eq_left h₃, op35, op36, op37, write]
    cases bits <;> simp (config := {decide := true}) [regSymbol,h₃,Function.update,Report.prepend]
  rw [ite_eq_right h₃, op22]
  by_cases h₄ : r 8 < r 3
  · rw [ite_eq_left h₄,op23]
    by_cases h₅ : r 3 < r 9
    · rw [ite_eq_left h₅,op25,write]
      cases bits <;> simp (config := {decide := true}) [regSymbol,h₀,h₁,h₂,h₃,h₄,h₅,Function.update,Report.prepend]
    · rw [ite_eq_right h₅,op26,write]
      cases bits <;> simp (config := {decide := true}) [regSymbol,h₀,h₁,h₂,h₃,h₅,Function.update,Report.prepend]
  · rw [ite_eq_right h₄,op24,op26,write]
    cases bits <;> simp (config := {decide := true}) [regSymbol,h₀,h₁,h₂,h₃,h₄,Function.update,Report.prepend]

/-- An active call is deterministic and emits exactly one symbol write.
The last cell hands off to the next stage in that same call. -/
private theorem execute_active_word (pub : Fin 4 → Word w) (j : Word w) (m : Memory w)
    (f : ℕ) (bits : List Bool) (active : j < pub 3) :
    let P := (skeletonStage.instantiate w pub).program
    execute P (f+28) (P.start j) m bits = if bits = [] then
      some ⟨List.replicate 25 .tick ++ [.write (pub 2 + j) (selected pub j),.tick],
        if j+1 = pub 3 then none else some (j+1)⟩ else none := by
  obtain ⟨rs, ht, h1,h2,h3,h7,h8,h9,h10,h11,h12,h13⟩ := setup_trace pub j (fun _ => 0) m
  have he := (contains_setup pub).execute (by rfl) j (fun _ => 0) (fun _ => 0) m bits (f+11)
  dsimp only
  change execute _ (f+11+setupOps.length) (Config.mk 0 j (fun _ => 0) (fun _ => 0)) m bits = _
  rw [he, run_eq_trace]
  change (trace pub j setupOps (fun _ => 0) m).bind _ = _
  rw [ht, Option.bind_some]
  dsimp only
  rw [control_exec pub j rs m f bits (by rwa [h3,h7])]
  simp only [regSymbol, selected, h1,h2,h3,h7,h8,h9,h10,h11,h12,h13]
  cases bits <;> rfl


private theorem selected_eq (hw : 2 ≤ w) (pub : Fin 4 → Word w) (j : Word w)
    (hlen : (pub 3).val = 2*(pub 1).val + 6*(pub 0).val + 4) (active : j < pub 3) :
    selected pub j = PrimedInputRAM.encodeBit w (skeletonBit (pub 0).val (pub 1).val j.val) + 1 := by
  have cap := (pub 3).isLt
  have hj := Fin.lt_def.mp active
  have a : (end₀ pub).val = 2*(pub 0).val := by
    rw [end₀, Fin.val_add_eq_of_add_lt (by omega)]; omega
  have b : (end₁ pub).val = 2*(pub 0).val + 1 + 2*(pub 1).val := by
    unfold end₁
    have d : (pub 1 + pub 1).val = 2*(pub 1).val := by
      rw [Fin.val_add_eq_of_add_lt (by omega)]; omega
    have e : ((pub 1 + pub 1) + end₀ pub).val = 2*(pub 1).val + 2*(pub 0).val :=
      by rw [Fin.val_add_eq_of_add_lt (by omega), d, a]
    rw [Fin.val_add_one_of_lt' (by omega), e]; omega
  have c : (end₂ pub).val = 4*(pub 0).val + 2 + 2*(pub 1).val := by
    unfold end₂
    have e := Fin.val_add_eq_of_add_lt (a := end₀ pub) (b := end₁ pub) (by omega)
    rw [Fin.val_add_one_of_lt' (by omega), e,a,b]; omega
  have hn : (j+1).val = j.val+1 := Fin.val_add_one_of_lt' (by omega)
  have htwo : (2 : Word w).val = 2 :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hw))
  have parity : BinaryOp.mod.eval j 2 = if j.val%2 = 1 then 1 else 0 := by
    change Fin.ofNat _ (j.val % (2 : Word w).val) = _
    rw [htwo]
    by_cases h : j.val%2 = 1
    · rw [ite_eq_left h,h]; rfl
    · rw [ite_eq_right h, show j.val%2 = 0 by omega]; rfl
  simp only [selected, skeletonBit, parity, show j = end₀ pub ↔ j.val = 2*(pub 0).val by rw [Fin.ext_iff,a],
    show j = end₁ pub ↔ j.val = 2*(pub 0).val+1+2*(pub 1).val by rw [Fin.ext_iff,b],
    show j = end₂ pub ↔ j.val = 4*(pub 0).val+2+2*(pub 1).val by rw [Fin.ext_iff,c],
    show j+1 = pub 3 ↔ j.val+1 = 2*(pub 1).val+6*(pub 0).val+4 by rw [Fin.ext_iff,hn,hlen],
    Fin.lt_def, a, b]
  split_ifs <;> simp_all [PrimedInputRAM.encodeBit]
  norm_num

/-- Report for one runtime position: local control ticks, one external write,
and the local cursor test. -/
def events (addr symbol : Word w) : List (Event w) :=
  List.replicate 25 .tick ++ [.write addr symbol, .tick]

theorem events_counts (addr symbol : Word w) :
    (events addr symbol).length = 27 ∧ countProbes (events addr symbol) = 1 ∧
      choiceBits (events addr symbol) = [] := ⟨rfl,rfl,rfl⟩

theorem events_after (addr symbol : Word w) (m : Memory w) :
    after m (events addr symbol) = writeMemory m addr symbol := rfl

/-- With the actual evaluator dimensions, the native stage writes the actual
serialized input bit, encoded as a nonblank two-tape symbol. -/
theorem skeletonStage_call (hw : 2 ≤ w) (pub : Fin 4 → Word w) (j : Word w) (m : Memory w)
    (width : (pub 0).val = Z) (total : (pub 1).val = t*Z)
    (length : (pub 3).val = 2*(t*Z)+6*Z+4) (active : j < pub 3) (bits : List Bool) (f : ℕ) :
    let P := (skeletonStage.instantiate w pub).program
    let raw := EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z))
    let symbol := PrimedInputRAM.encodeBit w (raw[j.val]?.getD false) + 1
    execute P (f+28) (P.start j) m bits = if bits = [] then
      some ⟨events (pub 2 + j) symbol, if j+1 = pub 3 then none else some (j+1)⟩ else none := by
  have ha : j.val < 2*(t*Z)+6*Z+4 := by simpa [← length] using Fin.lt_def.mp active
  dsimp only
  rw [execute_active_word pub j m f bits active, selected_eq hw pub j (by rwa [width,total]) active,
    width, total, runtime_zero_at t Z j.val ha]
  rfl


/-- The complete runtime preparation uses one deterministic call per symbol.
The four terminating zeros guarantee a nonempty sweep even if either
dimension vanishes. Every address outside the prepared interval is preserved. -/
theorem skeletonStage_sweep (hw : 2 ≤ w) (pub : Fin 4 → Word w) (original : Memory w)
    (width : (pub 0).val = Z) (total : (pub 1).val = t*Z)
    (length : (pub 3).val = 2*(t*Z)+6*Z+4) (fit : (pub 2).val + (pub 3).val ≤ 2^w) :
    let raw := EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z))
    let P := (skeletonStage.instantiate w pub).program
    ∃ rs, runSegment P 28 (some 0) original (List.replicate raw.length []) = some rs ∧
      endState (some 0) rs = none ∧
      LiveEvaluatorInitialize.Copied raw (pub 2).val raw.length original (after original (eventLog rs)) ∧
      rs.length = raw.length ∧ ∀ r ∈ rs, countProbes r.events ≤ 1 := by
  let raw := EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z))
  let n := raw.length - 1
  have hlen : raw.length = n+1 := by
    have h : raw.length = 2*(t*Z)+6*Z+4 := EvaluatorProgramRawInput.runtime_length _
    dsimp [n]; omega
  have hpub : (pub 3).val = n+1 := length.trans ((EvaluatorProgramRawInput.runtime_length _).symm.trans hlen)
  let P := (skeletonStage.instantiate w pub).program
  let inv (j : ℕ) := LiveEvaluatorInitialize.Copied raw (pub 2).val j original
  let ev (j : ℕ) := events (pub 2 + (j : Word w)) (PrimedInputRAM.encodeBit w (raw[j]?.getD false) + 1)
  have hcast (j : ℕ) (h : j ≤ n+1) : (j : Word w).val = j :=
    Fin.val_cast_of_lt (by have := (pub 3).isLt; omega)
  have call (j : ℕ) (hj : j ≤ n) (m : Memory w) :
      execute P 28 (P.start (j : Word w)) m [] =
        some ⟨ev j, if j = n then none else some ((j+1 : ℕ) : Word w)⟩ := by
    have ha : (j : Word w) < pub 3 := Fin.lt_def.mpr (by rw [hcast j (by omega),hpub]; omega)
    have hn : (j : Word w) + 1 = ((j+1 : ℕ) : Word w) := by simp
    have iff : ((j+1 : ℕ) : Word w) = pub 3 ↔ j = n := by
      rw [Fin.ext_iff, hcast _ (by omega), hpub]; omega
    simpa only [ev, raw, hcast j (by omega), hn, iff, ite_true]
      using skeletonStage_call hw pub (j : Word w) m width total length ha [] 0
  have step (j : ℕ) (hj : j ≤ n) (m : Memory w) (h : inv j m) : inv (j+1) (after m (ev j)) := by
    have addr : (pub 2 + (j : Word w)).val = (pub 2).val+j := by
      rw [Fin.val_add_eq_of_add_lt (by rw [hcast j (by omega)]; omega), hcast j (by omega)]
    dsimp only [ev]
    rw [events_after]
    constructor
    · intro i hi
      by_cases eq : i = j
      · subst i; simp [writeMemory, addr]
      · simp [writeMemory, addr, eq, h.symbols i (by omega)]
    · intro a ha
      rw [writeMemory, ite_eq_right (by omega)]
      exact h.outside _ (by omega)
  have initial : inv 0 original := ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩
  obtain ⟨rs,hr,hs,hi,hl,hp⟩ := LiveHeader.run_cursor_segment P 28 n 1 inv original initial
    (fun j hj m hm => ⟨ev j, by simpa only [ite_eq_right (Nat.ne_of_lt hj)] using call j hj.le m,
      step j hj.le m hm, (events_counts ..).2.1.le⟩)
  let last : Report w := ⟨ev n,none⟩
  have he : execute P 28 (P.start (n : Word w)) (after original (eventLog rs)) [] = some last := by
    simpa only [ite_true] using call n le_rfl (after original (eventLog rs))
  change ∃ rs : List (Report w), runSegment P 28 (some 0) original (List.replicate raw.length []) = some rs ∧
    endState (some 0) rs = none ∧ inv raw.length (after original (eventLog rs)) ∧ rs.length = raw.length ∧ _
  rw [hlen]
  refine ⟨rs ++ [last], ?_, ?_, ?_, by simp [hl], ?_⟩
  · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hr]
    simp only [Option.bind_some, hs, runSegment]
    rw [he]
    rfl
  · rw [endState_append]; rfl
  · simpa only [last, eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append]
      using step n le_rfl _ hi
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hp r h
    · have heq : r = last := List.mem_singleton.mp h
      exact heq ▸ (events_counts ..).2.1.le

end LiveEvaluatorReindexSkeleton

end VPVNP
end Computability
end OAI
