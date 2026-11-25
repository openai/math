import OAI.Optimization.LinearProgramming.Compression.PowerTape
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! A fixed transducer reads an explicit stream of signed binary exponents and constructs
the five-opcode power tape. The sign bit follows the digits of each term. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

variable {K : Type*}

inductive PowerToken where
  | beginTerm
  | bit (value : Bool)
  | finish (negative : Bool)
  deriving Repr, DecidableEq

def PowerToken.code : PowerToken → ℕ
  | .beginTerm => 0
  | .bit false => 1
  | .bit true => 2
  | .finish false => 3
  | .finish true => 4

def PowerToken.ops : PowerToken → List PowerOp
  | .beginTerm => [.beginTerm]
  | .bit false => [.square]
  | .bit true => [.square, .multiply]
  | .finish false => [.commit]
  | .finish true => [.invert, .commit]

def exponentTokens (x : ℤ) : List PowerToken :=
  .beginTerm :: (x.natAbs.bits.reverse.map .bit ++ [.finish (decide (x < 0))])

def signedBitTape (xs : List ℤ) : List PowerToken := xs.flatMap exponentTokens

private theorem bits_expand (bs : List Bool) : (bs.map PowerToken.bit).flatMap PowerToken.ops = digitOps bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [digitOps, PowerToken.ops, ih]

theorem expand_exponentTokens (x : ℤ) : (exponentTokens x).flatMap PowerToken.ops = termOps x := by
  by_cases h : x < 0 <;> simp [exponentTokens, termOps, PowerToken.ops, h]
  all_goals simpa only [List.map_reverse] using bits_expand x.natAbs.bits.reverse

theorem expand_signedBitTape (xs : List ℤ) : (signedBitTape xs).flatMap PowerToken.ops = productOps xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [signedBitTape, productOps, List.flatMap_cons, List.flatMap_append, expand_exponentTokens]
      using congrArg (termOps x ++ ·) ih

theorem signedBitTape_length (xs : List ℤ) :
    (signedBitTape xs).length = (xs.map fun x => x.natAbs.size + 2).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (exponentTokens x ++ signedBitTape xs).length = _
    simp [exponentTokens, ih, Nat.size_eq_bits_len, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    omega

theorem powerTokens_opCount (xs : List PowerToken) : (xs.flatMap PowerToken.ops).length ≤ 2*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x.ops.length ≤ 2 := by cases x with
      | beginTerm => decide
      | bit b | finish b => cases b <;> decide
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- The input region begins after two reserved output words per token. The scalar bank
is unchanged by every encoder instruction. -/
def powerEncoderAddressInput (ts : List PowerToken) : List ℕ :=
  [2*ts.length+8, 3*ts.length+8, 8, 0, 1, 2, 3, 4] ++
    (List.replicate (2*ts.length) 0 ++ ts.map PowerToken.code)

private def putWord (r : ℕ) : Block :=
  .seq (.op (.addrStore 2 r)) (.op (.incr 2 2))

private def emitOps : Block :=
  .branch (.addrLT 3 4) (putWord 3)
    (.branch (.addrLT 3 5) (putWord 4)
      (.branch (.addrLT 3 6) (.seq (putWord 4) (putWord 5))
        (.branch (.addrLT 3 7) (putWord 7) (.seq (putWord 6) (putWord 7)))))

private def encoderBody : Block :=
  .seq (.op (.addrLoad 3 0)) (.seq (.op (.incr 0 0)) emitOps)

/-- The last four writes install the header expected by the power interpreter. -/
def powerEncoderBlock : Block :=
  .seq (.loop (.addrLT 0 1) encoderBody)
    (Block.straight [.addrCopy 1 2, .addrConst 0 8, .addrConst 2 4, .addrConst 3 0])


private def overlay (xs : List ℕ) (t : ℕ → ℕ) (j : ℕ) : ℕ := xs[j]?.getD (t j)

private theorem overlay_push (xs : List ℕ) (t : ℕ → ℕ) (v : ℕ) :
    Function.update (overlay xs t) xs.length v = overlay (xs ++ [v]) t := by
  funext j
  by_cases hj : j < xs.length
  · simp [overlay, Function.update_of_ne hj.ne, List.getElem?_append_left hj]
  · have hle : xs.length ≤ j := Nat.le_of_not_gt hj
    rw [show overlay (xs ++ [v]) t j = [v][j-xs.length]?.getD (t j) by
      simp [overlay,List.getElem?_append_right hle]]
    by_cases he : j = xs.length
    · subst j; simp
    · have hdiff : j-xs.length ≠ 0 := by omega
      simp [overlay, Function.update_of_ne he, List.getElem?_eq_none hle, hdiff]

private def indexBank (src stop dst tag : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => src
  | 1 => stop
  | 2 => dst
  | 3 => tag
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | i+8 => t i

private def config (d : ℕ → K) (src stop dst tag : ℕ) (t : ℕ → ℕ) : Memory K :=
  ⟨d, indexBank src stop dst tag t⟩

private theorem set0 (d : ℕ → K) (src stop dst tag x : ℕ) (t : ℕ → ℕ) :
    (config d src stop dst tag t).putIndex 0 x = config d x stop dst tag t := by
  unfold config Memory.putIndex
  congr 1
  funext j; match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem set1 (d : ℕ → K) (src stop dst tag x : ℕ) (t : ℕ → ℕ) :
    (config d src stop dst tag t).putIndex 1 x = config d src x dst tag t := by
  unfold config Memory.putIndex
  congr 1
  funext j; match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem set2 (d : ℕ → K) (src stop dst tag x : ℕ) (t : ℕ → ℕ) :
    (config d src stop dst tag t).putIndex 2 x = config d src stop x tag t := by
  unfold config Memory.putIndex
  congr 1
  funext j; match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem set3 (d : ℕ → K) (src stop dst tag x : ℕ) (t : ℕ → ℕ) :
    (config d src stop dst tag t).putIndex 3 x = config d src stop dst x t := by
  unfold config Memory.putIndex
  congr 1
  funext j; match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem setHigh (d : ℕ → K) (src stop dst tag j v : ℕ) (t : ℕ → ℕ) :
    (config d src stop dst tag t).putIndex (j+8) v =
      config d src stop dst tag (Function.update t j v) := by
  unfold config Memory.putIndex
  congr 1
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | i+8 =>
    by_cases he : i = j
    · subst i; simp [indexBank]
    · have hne : i+8 ≠ j+8 := by omega
      simp [Function.update_of_ne hne, Function.update_of_ne he, indexBank]

private def unchanged (d : ℕ → K) (m : Memory K) := m.data = d

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem push_eval (d : ℕ → K) (src stop tag r : ℕ) (out : List ℕ) (t : ℕ → ℕ)
    (v : ℕ) (hv : indexBank src stop (out.length+8) tag (overlay out t) r = v) :
    Block.Eval (unchanged d) (putWord r)
      (config d src stop (out.length+8) tag (overlay out t)) 2
      (config d src stop ((out++[v]).length+8) tag (overlay (out++[v]) t)) := by
  let m := config d src stop (out.length+8) tag (overlay out t)
  have hw : m.putIndex (m.index 2) (m.index r) =
      config d src stop (out.length+8) tag (overlay (out++[v]) t) := by
    change (config d src stop (out.length+8) tag (overlay out t)).putIndex (out.length+8)
      (indexBank src stop (out.length+8) tag (overlay out t) r) = _
    rw [hv, setHigh, overlay_push]
  have first := Block.Eval.op_addrStore (safe := unchanged d) m 2 r rfl rfl
  rw [hw] at first
  refine Block.Eval.seq (l := 1) first ?_
  let m' := config d src stop (out.length+8) tag (overlay (out++[v]) t)
  have hi := Block.Eval.op_incr (safe := unchanged d) m' 2 2 rfl rfl
  change Block.Eval _ _ _ _ ((config d src stop (out.length+8) tag _).putIndex 2 (out.length+8+1)) at hi
  rw [set2] at hi
  simpa using hi

private theorem push_pair (d : ℕ → K) (src stop tag r₁ r₂ : ℕ) (out : List ℕ) (t : ℕ → ℕ)
    (u v : ℕ) (h₁ : indexBank src stop (out.length+8) tag (overlay out t) r₁ = u)
    (h₂ : indexBank src stop ((out++[u]).length+8) tag (overlay (out++[u]) t) r₂ = v) :
    Block.Eval (unchanged d) (.seq (putWord r₁) (putWord r₂))
      (config d src stop (out.length+8) tag (overlay out t)) 4
      (config d src stop ((out++[u,v]).length+8) tag (overlay (out++[u,v]) t)) := by
  have h := Block.Eval.seq (push_eval d src stop tag r₁ out t u h₁)
    (push_eval d src stop tag r₂ (out++[u]) t v h₂)
  simpa only [List.append_assoc, List.cons_append, List.nil_append, Nat.reduceAdd] using h

private def tokenWords (tok : PowerToken) := tok.ops.map PowerOp.code

private theorem emit_eval (d : ℕ → K) (src stop : ℕ) (out : List ℕ) (t : ℕ → ℕ)
    (tok : PowerToken) :
    ∃ k ≤ 8, Block.Eval (unchanged d) emitOps
      (config d src stop (out.length+8) tok.code (overlay out t)) k
      (config d src stop ((out++tokenWords tok).length+8) tok.code (overlay (out++tokenWords tok) t)) := by
  cases tok with
  | beginTerm =>
    exact ⟨4,by decide, .branchTrue rfl (push_eval d src stop _ 3 out t 0 rfl)⟩
  | bit b =>
    cases b
    · exact ⟨5,by decide, .branchFalse rfl (.branchTrue rfl (push_eval d src stop _ 4 out t 1 rfl))⟩
    · exact ⟨8,by decide, .branchFalse rfl (.branchFalse rfl (.branchTrue rfl
        (push_pair d src stop _ 4 5 out t 1 2 rfl rfl)))⟩
  | finish b =>
    cases b
    · exact ⟨7,by decide, .branchFalse rfl (.branchFalse rfl (.branchFalse rfl (.branchTrue rfl
        (push_eval d src stop _ 7 out t 4 rfl))))⟩
    · exact ⟨8,by decide, .branchFalse rfl (.branchFalse rfl (.branchFalse rfl (.branchFalse rfl
        (push_pair d src stop _ 6 7 out t 3 4 rfl rfl))))⟩


private theorem body_eval (d : ℕ → K) (src stop tag : ℕ) (out : List ℕ) (t : ℕ → ℕ)
    (tok : PowerToken) (hread : t src = tok.code) (hdisj : out.length ≤ src) :
    ∃ k ≤ 10, Block.Eval (unchanged d) encoderBody
      (config d (src+8) (stop+8) (out.length+8) tag (overlay out t)) k
      (config d (src+1+8) (stop+8) ((out++tokenWords tok).length+8) tok.code
        (overlay (out++tokenWords tok) t)) := by
  let m := config d (src+8) (stop+8) (out.length+8) tag (overlay out t)
  have hv : m.index (m.index 0) = tok.code := by
    change out[src]?.getD (t src) = _
    rw [List.getElem?_eq_none hdisj]
    exact hread
  have first := Block.Eval.op_addrLoad (safe := unchanged d) m 3 0 rfl rfl
  rw [hv] at first
  change Block.Eval _ _ _ _ ((config _ _ _ _ _ _).putIndex 3 tok.code) at first
  rw [set3] at first
  have second := Block.Eval.op_incr (safe := unchanged d)
    (config d (src+8) (stop+8) (out.length+8) tok.code (overlay out t)) 0 0 rfl rfl
  change Block.Eval _ _ _ _
    ((config _ _ _ _ _ _).putIndex 0 (src+8+1)) at second
  rw [set0] at second
  obtain ⟨k,hk,h⟩ := emit_eval d (src+1+8) (stop+8) out t tok
  exact ⟨1+(1+k),by omega, .seq first (.seq second h)⟩

private theorem tokenWords_length (tok : PowerToken) : (tokenWords tok).length ≤ 2 := by
  cases tok with
  | beginTerm => decide
  | bit b | finish b => cases b <;> decide

private theorem encoder_loop (d : ℕ → K) (t : ℕ → ℕ) (xs : List PowerToken)
    (src stop tag : ℕ) (out : List ℕ) (hrange : src + xs.length = stop)
    (hdisj : out.length + 2*xs.length ≤ src)
    (hread : ∀ i, ∀ hi : i < xs.length, t (src+i) = xs[i].code) :
    ∃ k last, k ≤ 12*xs.length+1 ∧
      Block.Eval (unchanged d) (.loop (.addrLT 0 1) encoderBody)
        (config d (src+8) (stop+8) (out.length+8) tag (overlay out t)) k
        (config d (stop+8) (stop+8) ((out++xs.flatMap tokenWords).length+8) last
          (overlay (out++xs.flatMap tokenWords) t)) := by
  induction xs generalizing src tag out with
  | nil =>
    have he : src = stop := by simpa using hrange
    subst src
    simp only [List.flatMap_nil, List.append_nil, List.length_nil, Nat.mul_zero, Nat.zero_add]
    exact ⟨1,tag,le_rfl,.loopFalse (by simp [Cond.test,config,indexBank]) rfl⟩
  | cons tok xs ih =>
    have hs : src < stop := by simp only [List.length_cons] at hrange; omega
    have freeze : t src = tok.code := by
      have h := hread 0 (by simp)
      change t (src+0) = tok.code at h
      simpa using h
    obtain ⟨c,hc,one⟩ := body_eval d src stop tag out t tok freeze (by omega)
    have htail (i : ℕ) (hi : i < xs.length) : t (src+1+i) = xs[i].code := by
      have h := hread (i+1) (by simpa using hi)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    have hsep : (out++tokenWords tok).length + 2*xs.length ≤ src+1 := by
      have h := tokenWords_length tok
      simp only [List.length_cons] at hdisj
      simp only [List.length_append]
      omega
    obtain ⟨k,last,hk,rest⟩ := ih (src+1) tok.code (out++tokenWords tok)
      (by simp only [List.length_cons] at hrange; omega) hsep htail
    have guard : (Cond.addrLT 0 1).test
        (config d (src+8) (stop+8) (out.length+8) tag (overlay out t)) = true := by
      simp [Cond.test,config,indexBank,hs]
    refine ⟨1+c+1+k,last,by simp only [List.length_cons]; omega,?_⟩
    simpa only [List.flatMap_cons, List.append_assoc] using Block.Eval.loopTrue guard one rest

private theorem install_header (d : ℕ → K) (endAddr outputAddr tag : ℕ) (t : ℕ → ℕ) :
    Block.Eval (unchanged d)
      (Block.straight [.addrCopy 1 2, .addrConst 0 8, .addrConst 2 4, .addrConst 3 0])
      (config d endAddr endAddr outputAddr tag t) 4 (config d 8 outputAddr 4 0 t) := by
  have h₁ := Block.Eval.op_addrCopy (safe := unchanged d) (config d endAddr endAddr outputAddr tag t)
    1 2 rfl rfl
  change Block.Eval _ _ _ _ ((config _ _ _ _ _ _).putIndex 1 outputAddr) at h₁
  rw [set1] at h₁
  have h₂ := Block.Eval.op_addrConst (safe := unchanged d) (config d endAddr outputAddr outputAddr tag t)
    0 8 rfl rfl
  rw [set0] at h₂
  have h₃ := Block.Eval.op_addrConst (safe := unchanged d) (config d 8 outputAddr outputAddr tag t)
    2 4 rfl rfl
  rw [set2] at h₃
  have h₄ := Block.Eval.op_addrConst (safe := unchanged d) (config d 8 outputAddr 4 tag t) 3 0 rfl rfl
  rw [set3] at h₄
  exact .seq h₁ (.seq h₂ (.seq h₃ (.seq h₄ (.skip rfl))))

private def inputWords (ts : List PowerToken) : List ℕ :=
  List.replicate (2*ts.length) 0 ++ ts.map PowerToken.code

private def inputTail (ts : List PowerToken) (j : ℕ) : ℕ := (inputWords ts)[j]?.getD 0

/-- The high address memory after encoding, including the unchanged input beyond the
opcode prefix. -/
def encodedPowerTail (ts : List PowerToken) (j : ℕ) : ℕ :=
  overlay (ts.flatMap tokenWords) (inputTail ts) j

private theorem input_code (ts : List PowerToken) (i : ℕ) (hi : i < ts.length) :
    inputTail ts (2*ts.length+i) = ts[i].code := by
  simp [inputTail, inputWords, hi]

private theorem reg_encoder (ts : List PowerToken) (d : ℕ → K) :
    ∃ k ≤ 12*ts.length+5, Block.Eval (unchanged d) powerEncoderBlock
      (config d (2*ts.length+8) (3*ts.length+8) 8 0 (inputTail ts)) k
      (config d 8 ((ts.flatMap tokenWords).length+8) 4 0 (encodedPowerTail ts)) := by
  obtain ⟨c,tag,hc,loop⟩ := encoder_loop d (inputTail ts) ts (2*ts.length) (3*ts.length) 0 []
    (by omega) (by simp) (input_code ts)
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at loop
  have he : overlay [] (inputTail ts) = inputTail ts := by funext j; simp [overlay]
  rw [he] at loop
  exact ⟨c+4,by omega,.seq loop (install_header ..)⟩

private theorem words_flatMap (ts : List PowerToken) :
    ts.flatMap tokenWords = (ts.flatMap PowerToken.ops).map PowerOp.code := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih,tokenWords]

theorem encodedPowerTail_code (ts : List PowerToken) (i : ℕ) (hi : i < (ts.flatMap PowerToken.ops).length) :
    encodedPowerTail ts i = (ts.flatMap PowerToken.ops)[i].code := by
  unfold encodedPowerTail overlay
  rw [words_flatMap,List.getElem?_map,List.getElem?_eq_getElem hi]
  rfl


/-- Initial memory for an encoder that may be embedded at any program address. -/
def powerEncoderMemory (ts : List PowerToken) (d : ℕ → K) : Memory K :=
  config d (2*ts.length+8) (3*ts.length+8) 8 0 (inputTail ts)

/-- The encoder writes the interpreter header in place. It retains the input words
after the opcode prefix, where they cannot affect subsequent interpretation. -/
def powerEncodedMemory (ts : List PowerToken) (d : ℕ → K) : Memory K :=
  config d 8 ((ts.flatMap PowerToken.ops).length+8) 4 0 (encodedPowerTail ts)

/-- The assembled instruction sequence performs the entire token expansion with a
linear control-step bound. The scalar bank is preserved throughout the execution. -/
theorem powerEncoderBlock_correct {P : Program} {pc : ℕ} (ts : List PowerToken) (d : ℕ → K)
    (located : CodeAt P pc (powerEncoderBlock.compile pc)) :
    ∃ k ≤ 12*ts.length+5, Execution P (fun s => s.data = d)
      ((powerEncoderMemory ts d).atPC pc) k
      ((powerEncodedMemory ts d).atPC (pc + powerEncoderBlock.size)) := by
  obtain ⟨k,hk,h⟩ := reg_encoder ts d
  refine ⟨k,hk,?_⟩
  have ex := h.compile_correct located
  simpa only [powerEncoderMemory, powerEncodedMemory, unchanged, State.memory,
    words_flatMap, List.length_map] using ex

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem start_encoder (ts : List PowerToken) (input : List K) :
    start (powerEncoderAddressInput ts) input =
      (powerEncoderMemory ts (fun i => input[i]?.getD 0)).atPC 0 := by
  unfold start powerEncoderMemory config Memory.atPC
  congr 1
  funext j
  match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

def powerEncoderProgram : Program := powerEncoderBlock.compile 0 ++ [.halt 0]

/-- Starting on literal signed bits in the documented input bank, the fixed encoder
halts with the exact opcode words for every exponent. All scalar inputs survive. -/
theorem powerEncoderProgram_correct (es : List ℤ) (input : List K) :
    ∃ k ≤ 12*(es.map fun e => e.natAbs.size+2).sum+6, ∃ tr : Fin (k+1) → State K,
      Trace powerEncoderProgram (start (powerEncoderAddressInput (signedBitTape es)) input) k tr ∧
      (tr (Fin.last k)).output = some 0 ∧
      (tr (Fin.last k)).index 0 = 8 ∧ (tr (Fin.last k)).index 1 = (productOps es).length+8 ∧
      (∀ i, ∀ hi : i < (productOps es).length,
        (tr (Fin.last k)).index (i+8) = (productOps es)[i].code) ∧
      ∀ j, (tr j).data = fun i => input[i]?.getD 0 := by
  let ts := signedBitTape es
  let d (i : ℕ) : K := input[i]?.getD 0
  have loc : CodeAt powerEncoderProgram 0 (powerEncoderBlock.compile 0) :=
    ⟨[],[.halt 0],rfl,rfl⟩
  obtain ⟨k,hk,ex⟩ := powerEncoderBlock_correct ts d loc
  let m := powerEncodedMemory ts d
  have hbody : Execution powerEncoderProgram (fun s => s.data = d)
      (start (powerEncoderAddressInput ts) input) k (m.atPC powerEncoderBlock.size) := by
    simpa only [start_encoder, Nat.zero_add] using ex
  have hh : step powerEncoderProgram (m.atPC powerEncoderBlock.size) =
      some {(m.atPC powerEncoderBlock.size) with output := some 0} := by
    have eqn : powerEncoderProgram[powerEncoderBlock.size]? = some (.halt 0) := by
      simp [powerEncoderProgram]
    simp [step, Memory.atPC, eqn, execInstr]
  have last := hbody.append (Execution.one hbody.safe_end hh hbody.safe_end)
  obtain ⟨tr,htr,he,hs⟩ := last.to_trace
  have hsize := signedBitTape_length es
  change ts.length = _ at hsize
  refine ⟨k+1,by omega,tr,htr,?_,?_,?_,?_,hs⟩
  · rw [he]
  · rw [he]; rfl
  · rw [he]
    change ((signedBitTape es).flatMap PowerToken.ops).length + 8 = _
    rw [expand_signedBitTape]
  · intro i hi
    rw [he]
    change encodedPowerTail ts i = _
    have heq : ts.flatMap PowerToken.ops = productOps es := expand_signedBitTape es
    have hi' : i < (ts.flatMap PowerToken.ops).length := by simpa only [heq] using hi
    simpa only [heq] using encodedPowerTail_code ts i hi'
end Compression
end LinearProgramming
end Optimization
end OAI
