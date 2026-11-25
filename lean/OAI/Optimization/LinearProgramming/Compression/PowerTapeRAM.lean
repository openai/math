import OAI.Optimization.LinearProgramming.Compression.PowerTape
import OAI.Optimization.LinearProgramming.RAM.Execution

/-! A uniform interpreter for the signed-power product instruction tape. Scalar inputs are
kept in a separate bank from the constructed five-opcode stream. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

/-- Program counter 0 fetches the next opcode. Register 2 contains the product. -/
def powerTapeProgram : Program :=
  [.branchAddrLT 0 1 1 19, .addrLoad 3 0, .incr 0 0,
   .branchAddrLT 3 4 7 4, .branchAddrLT 3 5 11 5, .branchAddrLT 3 6 13 6,
   .branchAddrLT 3 7 15 17, .load 0 2, .incr 2 2, .const 1 1, .jump 0,
   .mul 1 1 1, .jump 0, .mul 1 1 0, .jump 0, .div 1 3 1, .jump 0,
   .mul 2 2 1, .jump 0, .halt 0]

/-- The header contains both cursors, the stop address, opcode scratch and four
dispatch constants. All remaining entries are constructed opcode tags. -/
def powerTapeAddressInput (ops : List PowerOp) : List ℕ :=
  [8, ops.length+8, 4, 0, 1, 2, 3, 4] ++ ops.map PowerOp.code

def powerTapeScalarInput (bases : List ℚ) : List ℚ := [0, 1, 1, 1] ++ bases

private structure Work where
  base : ℚ
  power : ℚ
  product : ℚ
  cur : ℕ
  input : ℕ
  tag : ℕ

private def Work.fromMem (m : PowerMem) (cur input tag : ℕ) : Work :=
  ⟨m.base, m.power, m.product, cur, input, tag⟩

private def scalars (w : Work) (data : ℕ → ℚ) : ℕ → ℚ
  | 0 => w.base
  | 1 => w.power
  | 2 => w.product
  | 3 => 1
  | i+4 => data i

private def addresses (w : Work) (n : ℕ) (code : ℕ → ℕ) : ℕ → ℕ
  | 0 => w.cur+8
  | 1 => n+8
  | 2 => w.input+4
  | 3 => w.tag
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | i+8 => code i

private def frame (n : ℕ) (code : ℕ → ℕ) (data : ℕ → ℚ) (p : ℕ) (w : Work) : State ℚ :=
  ⟨p, scalars w data, addresses w n code, none⟩

private theorem scalar_update_base (w : Work) (data : ℕ → ℚ) (z : ℚ) :
    Function.update (scalars w data) 0 z = scalars {w with base := z} data := by
  funext j
  match j with | 0 | 1 | 2 | 3 | _+4 => rfl

private theorem scalar_update_power (w : Work) (data : ℕ → ℚ) (z : ℚ) :
    Function.update (scalars w data) 1 z = scalars {w with power := z} data := by
  funext j
  match j with | 0 | 1 | 2 | 3 | _+4 => rfl

private theorem scalar_update_product (w : Work) (data : ℕ → ℚ) (z : ℚ) :
    Function.update (scalars w data) 2 z = scalars {w with product := z} data := by
  funext j
  match j with | 0 | 1 | 2 | 3 | _+4 => rfl

private theorem advance_cur (w : Work) (n : ℕ) (code : ℕ → ℕ) :
    Function.update (addresses w n code) 0 (w.cur+8+1) =
      addresses {w with cur := w.cur+1} n code := by
  funext j
  match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem advance_input (w : Work) (n : ℕ) (code : ℕ → ℕ) :
    Function.update (addresses w n code) 2 (w.input+4+1) =
      addresses {w with input := w.input+1} n code := by
  funext j
  match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem fetch_tag (w : Work) (n : ℕ) (code : ℕ → ℕ) (z : ℕ) :
    Function.update (addresses w n code) 3 z = addresses {w with tag := z} n code := by
  funext j
  match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private def Within (w : Work) (B : ℕ) : Prop :=
  ratBits w.base ≤ B ∧ ratBits w.power ≤ B ∧ ratBits w.product ≤ B

private theorem frame_safe {n pc B : ℕ} {w : Work} {code : ℕ → ℕ} {data : ℕ → ℚ}
    (h : Within w B) (h₃ : 3 ≤ B) (hd : ∀ i, ratBits (data i) ≤ B) :
    scalarBound B (frame n code data pc w) := by
  intro i
  match i with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | 2 => exact h.2.2
  | 3 => exact h₃
  | i+4 => exact hd i

section Instructions
variable (n : ℕ) (code : ℕ → ℕ) (data : ℕ → ℚ) (w : Work)
local notation "F" => frame n code data

private theorem f0 : step powerTapeProgram (F 0 w) =
    some (F (if w.cur < n then 1 else 19) w) := by
  change some (F (if w.cur+8 < n+8 then 1 else 19) w) = _
  simp

private theorem f1 : step powerTapeProgram (F 1 w) =
    some (F 2 {w with tag := code w.cur}) := by
  change some (State.mk 2 _ (Function.update (addresses w n code) 3 (code w.cur)) _) = _
  rw [fetch_tag]
  rfl

private theorem f2 : step powerTapeProgram (F 2 w) =
    some (F 3 {w with cur := w.cur+1}) := by
  change some (State.mk 3 _ (Function.update (addresses w n code) 0 (w.cur+8+1)) _) = _
  rw [advance_cur]
  rfl

private theorem f3 : step powerTapeProgram (F 3 w) = some (F (if w.tag < 1 then 7 else 4) w) := rfl
private theorem f4 : step powerTapeProgram (F 4 w) = some (F (if w.tag < 2 then 11 else 5) w) := rfl
private theorem f5 : step powerTapeProgram (F 5 w) = some (F (if w.tag < 3 then 13 else 6) w) := rfl
private theorem f6 : step powerTapeProgram (F 6 w) = some (F (if w.tag < 4 then 15 else 17) w) := rfl

private theorem f7 : step powerTapeProgram (F 7 w) =
    some (F 8 {w with base := data w.input}) := by
  change some (State.mk 8 (Function.update (scalars w data) 0 (data w.input)) _ _) = _
  rw [scalar_update_base]
  rfl

private theorem f8 : step powerTapeProgram (F 8 w) =
    some (F 9 {w with input := w.input+1}) := by
  change some (State.mk 9 _ (Function.update (addresses w n code) 2 (w.input+4+1)) _) = _
  rw [advance_input]
  rfl

private theorem f9 : step powerTapeProgram (F 9 w) = some (F 10 {w with power := 1}) := by
  change some (State.mk 10 (Function.update (scalars w data) 1 (1 : ℚ)) _ _) = _
  rw [scalar_update_power]
  rfl

private theorem f10 : step powerTapeProgram (F 10 w) = some (F 0 w) := rfl

private theorem f11 : step powerTapeProgram (F 11 w) = some (F 12 {w with power := w.power*w.power}) := by
  change some (State.mk 12 (Function.update (scalars w data) 1 (w.power*w.power)) _ _) = _
  rw [scalar_update_power]
  rfl

private theorem f12 : step powerTapeProgram (F 12 w) = some (F 0 w) := rfl

private theorem f13 : step powerTapeProgram (F 13 w) = some (F 14 {w with power := w.power*w.base}) := by
  change some (State.mk 14 (Function.update (scalars w data) 1 (w.power*w.base)) _ _) = _
  rw [scalar_update_power]
  rfl

private theorem f14 : step powerTapeProgram (F 14 w) = some (F 0 w) := rfl

private theorem f15 (hn : w.power ≠ 0) : step powerTapeProgram (F 15 w) =
    some (F 16 {w with power := w.power⁻¹}) := by
  change (if w.power = 0 then none else
    some (State.mk 16 (Function.update (scalars w data) 1 (1/w.power)) _ _)) = _
  rw [ite_eq_right hn, one_div, scalar_update_power]
  rfl

private theorem f16 : step powerTapeProgram (F 16 w) = some (F 0 w) := rfl

private theorem f17 : step powerTapeProgram (F 17 w) = some (F 18 {w with product := w.product*w.power}) := by
  change some (State.mk 18 (Function.update (scalars w data) 2 (w.product*w.power)) _ _) = _
  rw [scalar_update_product]
  rfl

private theorem f18 : step powerTapeProgram (F 18 w) = some (F 0 w) := rfl

private theorem f19 : step powerTapeProgram (F 19 w) = some { F 19 w with output := some 0 } := rfl

end Instructions

private def handler : PowerOp → ℕ
  | .beginTerm => 7
  | .square => 11
  | .multiply => 13
  | .invert => 15
  | .commit => 17

private def dispatchSteps : PowerOp → ℕ
  | .beginTerm => 4
  | .square => 5
  | .multiply => 6
  | .invert | .commit => 7

private def bodySteps : PowerOp → ℕ
  | .beginTerm => 4
  | _ => 2

private theorem instruction_count (op : PowerOp) : dispatchSteps op + bodySteps op ≤ 9 := by
  cases op <;> decide

private def fetched (w : Work) (op : PowerOp) : Work :=
  { w with cur := w.cur+1, tag := op.code }

private theorem dispatch {B n : ℕ} (code : ℕ → ℕ) (data : ℕ → ℚ) (w : Work) (op : PowerOp)
    (hw : Within w B) (h₃ : 3 ≤ B) (hd : ∀ i, ratBits (data i) ≤ B)
    (hpos : w.cur < n) (hop : code w.cur = op.code) :
    Execution powerTapeProgram (scalarBound B) (frame n code data 0 w) (dispatchSteps op)
      (frame n code data (handler op) (fetched w op)) := by
  have h : scalarBound B (frame n code data 0 w) := frame_safe hw h₃ hd
  have read : Execution powerTapeProgram (scalarBound B) (frame n code data 0 w) 3
      (frame n code data 3 (fetched w op)) := by
    refine .next h (by simpa [hpos] using f0 n code data w) ?_
    refine .next h (by simpa only [hop] using f1 n code data w) ?_
    exact .next h (f2 ..) (.done _ h)
  cases op with
  | beginTerm =>
    exact read.append (.one h (f3 ..) h)
  | square =>
    exact read.append (.next h (f3 ..) (.one h (f4 ..) h))
  | multiply =>
    exact read.append (.next h (f3 ..) (.next h (f4 ..) (.one h (f5 ..) h)))
  | invert =>
    exact read.append (.next h (f3 ..) (.next h (f4 ..) (.next h (f5 ..) (.one h (f6 ..) h))))
  | commit =>
    exact read.append (.next h (f3 ..) (.next h (f4 ..) (.next h (f5 ..) (.one h (f6 ..) h))))

private def valAt (xs : List ℚ) (i : ℕ) : ℚ := xs[i]?.getD 0

private theorem valAt_of_drop {xs qs : List ℚ} {j : ℕ} {q : ℚ} (h : xs.drop j = q :: qs) :
    valAt xs j = q ∧ xs.drop (j+1) = qs := by
  have hhead := congrArg List.head? h
  have htail := congrArg List.tail h
  simp only [List.head?_drop, List.head?_cons] at hhead
  exact ⟨by simp [valAt, hhead], by simpa only [List.drop_add_one_eq_tail_drop, List.tail_cons] using htail⟩

private theorem handler_execution {B n : ℕ} (code : ℕ → ℕ) (bases : List ℚ)
    (cur j : ℕ) (op : PowerOp) (m m' : PowerMem) (hstep : op.step m = some m')
    (hr : bases.drop j = m.remaining) (h₃ : 3 ≤ B)
    (hdata : ∀ i, ratBits (valAt bases i) ≤ B)
    (hbase : ratBits m.base ≤ B) (hpow : ratBits m.power ≤ B) (hprod : ratBits m.product ≤ B)
    (hbase' : ratBits m'.base ≤ B) (hpow' : ratBits m'.power ≤ B) (hprod' : ratBits m'.product ≤ B) :
    ∃ j', bases.drop j' = m'.remaining ∧
      Execution powerTapeProgram (scalarBound B)
        (frame n code (valAt bases) (handler op) (Work.fromMem m cur j op.code)) (bodySteps op)
        (frame n code (valAt bases) 0 (Work.fromMem m' cur j' op.code)) := by
  have sf (m₀ : PowerMem) (hm₀ : Within (Work.fromMem m₀ 0 0 0) B) (p : ℕ) :
      scalarBound B (frame n code (valAt bases) p (Work.fromMem m₀ cur j op.code)) :=
    frame_safe hm₀ h₃ hdata
  have hm : Within (Work.fromMem m 0 0 0) B := ⟨hbase,hpow,hprod⟩
  have hm' : Within (Work.fromMem m' 0 0 0) B := ⟨hbase',hpow',hprod'⟩
  cases op with
  | beginTerm =>
    cases m with
    | mk b p v rem =>
      cases rem with
      | nil => contradiction
      | cons q qs =>
        have he : (⟨q,1,v,qs⟩ : PowerMem) = m' := Option.some.inj hstep
        subst m'
        obtain ⟨hb,ht⟩ := valAt_of_drop hr
        refine ⟨j+1, ht, .next (t := frame n code (valAt bases) 8
          (Work.fromMem ⟨q,p,v,qs⟩ cur j 0)) (sf _ hm _) ?_ ?_⟩
        · simpa only [Work.fromMem, handler, PowerOp.code, hb] using f7 n code (valAt bases) (Work.fromMem ⟨b,p,v,q::qs⟩ cur j 0)
        · have hmixed : Within (Work.fromMem ⟨q,p,v,qs⟩ 0 0 0) B :=
            ⟨hbase', hpow, hprod⟩
          refine .next (sf _ hmixed 8) (f8 ..) ?_
          refine .next (sf _ hmixed 9) (f9 ..) ?_
          exact .one (sf _ hm' 10) (f10 ..) (sf _ hm' 0)
  | square =>
    have he : {m with power := m.power*m.power} = m' := Option.some.inj hstep
    subst m'
    exact ⟨j, hr, .next (sf _ hm _) (f11 ..) (.one (sf _ hm' _) (f12 ..) (sf _ hm' _))⟩
  | multiply =>
    have he : {m with power := m.power*m.base} = m' := Option.some.inj hstep
    subst m'
    exact ⟨j, hr, .next (sf _ hm _) (f13 ..) (.one (sf _ hm' _) (f14 ..) (sf _ hm' _))⟩
  | invert =>
    by_cases hz : m.power = 0
    · simp [PowerOp.step, hz] at hstep
    · have he : {m with power := m.power⁻¹} = m' := by simpa [PowerOp.step, hz] using hstep
      subst m'
      exact ⟨j, hr, .next (sf _ hm _) (f15 _ _ _ _ hz) (.one (sf _ hm' _) (f16 ..) (sf _ hm' _))⟩
  | commit =>
    have he : {m with product := m.product*m.power} = m' := Option.some.inj hstep
    subst m'
    exact ⟨j, hr, .next (sf _ hm _) (f17 ..) (.one (sf _ hm' _) (f18 ..) (sf _ hm' _))⟩

private theorem interpret_ops {B n : ℕ} {safe : PowerMem → Prop}
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (h₃ : 3 ≤ B) (bases : List ℚ) (code : ℕ → ℕ) (hdata : ∀ i, ratBits (valAt bases i) ≤ B)
    {ops : List PowerOp} {m out : PowerMem} (h : PowerRun safe ops m out)
    (cur j old : ℕ) (hstop : cur + ops.length = n)
    (hr : bases.drop j = m.remaining)
    (htape : ∀ i, ∀ hi : i < ops.length, code (cur+i) = ops[i].code) :
    ∃ k x tag, k ≤ 9*ops.length ∧
      Execution powerTapeProgram (scalarBound B)
        (frame n code (valAt bases) 0 (Work.fromMem m cur j old)) k
        (frame n code (valAt bases) 0 (Work.fromMem out n x tag)) := by
  induction h generalizing cur j old with
  | nil m hm =>
    have e : cur = n := by simpa using hstop
    subst cur
    refine ⟨0,j,old,by simp,.done _ ?_⟩
    exact frame_safe (bound m hm) h₃ hdata
  | @cons op ops m next out hm hs tail ih =>
    have hn : cur < n := by simp only [List.length_cons] at hstop; omega
    have hcode : code cur = op.code := by
      have h0 := htape 0 (by simp)
      change code (cur+0) = op.code at h0
      simpa using h0
    have hbounds := bound m hm
    have nb := bound next tail.safe_start
    have d := dispatch (n := n) code (valAt bases) (Work.fromMem m cur j old) op
      hbounds h₃ hdata hn hcode
    obtain ⟨j', hrem, b⟩ := handler_execution (n := n) code bases (cur+1) j op m next
      hs hr h₃ hdata hbounds.1 hbounds.2.1 hbounds.2.2 nb.1 nb.2.1 nb.2.2
    have ht : ∀ i, ∀ hi : i < ops.length, code (cur+1+i) = ops[i].code := by
      intro i hi
      have h' := htape (i+1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'
    obtain ⟨k, x, tag, hk, r⟩ := ih (cur+1) j' op.code
      (by simp only [List.length_cons] at hstop; omega) hrem ht
    refine ⟨dispatchSteps op + bodySteps op + k, x, tag, ?_, (d.append b).append r⟩
    have hc := instruction_count op
    simp only [List.length_cons]
    omega

private def codeAt (xs : List PowerOp) (i : ℕ) : ℕ := ((xs.map PowerOp.code)[i]?).getD 0

private theorem start_frame (ops : List PowerOp) (bases : List ℚ) :
    start (powerTapeAddressInput ops) (powerTapeScalarInput bases) =
      frame ops.length (codeAt ops) (valAt bases) 0 (Work.fromMem (.initial bases) 0 0 0) := by
  unfold start frame
  congr 1
  · funext j
    match j with | 0 | 1 | 2 | 3 | _+4 => rfl
  · funext j
    match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl


/-- Header and scalar inputs required by the interpreter. Only the first `n` opcode
words are read, so another RAM subroutine may retain scratch data after that range. -/
def powerTapeEntry (n : ℕ) (bases : List ℚ) (tape : ℕ → ℕ) : State ℚ :=
  frame n tape (valAt bases) 0 (Work.fromMem (.initial bases) 0 0 0)

private theorem before_exit_with_tape {B : ℕ} {safe : PowerMem → Prop} {ops : List PowerOp}
    {bases : List ℚ} {out : PowerMem} (run : PowerRun safe ops (.initial bases) out)
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B)
    (tape : ℕ → ℕ) (hc : ∀ i, ∀ hi : i < ops.length, tape (0+i) = ops[i].code) :
    ∃ k x tag, k ≤ 9*ops.length + 1 ∧
      Execution powerTapeProgram (scalarBound B)
        (powerTapeEntry ops.length bases tape) k
        (frame ops.length tape (valAt bases) 19 (Work.fromMem out ops.length x tag)) := by
  have h₃ : 3 ≤ B := (bound _ run.safe_start).1
  have hd (j : ℕ) : ratBits (valAt bases j) ≤ B := by
    cases he : bases[j]? with
    | none =>
      simp only [valAt, he, Option.getD_none]
      exact h₃
    | some q => simpa only [valAt, he, Option.getD_some] using inputs q (List.mem_of_getElem? he)
  obtain ⟨k,x,tag,hk,body⟩ := interpret_ops (n := ops.length) bound h₃ bases tape hd run 0 0 0
    (by simp) (by rfl) hc
  have good := bound _ run.safe_end
  let w := Work.fromMem out ops.length x tag
  have exitStep : step powerTapeProgram (frame ops.length tape (valAt bases) 0 w) =
      some (frame ops.length tape (valAt bases) 19 w) := by
    simpa [w, Work.fromMem] using f0 ops.length tape (valAt bases) w
  refine ⟨k+1,x,tag,by omega,?_⟩
  exact body.append (Execution.one (frame_safe good h₃ hd) exitStep (frame_safe good h₃ hd))


private theorem before_exit {B : ℕ} {safe : PowerMem → Prop} {ops : List PowerOp}
    {bases : List ℚ} {out : PowerMem} (run : PowerRun safe ops (.initial bases) out)
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B) :
    ∃ k x tag, k ≤ 9*ops.length + 1 ∧
      Execution powerTapeProgram (scalarBound B)
        (start (powerTapeAddressInput ops) (powerTapeScalarInput bases)) k
        (frame ops.length (codeAt ops) (valAt bases) 19 (Work.fromMem out ops.length x tag)) := by
  rw [start_frame]
  apply before_exit_with_tape run bound inputs (codeAt ops)
  intro i hi
  simp [codeAt, hi]

/-- From the two explicitly encoded input banks the fixed program halts, returns the
specified product, and respects the given bit bound in every register and state. -/
theorem powerTapeProgram_correct {B : ℕ} {safe : PowerMem → Prop} {ops : List PowerOp}
    {bases : List ℚ} {out : PowerMem} (run : PowerRun safe ops (.initial bases) out)
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B) :
    ∃ k ≤ 9*ops.length+2, ∃ tr : Fin (k+1) → State ℚ,
      Trace powerTapeProgram (start (powerTapeAddressInput ops) (powerTapeScalarInput bases)) k tr ∧
      (tr (Fin.last k)).data 2 = out.product ∧ (tr (Fin.last k)).output = some 0 ∧
      ∀ i, scalarBound B (tr i) := by
  obtain ⟨k,x,tag,hk,body⟩ := before_exit run bound inputs
  have hs := body.safe_end
  let w := Work.fromMem out ops.length x tag
  have hh := Execution.one hs (f19 ops.length (codeAt ops) (valAt bases) w) hs
  obtain ⟨tr,ht,he,hsafe⟩ := (body.append hh).to_trace
  refine ⟨k+1,by omega,tr,ht,?_,?_,hsafe⟩
  · rw [he]; rfl
  · rw [he]

/-- The interpreter before its halt instruction. Appending a custom continuation places
its first instruction at address 19. -/
def powerTapeBody : Program := powerTapeProgram.take 19

private theorem step_from_live {p : Program} {s t : State ℚ} (h : step p s = some t) :
    s.output = none := by
  cases e : s.output with
  | none => rfl
  | some tag => simp [step, e] at h

private theorem live_before_end {p : Program} {safe : State ℚ → Prop} {s t : State ℚ} {k : ℕ}
    (e : Execution p safe s k t) (ht : t.output = none) : s.output = none := by
  cases e with
  | done => exact ht
  | next _ h _ => exact step_from_live h

private theorem same_running_step (suffix : Program) {s t : State ℚ}
    (e : step powerTapeProgram s = some t) (ht : t.output = none) :
    step (powerTapeBody ++ suffix) s = some t := by
  have hs := step_from_live e
  have hn : s.pc ≠ 19 := by
    intro hpc
    have h : some {s with output := some 0} = some t := by
      simpa only [step, hs, hpc, show powerTapeProgram[19]? = some (.halt 0) from rfl,
        execInstr] using e
    have hout := congrArg State.output (Option.some.inj h)
    simp [ht] at hout
  have hp : s.pc < powerTapeBody.length := by
    change s.pc < 19
    by_contra! h
    have hlen : powerTapeProgram.length ≤ s.pc := by change 20 ≤ s.pc; omega
    simp [step, hs, List.getElem?_eq_none hlen] at e
  have hlookup : (powerTapeBody ++ suffix)[s.pc]? = powerTapeProgram[s.pc]? := by
    rw [show powerTapeProgram = powerTapeBody ++ [.halt 0] from rfl,
      List.getElem?_append_left hp, List.getElem?_append_left hp]
  simpa only [step, hlookup] using e

private theorem replace_exit (suffix : Program) {safe : State ℚ → Prop} {s t : State ℚ} {k : ℕ}
    (e : Execution powerTapeProgram safe s k t) (ht : t.output = none) :
    Execution (powerTapeBody ++ suffix) safe s k t := by
  induction e with
  | done _ hs => exact .done _ hs
  | next hs h rest ih =>
    exact .next hs (same_running_step suffix h (live_before_end rest ht)) (ih ht)

/-- A caller can replace the halt instruction by arbitrary code. The interpreter
reaches its first instruction with the computed product and the unit register live. -/
theorem powerTapeProgram_prefix (suffix : Program) {B : ℕ} {safe : PowerMem → Prop}
    {ops : List PowerOp} {bases : List ℚ} {out : PowerMem}
    (run : PowerRun safe ops (.initial bases) out)
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B) :
    ∃ k ≤ 9*ops.length+1, ∃ s : State ℚ,
      Execution (powerTapeBody ++ suffix) (scalarBound B)
        (start (powerTapeAddressInput ops) (powerTapeScalarInput bases)) k s ∧
      s.pc = 19 ∧ s.output = none ∧ s.data 2 = out.product ∧ s.data 3 = 1 := by
  obtain ⟨k,x,tag,hk,h⟩ := before_exit run bound inputs
  exact ⟨k,hk,_,replace_exit suffix h rfl,rfl,rfl,rfl,rfl⟩

/-- The code prefix can execute on live memory prepared by a preceding subroutine.
The output cursor has passed the scalar header and the first dispatch constant remains one. -/
theorem powerTapeProgram_prefix_from_entry (suffix : Program) {B : ℕ} {safe : PowerMem → Prop}
    {ops : List PowerOp} {bases : List ℚ} {out : PowerMem}
    (run : PowerRun safe ops (.initial bases) out)
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B) (tape : ℕ → ℕ)
    (codes : ∀ i, ∀ hi : i < ops.length, tape i = ops[i].code) :
    ∃ k ≤ 9*ops.length+1, ∃ s : State ℚ,
      Execution (powerTapeBody ++ suffix) (scalarBound B) (powerTapeEntry ops.length bases tape) k s ∧
      s.pc = 19 ∧ s.output = none ∧ s.data 2 = out.product ∧ s.data 3 = 1 ∧
      4 ≤ s.index 2 ∧ s.index 4 = 1 := by
  obtain ⟨k,x,tag,hk,h⟩ := before_exit_with_tape run bound inputs tape (by simpa using codes)
  exact ⟨k,hk,_,replace_exit suffix h rfl,rfl,rfl,rfl,rfl, Nat.le_add_left _ _,rfl⟩

/-- The comparison suffix uses halt tags 0, 1, and 2 for less, equal, and greater. -/
def powerTapeCompareSuffix : Program :=
  [.branchLT 2 3 21 20, .branchLT 3 2 22 23, .halt 0, .halt 2, .halt 1]

def powerTapeCompareProgram : Program := powerTapeBody ++ powerTapeCompareSuffix

/-- The suffix compares the accumulator with one over any ordered field. It preserves
the scalar bank, so the caller's scalar invariant survives every comparison and halt. -/
theorem powerTapeCompareSuffix_exec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : (ℕ → K) → Prop} (s : State K) (hs : P s.data) (hp : s.pc = 19)
    (ho : s.output = none) (hu : s.data 3 = 1) :
    ∃ c ≤ 3, ∃ u : State K, Execution powerTapeCompareProgram (fun t => P t.data) s c u ∧
      u.output = some (if s.data 2 < 1 then 0 else if 1 < s.data 2 then 2 else 1) ∧
      u.data 2 = s.data 2 := by
  let go (pc : ℕ) := {s with pc := pc}
  have h19 : step powerTapeCompareProgram s =
      some (go (if s.data 2 < 1 then 21 else 20)) := by
    simp only [step, ho, hp,
      show powerTapeCompareProgram[19]? = some (.branchLT 2 3 21 20) from rfl, execInstr, hu, go]
  have h20 : step powerTapeCompareProgram (go 20) =
      some (go (if 1 < s.data 2 then 22 else 23)) := by
    simp only [step, go, ho,
      show powerTapeCompareProgram[20]? = some (.branchLT 3 2 22 23) from rfl, execInstr, hu]
  have haltAt (p tag : ℕ) (he : powerTapeCompareProgram[p]? = some (.halt tag)) :
      step powerTapeCompareProgram (go p) = some {go p with output := some tag} := by
    simp [step,go,ho,he,execInstr]
  by_cases hl : s.data 2 < 1
  · rw [ite_eq_left hl] at h19
    exact ⟨2,by decide,_,.next hs h19 (.one hs (haltAt 21 0 rfl) hs), by simp [hl], rfl⟩
  · rw [ite_eq_right hl] at h19
    by_cases hg : 1 < s.data 2
    · rw [ite_eq_left hg] at h20
      exact ⟨3,by decide,_,.next hs h19 (.next hs h20 (.one hs (haltAt 22 2 rfl) hs)),
        by simp [hl,hg], rfl⟩
    · rw [ite_eq_right hg] at h20
      exact ⟨3,by decide,_,.next hs h19 (.next hs h20 (.one hs (haltAt 23 1 rfl) hs)),
        by simp [hl,hg], rfl⟩

/-- A full RAM trace computes the product and compares it with one, including the
two comparisons and the actual halt instruction in the size and runtime guarantee. -/
theorem powerTapeCompareProgram_correct {B : ℕ} {safe : PowerMem → Prop}
    {ops : List PowerOp} {bases : List ℚ} {out : PowerMem}
    (run : PowerRun safe ops (.initial bases) out)
    (bound : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B) :
    ∃ k ≤ 9*ops.length+4, ∃ tr : Fin (k+1) → State ℚ,
      Trace powerTapeCompareProgram (start (powerTapeAddressInput ops) (powerTapeScalarInput bases)) k tr ∧
      (tr (Fin.last k)).data 2 = out.product ∧
      (tr (Fin.last k)).output = some (if out.product < 1 then 0 else if 1 < out.product then 2 else 1) ∧
      ∀ i, scalarBound B (tr i) := by
  obtain ⟨k,hk,s,body,hp,ho,hq,hu⟩ := powerTapeProgram_prefix powerTapeCompareSuffix run bound inputs
  obtain ⟨c,hc,u,tail,hflag,hval⟩ := powerTapeCompareSuffix_exec (P := fun data => ∀ j, ratBits (data j) ≤ B) s body.safe_end hp ho hu
  obtain ⟨tr,htr,he,hsafe⟩ := (body.append tail).to_trace
  refine ⟨k+c,by omega,tr,htr,?_,?_,hsafe⟩
  · rw [he, hval, hq]
  · rw [he, hflag, hq]
end Compression
end LinearProgramming
end Optimization
end OAI
