import OAI.Computability.VPVNP.PrimedCounterGuessFlow
import OAI.Computability.VPVNP.CompressorRecordScores
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval
import OAI.Computability.VPVNP.CompressorRecordChoices

/-!
# Native RAM admission for a compressor motif

Appendix E scans the outer indices of Theorem 6.1 in supply-edge order. This
finite instruction table reads each coordinate as a full machine word, checks
its cap, stores the payload, and accumulates the cleared quadratic score. Both
valid and rejected prefixes can be embedded in larger native programs. For a
complete call the successful streams are exactly the encodings admitted by
the motif inequality. The complete call reads the repetition count from persistent state and
computes its cap and energy limit using fixed motif coefficients.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open PrimedCounter.GuessWord

namespace MotifChoiceRAM

variable {w d p : ℕ}

/-- Registers 0–2 implement the word reader, register 3 holds the exclusive
coordinate cap, register 4 the running energy, and register 5 the exclusive
energy limit. The following registers retain the complete guessed vector. -/
def low (d : ℕ) (i : Fin 6) : Fin (6 + d) := i.castAdd d

/-- Register retaining guessed supply coordinate `i`, after the six reader and score registers. -/
def slot (i : Fin d) : Fin (6 + d) := i.natAdd 6

private def reader (d : ℕ) : Fin 3 ↪ Fin (6 + d) :=
  (Fin.castAddEmb 3).trans (Fin.castAddEmb d)

@[simp] private theorem low_eq_low {i j : Fin 6} : low d i = low d j ↔ i = j :=
  (Fin.castAddEmb d).injective.eq_iff

@[simp] private theorem slot_eq_slot {i j : Fin d} : slot i = slot j ↔ i = j :=
  (Fin.natAddEmb 6).injective.eq_iff

@[simp] private theorem low_ne_slot (i : Fin 6) (j : Fin d) : low d i ≠ slot j := by
  intro h
  have h' := congrArg Fin.val h
  change i.val = 6 + j.val at h'
  omega

@[simp] private theorem slot_ne_low (i : Fin 6) (j : Fin d) : slot j ≠ low d i := (low_ne_slot i j).symm

private theorem outside_reader (i : Fin 6) (hi : 3 ≤ i.val) : low d i ∉ Set.range (reader d) := by
  rintro ⟨j,h⟩
  have h' := congrArg Fin.val h
  change j.val = i.val at h'
  omega

private theorem slot_outside (i : Fin d) : slot i ∉ Set.range (reader d) := by
  rintro ⟨j,h⟩
  exact low_ne_slot (j.castAdd 3) i h

/-- The public datum at a coordinate is its fixed cleared quadratic coefficient.
Only the three numerical bounds/counters in the incoming registers depend on the call. -/
def coordinate (i : Fin d) : Flow (6+d) d :=
  let r := low d
  .seq (PrimedCounter.GuessWord.flow (reader d)) <|
  .seq (.line (.guardLt (r 0) (r 3))) <|
  .seq (.line (.copy (slot i) (r 0))) <|
  .seq (.line (.publicWord (r 1) i)) <|
  .seq (.line (.binary .mul (r 0) (r 0) (r 0))) <|
  .seq (.line (.binary .mul (r 0) (r 1) (r 0)))
       (.line (.binary .add (r 4) (r 4) (r 0)))

/-- The final comparison is performed even when the supply arity is zero. -/
def scan : List (Fin d) → Flow (6+d) d
  | [] => .line (.guardLt (low d 4) (low d 5))
  | i :: is => .seq (coordinate i) (scan is)

private theorem bits_append {w : ℕ} (es fs : List (Event w)) :
    choiceBits (es ++ fs) = choiceBits es ++ choiceBits fs := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [choiceBits, ih]

private theorem line_step {r k : ℕ} {M : Machine w p r k} {op : Op r k}
    {label : (Flow.line op).Label → Fin p} {stop bad : Fin p}
    (h : Flow.Linked M (.line op) label stop bad) (c : Config w p r)
    (hc : c.pc = label ()) :
    M.program.step c = ((op.emit stop bad).resize w).run M.publicData c := by
  change (M.code c.pc).run _ _ = _
  rw [hc, h.atLabel ()]
  rfl

private def entryPC {r k : ℕ} {M : Machine w p r k} {a : Flow r k}
    {label : a.Label → Fin p} {stop bad : Fin p} (_ : Flow.Linked M a label stop bad) : Fin p := label a.entry

/-- A successful coordinate choice executes the native eight-label word reader
and six deterministic instructions. The coordinate slot is retained for the descriptor. -/
theorem coordinate_prefix {M : Machine w p (6+d) d} {i : Fin d}
    {label : (coordinate i).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (coordinate i) label stop bad) (c : Config w p (6+d))
    (hpc : c.pc = label (coordinate i).entry) (v : Word w)
    (hcap : v < c.reg (low d 3)) :
    ∃ out es, Prefix M c es out ∧ es.length = 4*w+10 ∧ choiceBits es = wordBits v ∧
      out.pc = stop ∧ out.reg (low d 3) = c.reg (low d 3) ∧
      out.reg (low d 4) = c.reg (low d 4) + M.publicData i * (v*v) ∧
      out.reg (low d 5) = c.reg (low d 5) ∧
      (∀ j, out.reg (slot j) = if j = i then v else c.reg (slot j)) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let g := hc.seqRight
  let a := g.seqRight
  let b := a.seqRight
  let s := b.seqRight
  let t := s.seqRight
  obtain ⟨q,es,hpre,hlen,hbits,hq,hw,ho,hpriv,hstate⟩ := flow_native hc.seqLeft c hpc v
  change q.reg (low d 0) = v at hw
  have keep (j : Fin 6) (hj : 3 ≤ j.val) := ho _ (outside_reader j hj)
  have slots (j : Fin d) := ho _ (slot_outside j)
  have guard := line_step g.seqLeft q hq
  let qa : Config w p (6+d) := {q with pc := entryPC a}
  let qb := qa.put (entryPC b) (slot i) v
  let qs := qb.put (entryPC s) (low d 1) (M.publicData i)
  let qt := qs.put (entryPC t) (low d 0) (v*v)
  let qu := qt.put (entryPC t.seqRight) (low d 0) (M.publicData i * (v*v))
  let qf := qu.put stop (low d 4) (c.reg (low d 4) + M.publicData i * (v*v))
  have hg : M.program.step q = .localStep qa := by
    rw [guard]; simp only [Op.emit, Instr.resize, Instr.run, hw, keep 3 (by decide), hcap, ↓reduceIte]
    rfl
  have ha : M.program.step qa = .localStep qb := by
    rw [line_step a.seqLeft qa rfl]; simp only [Op.emit, Instr.resize, Instr.run, qa, hw]; rfl
  have hb : M.program.step qb = .localStep qs := by rw [line_step b.seqLeft qb rfl]; rfl
  have hs : M.program.step qs = .localStep qt := by
    rw [line_step s.seqLeft qs rfl]
    simp (config := {decide := true}) [Op.emit, Instr.resize, Instr.run, BinaryOp.eval, qt, qs, qb, qa,
      Config.put, hw, Function.update]
    rfl
  have ht : M.program.step qt = .localStep qu := by
    rw [line_step t.seqLeft qt rfl]
    simp (config := {decide := true}) [Op.emit, Instr.resize, Instr.run, BinaryOp.eval, qu, qt, qs,
      Config.put, Function.update]
    rfl
  have hu : M.program.step qu = .localStep qf := by
    rw [line_step t.seqRight qu rfl]
    simp (config := {decide := true}) [Op.emit, Instr.resize, Instr.run, BinaryOp.eval, qf, qu, qt, qs,
      qb, qa, Config.put, Function.update, keep 4 (by decide)]
  let ticks : List (Event w) := [.tick,.tick,.tick,.tick,.tick,.tick]
  have hticks : Prefix M q ticks qf := .tick hg (.tick ha (.tick hb (.tick hs (.tick ht (.tick hu (.nil _))))))
  refine ⟨qf, es ++ ticks, hpre.append hticks, ?_, ?_, rfl, ?_, by simp [qf], ?_, ?_, hpriv,hstate⟩
  · simp [ticks, hlen]
  · simp [ticks, bits_append, hbits, choiceBits]
  · simp (config := {decide := true}) [qf, qu, qt, qs, qb, qa, Config.put, Function.update, keep 3 (by decide)]
  · simp (config := {decide := true}) [qf, qu, qt, qs, qb, qa, Config.put, Function.update, keep 5 (by decide)]
  · intro j
    simp [qf, qu, qt, qs, qb, qa, Config.put, Function.update, slots]

/-- Full-word choices in the prescribed order of the descriptor scan. -/
def encoding (is : List (Fin d)) (v : Fin d → Word w) : List Bool :=
  is.flatMap (fun i => wordBits (v i))

/-- Energy is accumulated over the coordinates actually visited by the scan. -/
def score (is : List (Fin d)) (weights v : Fin d → Word w) : ℕ :=
  (is.map (fun i => (weights i).val * (v i).val ^ 2)).sum

/-- The accepting prefix uses one final guard and `4*w+10` native steps per
coordinate, and every visited slot holds exactly its encoded coordinate. -/
theorem scan_prefix {M : Machine w p (6+d) d} (is : List (Fin d))
    {label : (scan is).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (scan is) label stop bad) (c : Config w p (6+d))
    (hpc : c.pc = label (scan is).entry) (v : Fin d → Word w)
    (hcap : ∀ i ∈ is, v i < c.reg (low d 3))
    (hscore : (c.reg (low d 4)).val + score is M.publicData v < (c.reg (low d 5)).val) :
    ∃ out es, Prefix M c es out ∧ es.length = is.length * (4*w+10) + 1 ∧
      choiceBits es = encoding is v ∧ out.pc = stop ∧
      (out.reg (low d 4)).val = (c.reg (low d 4)).val + score is M.publicData v ∧
      (∀ j, out.reg (slot j) = if j ∈ is then v j else c.reg (slot j)) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction is generalizing c with
  | nil =>
    have ht : c.reg (low d 4) < c.reg (low d 5) := by simpa [score] using hscore
    have hs : M.program.step c = .localStep {c with pc := stop} := by
      rw [line_step hc c hpc]; simp [Op.emit, Instr.resize, Instr.run, ht]
    refine ⟨_, [.tick], .tick hs (.nil _), by simp, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · simp [score]
    · simp
  | cons i is ih =>
    obtain ⟨q,es,hpre,hlen,hbits,hq,hcap',hs,hlimit,hslots,hpriv,hstate⟩ :=
      coordinate_prefix hc.seqLeft c hpc (v i) (hcap i (by simp))
    have htotal := hscore
    simp only [score, List.map_cons, List.sum_cons] at htotal
    have hbound := (c.reg (low d 5)).isLt
    have hnew : (q.reg (low d 4)).val = (c.reg (low d 4)).val +
        (M.publicData i).val * (v i).val ^ 2 := by rw [hs]; apply scoreWord_exact; omega
    obtain ⟨out,fs,hpost,hflen,hfbits,ho,he,hvs,hp,ht⟩ := ih hc.seqRight q hq
      (fun j hj => hcap' ▸ hcap j (List.mem_cons_of_mem _ hj))
      (by rw [hnew,hlimit]; simpa [score, Nat.add_assoc] using htotal)
    refine ⟨out,es++fs,hpre.append hpost,?_,?_,ho,?_,?_,hp.trans hpriv,ht.trans hstate⟩
    · simp [hlen,hflen,Nat.add_mul]; omega
    · simp [bits_append,hbits,hfbits,encoding]
    · simp [he,hnew,score,Nat.add_assoc]
    · intro j
      by_cases hj : j ∈ is <;> by_cases hji : j = i <;> simp_all

/-- An out-of-range coordinate transfers to the actual rejecting continuation
immediately after the word read and its guard, before performing arithmetic. -/
theorem coordinate_reject {M : Machine w p (6+d) d} {i : Fin d}
    {label : (coordinate i).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (coordinate i) label stop bad) (c : Config w p (6+d))
    (hpc : c.pc = label (coordinate i).entry) (v : Word w)
    (hcap : ¬ v < c.reg (low d 3)) :
    ∃ out es, Prefix M c es out ∧ es.length = 4*w+5 ∧ choiceBits es = wordBits v ∧ out.pc = bad := by
  obtain ⟨q,es,hpre,hlen,hbits,hq,hw,ho,_⟩ := flow_native hc.seqLeft c hpc v
  change q.reg (low d 0) = v at hw
  have hg : M.program.step q = .localStep {q with pc := bad} := by
    rw [line_step hc.seqRight.seqLeft q hq]
    simp [Op.emit, Instr.resize, Instr.run, hw, ho _ (outside_reader 3 (by decide)), hcap]
  refine ⟨_,es ++ [.tick],hpre.append (.tick hg (.nil _)),?_,?_,rfl⟩
  · simp [hlen]
  · simp [bits_append,hbits,choiceBits]

/-- A rejected candidate reaches the rejecting label on a prefix of its encoding.
For candidates outside the coordinate box no fit assumption on their score is required. -/
theorem scan_reject {M : Machine w p (6+d) d} (is : List (Fin d))
    {label : (scan is).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (scan is) label stop bad) (c : Config w p (6+d))
    (hpc : c.pc = label (scan is).entry) (v : Fin d → Word w)
    (hfit : (∀ i ∈ is, v i < c.reg (low d 3)) →
      (c.reg (low d 4)).val + score is M.publicData v < 2 ^ w)
    (hfail : (∀ i ∈ is, v i < c.reg (low d 3)) →
      (c.reg (low d 5)).val ≤ (c.reg (low d 4)).val + score is M.publicData v) :
    ∃ out es rest, Prefix M c es out ∧ es.length ≤ is.length * (4*w+10) + 1 ∧
      encoding is v = choiceBits es ++ rest ∧ out.pc = bad := by
  induction is generalizing c with
  | nil =>
    have h := hfail (by simp)
    have ht : ¬ c.reg (low d 4) < c.reg (low d 5) := not_lt_of_ge (by simpa [score] using h)
    have hs : M.program.step c = .localStep {c with pc := bad} := by
      rw [line_step hc c hpc]; simp [Op.emit, Instr.resize, Instr.run, ht]
    exact ⟨_, [.tick], [], .tick hs (.nil _), by simp, rfl, rfl⟩
  | cons i is ih =>
    by_cases hv : v i < c.reg (low d 3)
    · obtain ⟨q,es,hpre,hlen,hbits,hq,hcap',hs,hlimit,_⟩ := coordinate_prefix hc.seqLeft c hpc _ hv
      have aux (h : ∀ j ∈ is, v j < q.reg (low d 3)) :
          (∀ j ∈ i :: is, v j < c.reg (low d 3)) ∧
          (q.reg (low d 4)).val + score is M.publicData v =
            (c.reg (low d 4)).val + score (i :: is) M.publicData v := by
        have hbox : ∀ j ∈ i :: is, v j < c.reg (low d 3) := by
          intro j hj; rcases List.mem_cons.mp hj with rfl | ht
          · exact hv
          · rw [← hcap']; exact h j ht
        refine ⟨hbox, ?_⟩
        have hf := hfit hbox
        simp only [score, List.map_cons, List.sum_cons] at hf ⊢
        rw [hs, scoreWord_exact _ _ _ (by omega), Nat.add_assoc]
      obtain ⟨out,fs,rest,hpost,hflen,hrest,ho⟩ := ih hc.seqRight q hq
        (fun h => (aux h).2 ▸ hfit (aux h).1) (fun h => by rw [hlimit, (aux h).2]; exact hfail (aux h).1)
      refine ⟨out, es++fs, rest, hpre.append hpost, ?_, ?_, ho⟩
      · simp only [List.length_append,hlen,List.length_cons,Nat.add_mul,Nat.one_mul]; omega
      · change wordBits (v i) ++ encoding is v = _
        rw [hrest, bits_append, hbits, List.append_assoc]
    · obtain ⟨q,es,hpre,hlen,hbits,hq⟩ := coordinate_reject hc.seqLeft c hpc _ hv
      refine ⟨q,es,encoding is v,hpre,?_,?_,hq⟩
      · simp only [hlen,List.length_cons,Nat.add_mul,Nat.one_mul]; omega
      · rw [hbits]; rfl

private theorem reject_at {r k : ℕ} (M : Machine w p r k) (c : Config w p r) (m : Memory w)
    (bits : List Bool) (fuel : ℕ) (h : M.code c.pc = .reject) : execute M.program fuel c m bits = none := by
  cases fuel <;> simp [execute,Machine.program,h,Instr.run]

private theorem score_mono (is : List (Fin d)) (weight v t : Fin d → Word w)
    (h : ∀ i ∈ is, v i ≤ t i) : score is weight v ≤ score is weight t := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (weight i).val * (v i).val ^ 2 + score is weight v ≤
      (weight i).val * (t i).val ^ 2 + score is weight t
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (h i (by simp)) _))
      (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

private theorem encoding_congr (is : List (Fin d)) {v t : Fin d → Word w} (h : ∀ i ∈ is, v i = t i) :
    encoding is v = encoding is t := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change wordBits (v i) ++ encoding is v = wordBits (t i) ++ encoding is t
    rw [h i (by simp), ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

private theorem score_congr (is : List (Fin d)) (weights : Fin d → Word w) {v t : Fin d → Word w}
    (h : ∀ i ∈ is, v i = t i) : score is weights v = score is weights t := by
  apply Nat.le_antisymm <;> apply score_mono
  · intro i hi; rw [h i hi]
  · intro i hi; rw [h i hi]

/-- Every successful machine stream consists of complete words, has exactly the
prescribed length, and passes both numerical tests. The fit condition covers the entire
box so that an overweight candidate cannot gain admission by wrapping around. -/
theorem scan_sound {M : Machine w p (6+d) d} (is : List (Fin d)) (hnd : is.Nodup)
    {label : (scan is).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (scan is) label stop bad) (hstop : M.code stop = .accept)
    (hbad : M.code bad = .reject) (c : Config w p (6+d)) (hpc : c.pc = label (scan is).entry)
    (mem : Memory w) (bits : List Bool)
    (hfit : (c.reg (low d 4)).val + score is M.publicData (fun _ => c.reg (low d 3)) < 2^w)
    (hrun : (execute M.program (is.length * (4*w+10) + 2) c mem bits).isSome) :
    ∃ v : Fin d → Word w, bits = encoding is v ∧ (∀ i ∈ is, v i < c.reg (low d 3)) ∧
      (c.reg (low d 4)).val + score is M.publicData v < (c.reg (low d 5)).val := by
  induction is generalizing c bits with
  | nil =>
    have hs := line_step hc c hpc
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add] at hrun
    rw [execute, hs] at hrun
    by_cases ht : c.reg (low d 4) < c.reg (low d 5)
    · have he : bits = [] := by
        cases bits <;> simp_all [Op.emit, Instr.resize, Instr.run, execute, Machine.program]
      exact ⟨fun _ => 0,he,by simp,by simpa [score] using ht⟩
    · simp [Op.emit, Instr.resize, Instr.run, ht, execute, Machine.program, hbad] at hrun
  | cons i is ih =>
    let tailFuel := is.length * (4*w+10) + 2
    by_cases short : bits.length < w
    · have hh := native_short (contains_flow hc.seqLeft.seqLeft) c hpc bits short
        ((i :: is).length * (4*w+10) + 2) mem
      rw [hh] at hrun; contradiction
    obtain ⟨x,hx⟩ := exists_wordBits (w := w) (bits.take w) (by simp [Nat.le_of_not_gt short])
    let tail := bits.drop w
    have hsplit : bits = wordBits x ++ tail := by rw [hx]; exact (List.take_append_drop w bits).symm
    by_cases hcap : x < c.reg (low d 3)
    · obtain ⟨q,es,hpre,hlen,hbits,hq,hcap',hs,hlimit,_⟩ := coordinate_prefix hc.seqLeft c hpc x hcap
      have hlen' : (i :: is).length * (4*w+10) + 2 = tailFuel + es.length := by
        simp [tailFuel,hlen,Nat.add_mul]; omega
      rw [hsplit, ← hbits, hlen', hpre.execute] at hrun
      have ht : (execute M.program tailFuel q mem tail).isSome := by simpa using hrun
      have headLe : (M.publicData i).val * x.val ^ 2 ≤
          (M.publicData i).val * (c.reg (low d 3)).val ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Fin.le_iff_val_le_val.mp hcap.le) _)
      have hfit' := hfit
      change (c.reg (low d 4)).val + ((M.publicData i).val * (c.reg (low d 3)).val ^ 2 +
        score is M.publicData (fun _ => c.reg (low d 3))) < 2^w at hfit'
      have hnew : (q.reg (low d 4)).val = (c.reg (low d 4)).val + (M.publicData i).val * x.val ^ 2 := by
        rw [hs]; apply scoreWord_exact; omega
      obtain ⟨v,he,hbox,hscore⟩ := ih (List.nodup_cons.mp hnd).2 hc.seqRight q hq tail
        (by rw [hnew,hcap']; omega) ht
      let v' := Function.update v i x
      have same (j : Fin d) (hj : j ∈ is) : v' j = v j :=
        Function.update_of_ne (by rintro rfl; exact (List.nodup_cons.mp hnd).1 hj) ..
      refine ⟨v',?_,?_,?_⟩
      · change bits = wordBits (v' i) ++ encoding is v'
        rw [encoding_congr is same, ← he]; simpa [v'] using hsplit
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | h
        · simpa [v'] using hcap
        · rw [same j h, ← hcap']; exact hbox j h
      · change (c.reg (low d 4)).val + ((M.publicData i).val * (v' i).val ^ 2 +
          score is M.publicData v') < _
        rw [score_congr is M.publicData same, ← Nat.add_assoc, ← hlimit]
        simpa [v',hnew] using hscore
    · obtain ⟨q,es,hpre,hlen,hbits,hq⟩ := coordinate_reject hc.seqLeft c hpc x hcap
      have hlen' : (i :: is).length * (4*w+10) + 2 = (tailFuel+5) + es.length := by
        simp [tailFuel,hlen,Nat.add_mul]; omega
      rw [hsplit, ← hbits, hlen', hpre.execute, reject_at M q mem tail _ (hq ▸ hbad)] at hrun
      contradiction

/-- Complete calls of the linked native scan are exactly the canonical encodings
of admitted vectors. Extra or truncated streams fail, including at zero supply arity. -/
theorem scan_execute_iff {M : Machine w p (6+d) d} (is : List (Fin d)) (hnd : is.Nodup)
    {label : (scan is).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (scan is) label stop bad) (hstop : M.code stop = .accept)
    (hbad : M.code bad = .reject) (c : Config w p (6+d)) (hpc : c.pc = label (scan is).entry)
    (mem : Memory w) (bits : List Bool)
    (hfit : (c.reg (low d 4)).val + score is M.publicData (fun _ => c.reg (low d 3)) < 2^w) :
    (execute M.program (is.length * (4*w+10) + 2) c mem bits).isSome ↔
      ∃ v : Fin d → Word w, bits = encoding is v ∧ (∀ i ∈ is, v i < c.reg (low d 3)) ∧
        (c.reg (low d 4)).val + score is M.publicData v < (c.reg (low d 5)).val := by
  refine ⟨scan_sound is hnd hc hstop hbad c hpc mem bits hfit, ?_⟩
  rintro ⟨v,rfl,hcap,hscore⟩
  obtain ⟨out,es,hpre,hlen,hbits,hout,_⟩ := scan_prefix is hc c hpc v hcap hscore
  have he := hpre.execute 1 mem []
  simp only [List.append_nil, hbits, hlen] at he
  rw [show is.length * (4*w+10) + 2 = 1 + (is.length * (4*w+10) + 1) by omega, he]
  simp [execute, Machine.program, hout, hstop, Instr.run]

/-- The native prefix consists entirely of private ticks and binary choices. -/
theorem prefix_probes {r k : ℕ} {M : Machine w p r k} {c out : Config w p r} {es : List (Event w)}
    (h : Prefix M c es out) : countProbes es = 0 := by
  induction h with
  | nil => rfl
  | tick _ _ ih | choice _ _ ih => exact ih

/-- With supply slots in numerical order the scan consumes the concatenation
of the little-endian word representations, including leading zero bits. -/
theorem full_encoding (v : Fin d → Word w) :
    encoding (List.finRange d) v = (List.ofFn (fun i => wordBits (v i))).flatten := by
  simp [encoding, List.flatMap_def, List.finRange, List.map_ofFn, Function.comp_def]

/-- The public quadratic coefficients include the squared radius denominator;
the accumulator therefore computes the complete left side of the admission test. -/
theorem full_score {S : Type*} [Fintype S] (order : Fin d ≃ S) (q : S → ℚ) (R : ℚ)
    (weights v : Fin d → Word w)
    (hweights : ∀ i, (weights i).val = MotifAdmission.weight q (order i) * R.den ^ 2) :
    score (List.finRange d) weights v =
      MotifAdmission.energy q (fun e => (v (order.symm e)).val) * R.den ^ 2 := by
  simp only [score, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_apply, hweights,
    MotifAdmission.energy, Finset.sum_mul]
  rw [← order.sum_comp (fun e => MotifAdmission.weight q e * (v (order.symm e)).val ^ 2 * R.den ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Equiv.symm_apply_apply]
  ring

/-- With positive supply masses and representable bounds, acceptance of the actual
machine agrees with the integer admission test used in the outer sum of Theorem 6.1. -/
theorem scan_admit_iff {S : Type*} [Fintype S] (order : Fin d ≃ S) (q : S → ℚ)
    (hq : ∀ e, 0 < q e) (u L : ℕ) (R : ℚ) {M : Machine w p (6+d) d}
    {label : (scan (List.finRange d)).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (scan (List.finRange d)) label stop bad) (hstop : M.code stop = .accept)
    (hbad : M.code bad = .reject) (c : Config w p (6+d)) (hpc : c.pc = label (scan (List.finRange d)).entry)
    (hweights : ∀ i, (M.publicData i).val = MotifAdmission.weight q (order i) * R.den ^ 2)
    (hcap : (c.reg (low d 3)).val = MotifAdmission.payloadCap q u L R + 1)
    (hzero : (c.reg (low d 4)).val = 0)
    (hlimit : (c.reg (low d 5)).val = (u * L * R.num.natAbs) ^ 2 * MotifAdmission.denominator q + 1)
    (hfit : score (List.finRange d) M.publicData (fun _ => c.reg (low d 3)) < 2^w)
    (mem : Memory w) (bits : List Bool) :
    (execute M.program (d * (4*w+10) + 2) c mem bits).isSome ↔
      ∃ v : Fin d → Word w, bits = encoding (List.finRange d) v ∧
        MotifAdmission.admit q (fun e => (v (order.symm e)).val) u L R = true := by
  have he := scan_execute_iff (List.finRange d) (List.nodup_finRange _) hc hstop hbad c hpc mem bits
    (by simpa [hzero] using hfit)
  simp only [List.length_finRange, hzero, Nat.zero_add, hlimit, Nat.lt_succ_iff] at he
  rw [he]
  apply exists_congr
  intro v
  rw [full_score order q R M.publicData v hweights]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨_,hv⟩; exact decide_eq_true hv
  · intro hv
    refine ⟨?_, of_decide_eq_true hv⟩
    intro i _
    apply Fin.lt_def.mpr
    rw [hcap, Nat.lt_succ_iff]
    simpa using MotifAdmission.payload_le_cap q hq (fun e => (v (order.symm e)).val) u L R hv (order i)

end MotifChoiceRAM
end CompressorRecords

namespace CompressorRecords.MotifChoiceRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter.GuessWord

variable {n w pcCount : ℕ}

/-- The unit term has no payload. Write the zero descriptor without guessing
bits, even when the incoming register file still holds the preceding motif. -/
def unitSlots : List (Fin n) → Flow (6 + n) n
  | [] => .line (.constant (low n 4) 0)
  | i :: rest => .seq (.line (.constant (slot i) 0)) (unitSlots rest)

private theorem constantStep {M : Machine w pcCount (6 + n) n} {dst : Fin (6 + n)}
    {label : (Flow.line (k := n) (.constant dst 0)).Label → Fin pcCount} {stop bad : Fin pcCount}
    (hc : Flow.Linked M (.line (.constant dst 0)) label stop bad) (c : Config w pcCount (6+n))
    (hpc : c.pc = label ()) :
    M.program.step c = .localStep (c.put stop dst 0) := by
  change (M.code c.pc).run _ _ = _
  rw [hpc, hc.atLabel ()]
  rfl

theorem unitSlots_prefix {M : Machine w pcCount (6+n) n} (is : List (Fin n))
    {label : (unitSlots is).Label → Fin pcCount} {stop bad : Fin pcCount}
    (hc : Flow.Linked M (unitSlots is) label stop bad) (c : Config w pcCount (6+n))
    (hpc : c.pc = label (unitSlots is).entry) :
    ∃ out es, Prefix M c es out ∧ es.length = is.length + 1 ∧ choiceBits es = [] ∧
      out.pc = stop ∧ (∀ j, out.reg (slot j) = if j ∈ is then 0 else c.reg (slot j)) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction is generalizing c with
  | nil =>
    have h := constantStep hc c hpc
    refine ⟨_, [.tick], .tick h (.nil _), rfl, rfl, rfl, ?_, rfl, rfl⟩
    intro j
    have hn : slot j ≠ low n 4 := by
      intro he
      have hval := congrArg Fin.val he
      change 6 + j.val = 4 at hval
      omega
    simp [Config.put, hn]
  | cons i is ih =>
    let q := c.put (label (.inr (unitSlots is).entry)) (slot i) 0
    have hs : M.program.step c = .localStep q := constantStep hc.seqLeft c hpc
    obtain ⟨out,es,hpre,hlen,hbits,hdone,hslot,hpriv,hpersist⟩ := ih hc.seqRight q rfl
    refine ⟨out, .tick :: es, .tick hs hpre, by simp [hlen], hbits, hdone, ?_, hpriv, hpersist⟩
    intro j
    rw [hslot]
    by_cases hj : j ∈ is
    · simp [hj]
    · by_cases he : j = i
      · subst j
        simp [hj, q, Config.put]
      · have hne : slot j ≠ slot i := fun h => he ((Fin.natAddEmb 6).injective h)
        simp [hj, he, q, Config.put, hne]

/-- The repetition count arrives in scratch register two, and the energy
accumulator in register four starts at zero. Both branches have fixed code. -/
def choosePayload (n : ℕ) : Flow (6+n) n :=
  .ifEq (low n 2) (low n 4) (unitSlots (List.finRange n)) (scan (List.finRange n))

private theorem dispatchStep {M : Machine w pcCount (6+n) n} {label : (choosePayload n).Label → Fin pcCount}
    {stop bad : Fin pcCount} (hc : Flow.Linked M (choosePayload n) label stop bad)
    (c : Config w pcCount (6+n)) (hpc : c.pc = label (choosePayload n).entry) :
    let dest := if c.reg (low n 2) = c.reg (low n 4) then
      label (.inr (.inl (unitSlots (List.finRange n)).entry)) else
      label (.inr (.inr (scan (List.finRange n)).entry))
    M.program.step c = .localStep {c with pc := dest} := by
  change (M.code c.pc).run _ _ = _
  rw [hpc, hc.atLabel _]
  rfl

theorem choosePayload_unit {M : Machine w pcCount (6+n) n} {label : (choosePayload n).Label → Fin pcCount}
    {stop bad : Fin pcCount} (hc : Flow.Linked M (choosePayload n) label stop bad)
    (c : Config w pcCount (6+n)) (hpc : c.pc = label (choosePayload n).entry)
    (hzero : c.reg (low n 2) = c.reg (low n 4)) :
    ∃ out es, Prefix M c es out ∧ es.length = n + 2 ∧ choiceBits es = [] ∧ out.pc = stop ∧
      (∀ i, out.reg (slot i) = 0) ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let next := {c with pc := label (.inr (.inl (unitSlots (List.finRange n)).entry))}
  have hs : M.program.step c = .localStep next := by simp [dispatchStep hc c hpc, hzero, next]
  obtain ⟨out, es, hp, hl, hb, ho, hslot, hpriv, hpersist⟩ := unitSlots_prefix _ hc.ifEqYes next rfl
  exact ⟨out, .tick :: es, .tick hs hp, by simp [hl], hb, ho, fun i => by simpa using hslot i, hpriv, hpersist⟩

theorem choosePayload_vector {M : Machine w pcCount (6+n) n} {label : (choosePayload n).Label → Fin pcCount}
    {stop bad : Fin pcCount} (hc : Flow.Linked M (choosePayload n) label stop bad)
    (c : Config w pcCount (6+n)) (hpc : c.pc = label (choosePayload n).entry)
    (hpos : c.reg (low n 2) ≠ c.reg (low n 4)) (v : Fin n → Word w)
    (hcap : ∀ i, v i < c.reg (low n 3)) (hscore : (c.reg (low n 4)).val +
      score (List.finRange n) M.publicData v < (c.reg (low n 5)).val) :
    ∃ out es, Prefix M c es out ∧ es.length = n * (4*w+10) + 2 ∧
      choiceBits es = encoding (List.finRange n) v ∧ out.pc = stop ∧
      (∀ i, out.reg (slot i) = v i) ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let next := {c with pc := label (.inr (.inr (scan (List.finRange n)).entry))}
  have hs : M.program.step c = .localStep next := by simp [dispatchStep hc c hpc, hpos, next]
  obtain ⟨out, es, hp, hl, hb, ho, _, hslot, hpriv, hpersist⟩ :=
    scan_prefix _ hc.ifEqNo next rfl v (fun i _ => hcap i) hscore
  exact ⟨out, .tick :: es, .tick hs hp, by simp [hl], hb, ho, fun i => by simpa using hslot i, hpriv, hpersist⟩

open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- The native call's complete streams are exactly those of the outer-index
reader, including the unit branch. All bound checks take place on machine
words whose exact numerical contents are given by the register hypotheses. -/
theorem choosePayload_execute_iff (order : Fin n ≃ S) (hq : ∀ e, 0 < q e) (demand : D → ℕ)
    {M : Machine w pcCount (6+n) n} {label : (choosePayload n).Label → Fin pcCount}
    {stop bad : Fin pcCount} (hc : Flow.Linked M (choosePayload n) label stop bad)
    (hstop : M.code stop = .accept) (hbad : M.code bad = .reject) (c : Config w pcCount (6+n))
    (hpc : c.pc = label (choosePayload n).entry)
    (hweights : ∀ i, (M.publicData i).val = MotifAdmission.weight q (order i) * B.radius.den ^ 2)
    (hreps : (c.reg (low n 2)).val = repetitions B demand)
    (hcap : (c.reg (low n 3)).val = outerCap B demand + 1)
    (hzero : (c.reg (low n 4)).val = 0)
    (hlimit : (c.reg (low n 5)).val =
      (repetitions B demand * B.scale * B.radius.num.natAbs) ^ 2 * MotifAdmission.denominator q + 1)
    (hfit : score (List.finRange n) M.publicData (fun _ => c.reg (low n 3)) < 2^w)
    (mem : Memory w) (bits : List Bool) :
    let hw : outerCap B demand < 2^w := by have _hv := (c.reg (low n 3)).isLt; omega
    (execute M.program (n * (4*w+10) + 3) c mem bits).isSome ↔
      ∃ v, (outerReader B order hq demand w hw).read bits = some (v, []) := by
  dsimp only
  have hcfit : outerCap B demand < 2 ^ w := by have _hv := (c.reg (low n 3)).isLt; omega
  by_cases hu : repetitions B demand = 0
  · have hz : c.reg (low n 2) = c.reg (low n 4) := Fin.ext (hreps.trans (hu.trans hzero.symm))
    obtain ⟨out, es, hp, hl, hb, ho, _⟩ := choosePayload_unit hc c hpc hz
    have hlen : es.length ≤ n * (4*w+10) + 2 := by
      have h := Nat.le_mul_of_pos_right n (by omega : 0 < 4*w+10)
      omega
    let extra := n * (4*w+10) + 2 - es.length
    have hrun := hp.execute (extra + 1) mem bits
    simp only [hb, List.nil_append] at hrun
    rw [show n * (4*w+10) + 3 = extra + 1 + es.length by dsimp [extra]; omega, hrun]
    have hstopRun : M.program.step out = .finish none := by simp [Machine.program, ho, hstop, Instr.run]
    have empty (v : ↥(outerIndices B demand)) : (outerReader B order hq demand w hcfit).encode v = [] := by
      apply List.length_eq_zero_iff.mp
      simp [outerReader_length, coordinateBits, hu]
    have h₀ : (fun _ => 0) ∈ outerIndices B demand := (mem_outerIndices_iff B hq _ _).mpr (by
      simp [MotifAdmission.admit, MotifAdmission.energy])
    simp only [execute, hstopRun, ChoiceReader.read_iff, List.append_nil]
    by_cases hbits : bits = []
    · simpa [hbits, empty] using (show ∃ a, a ∈ outerIndices B demand from ⟨_, h₀⟩)
    · simp [hbits, empty]
  · have hn : c.reg (low n 2) ≠ c.reg (low n 4) := fun he => hu (hreps.symm.trans ((congrArg Fin.val he).trans hzero))
    let next := {c with pc := label (.inr (.inr (scan (List.finRange n)).entry))}
    have hs : M.program.step c = .localStep next := by simp [dispatchStep hc c hpc, hn, next]
    have hm := scan_admit_iff order q hq (repetitions B demand) B.scale B.radius hc.ifEqNo hstop hbad next rfl
      hweights hcap hzero hlimit hfit mem bits
    rw [execute, hs, Option.isSome_map, hm]
    constructor
    · rintro ⟨v, rfl, hv⟩
      let a := fun e => (v (order.symm e)).val
      refine ⟨⟨a, (mem_outerIndices_iff B hq _ _).mpr hv⟩, (read_outer_iff B order hq demand w hcfit _ _ _).mpr ?_⟩
      rw [show coordinateBits B demand w = w from ite_eq_right hu, full_encoding, List.append_nil]
      congr 2
      funext i
      simp [a, PrimedCounter.digits]
    · rintro ⟨v, hr⟩
      have hadm := (mem_outerIndices_iff B hq _ _).mp v.property
      let z (i : Fin n) : BurstRAM.Word w := ⟨v.val (order i), (MotifAdmission.payload_le_cap q hq _ _ _ _ hadm _).trans_lt hcfit⟩
      refine ⟨z, ?_, ?_⟩
      · have he := (read_outer_iff B order hq demand w hcfit bits [] v).mp hr
        rw [he, full_encoding, List.append_nil]
        simp only [coordinateBits, hu, ↓reduceIte]
        congr 2
        funext i
        apply congrArg BurstRAM.wordBits
        exact Fin.ext (Nat.mod_eq_of_lt (z i).isLt)
      · simpa [z] using hadm

/-- For fixed rational motif data a constant plus twice the binary logarithm of
`M+1` suffices for the entire native reader. This covers the one-past guards,
all public weights, and the largest energy considered in the overflow proof. -/
theorem native_word_fit {D S : Type*} [Fintype D] [Fintype S]
    (p : D → ℚ) (q : S → ℚ) (L : ℕ) (hL : 0 < L) (R : ℚ) :
    ∃ K : ℕ, ∀ (M : ℕ) (b : D → ℕ), (∀ i, b i ≤ M) →
      let u := MotifAdmission.copies p b L
      let box := MotifAdmission.payloadCap q u L R + 1
      let limit := (u * L * R.num.natAbs) ^ 2 * MotifAdmission.denominator q + 1
      let modulus := 2 ^ (K + 2 * Nat.clog 2 (M + 1))
      u < modulus ∧ box < modulus ∧ limit < modulus ∧
        MotifAdmission.energy q (fun _ => box) * R.den ^ 2 < modulus ∧
        ∀ e, MotifAdmission.weight q e * R.den ^ 2 < modulus := by
  let U := (∑ i, MotifAdmission.weight p i) + 1
  let V := U * L * R.num.natAbs * MotifAdmission.denominator q
  let A := max U (V + 1)
  let B := (∑ e, MotifAdmission.weight q e) * A ^ 2 * R.den ^ 2
  let C := (A * L * R.num.natAbs) ^ 2 * MotifAdmission.denominator q
  let total := A + B + C + 1
  refine ⟨total.size, fun M b hb => ?_⟩
  dsimp only
  let u := MotifAdmission.copies p b L
  let box := MotifAdmission.payloadCap q u L R + 1
  have hu : u ≤ A * (M+1) := (MotifAdmission.copies_le p b L M hL hb).trans
    (Nat.mul_le_mul_right _ (le_max_left U (V+1)))
  have hcap : MotifAdmission.payloadCap q u L R ≤ V * (M+1) :=
    MotifAdmission.payloadCap_le p q b L M R hL hb
  have hbox : box ≤ A * (M+1) := calc
    box ≤ (V+1) * (M+1) := by dsimp [box]; rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ A * (M+1) := Nat.mul_le_mul_right _ (le_max_right U (V+1))
  obtain ⟨hleft,hright⟩ := MotifAdmission.admit_operands_le q (fun _ => box) u L R A M hu (fun _ => hbox)
  change MotifAdmission.energy q (fun _ => box) * R.den ^ 2 ≤ B * (M+1)^2 at hleft
  change (u * L * R.num.natAbs) ^ 2 * MotifAdmission.denominator q ≤ C * (M+1)^2 at hright
  have fit (x c : ℕ) (hc : c ≤ total) (hx : x ≤ c * (M+1)^2) : x < 2^(total.size + 2 * Nat.clog 2 (M+1)) :=
    Nat.size_le.mp (MotifAdmission.operand_bits_le x total M (hx.trans (Nat.mul_le_mul_right _ hc)))
  have grow : A * (M+1) ≤ A * (M+1)^2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)
  have positive : 0 < (M+1)^2 := by positivity
  refine ⟨fit u A (by dsimp [total]; omega) (hu.trans grow),
    fit box A (by dsimp [total]; omega) (hbox.trans grow),
    fit _ (C+1) (by dsimp [total]; omega) ?_,
    fit _ B (by dsimp [total]; omega) hleft, ?_⟩
  · change (u * L * R.num.natAbs) ^ 2 * MotifAdmission.denominator q + 1 ≤ (C+1) * (M+1)^2
    rw [Nat.add_mul, Nat.one_mul]; omega
  · intro e
    apply fit _ B (by dsimp [total]; omega)
    apply le_trans _ hleft
    apply Nat.mul_le_mul_right
    calc
      MotifAdmission.weight q e ≤ MotifAdmission.weight q e * box ^ 2 :=
        Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _)
      _ ≤ MotifAdmission.energy q (fun _ => box) :=
        Finset.single_le_sum (f := fun i => MotifAdmission.weight q i * box ^ 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)

end CompressorRecords.MotifChoiceRAM

namespace CompressorRecords.MotifChoiceRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {r k w d : ℕ}

/-- Multiply by a coefficient built into the fixed instruction table in binary.
The source survives, and the destination is initialized afresh. -/
def scaleDigits (dst src : Fin r) : List Bool → Flow r k
  | [] => .line (.constant dst 0)
  | b :: bs =>
    let double := Flow.line (.binary .add dst dst dst)
    let addSrc := Flow.line (.binary .add dst dst src)
    .seq (scaleDigits dst src bs) (if b then double.seq addSrc else double)

/-- Encode fixed motif coefficients in the code, independently of the actual
machine word width or the length-dependent public data. -/
def scaleFixed (dst src : Fin r) (n : ℕ) : Flow r k :=
  scaleDigits dst src (wordBits (⟨n, Nat.lt_size_self n⟩ : Word n.size))

private abbrev Straight {r k w : ℕ} (pub : Fin k → Word w) (state : Word w) (mem : Memory w)
    (code : Flow r k) (rs rs' : Regs w r) :=
  Flow.Exec pub state code rs mem (List.replicate code.length .tick) rs' mem

private theorem seq_straight {pub : Fin k → Word w} {state : Word w} {mem : Memory w}
    {a b : Flow r k} {x y z : Regs w r} (h : Straight pub state mem a x y) (h' : Straight pub state mem b y z) :
    Straight pub state mem (a.seq b) x z := by
  simpa only [Straight, Flow.length, List.replicate_add] using Flow.Exec.seq h h'

private theorem scaleDigits_straight (dst src : Fin r) (hds : src ≠ dst) (digits : List Bool)
    (pub : Fin k → Word w) (state : Word w) (mem : Memory w) (rs : Regs w r) :
    Straight pub state mem (scaleDigits dst src digits) rs
      (Function.update rs dst (rs src * (value digits : Word w))) := by
  induction digits with
  | nil =>
    apply Flow.Exec.line
    simp [Op.effect, value]
  | cons b bs ih =>
    let t := rs src * (value bs : Word w)
    let mid := Function.update rs dst t
    have hs : Straight pub state mem (.line (.binary .add dst dst dst)) mid
        (Function.update rs dst (t+t)) := by
      apply Flow.Exec.line
      simp [Op.effect, BinaryOp.eval, mid]
    cases b with
    | false =>
      apply seq_straight ih
      have hval : rs src * (value (false :: bs) : Word w) = t+t := by simp [value, t]; ring
      rw [hval]; exact hs
    | true =>
      apply seq_straight ih
      apply seq_straight hs
      have hval : rs src * (value (true :: bs) : Word w) = t+t+rs src := by simp [value, t]; ring
      rw [hval]
      apply Flow.Exec.line
      simp [Op.effect, BinaryOp.eval, hds]

theorem scaleFixed_length (dst src : Fin r) (n : ℕ) : (scaleFixed (k := k) dst src n).length ≤ 2*n.size+1 := by
  have digits (bs : List Bool) : (scaleDigits (k := k) dst src bs).length ≤ 2 * bs.length + 1 := by
    induction bs with
    | nil => simp [scaleDigits, Flow.length]
    | cons b bs ih => cases b <;> simp [scaleDigits, Flow.length] <;> omega
  simpa [scaleFixed] using digits (wordBits (⟨n,Nat.lt_size_self n⟩ : Word n.size))

private theorem scaleFixed_straight (dst src : Fin r) (hds : src ≠ dst) (n : ℕ)
    (pub : Fin k → Word w) (state : Word w) (mem : Memory w) (rs : Regs w r) :
    Straight pub state mem (scaleFixed dst src n) rs (Function.update rs dst (rs src * (n : Word w))) := by
  simpa only [scaleFixed, value_wordBits] using
    scaleDigits_straight dst src hds (wordBits (⟨n,Nat.lt_size_self n⟩ : Word n.size)) pub state mem rs

/-- The input repetition word is register 2. The code sets register 3 to one
past the coordinate cap, register 5 to one past the energy limit, and clears
the scratch and energy registers before dispatching on the repetition word. -/
def prepareBounds (d : ℕ) (factor denominator : ℕ) : Flow (6+d) d :=
  let r := low d
  .seq (scaleFixed (r 4) (r 2) factor) <|
  .seq (scaleFixed (r 3) (r 4) denominator) <|
  .seq (.line (.binary .mul (r 1) (r 4) (r 4))) <|
  .seq (scaleFixed (r 5) (r 1) denominator) <|
  .seq (.line (.constant (r 0) 1)) <|
  .seq (.line (.binary .add (r 3) (r 3) (r 0))) <|
  .seq (.line (.binary .add (r 5) (r 5) (r 0))) <|
  .seq (.line (.constant (r 4) 0)) <|
  .seq (.line (.constant (r 0) 0))
       (.line (.constant (r 1) 0))

/-- Constant instruction cost for a fixed motif. Only the binary lengths of the
fixed coefficients enter the bound, independently of the word size and of `u`. -/
theorem prepareBounds_length (d factor denominator : ℕ) :
    (prepareBounds d factor denominator).length ≤ 2*factor.size + 4*denominator.size + 10 := by
  have ha := scaleFixed_length (k := d) (low d 4) (low d 2) factor
  have hb := scaleFixed_length (k := d) (low d 3) (low d 4) denominator
  have hc := scaleFixed_length (k := d) (low d 5) (low d 1) denominator
  simp only [prepareBounds,Flow.length]; omega

private theorem binary_straight (pub : Fin k → Word w) (s : Word w) (m : Memory w) (rs : Regs w r)
    (op : BinaryOp) (dst x y : Fin r) : Straight pub s m (.line (.binary op dst x y)) rs
      (Function.update rs dst (op.eval (rs x) (rs y))) := .line rfl

private theorem const_straight (pub : Fin k → Word w) (s : Word w) (m : Memory w) (rs : Regs w r)
    (dst : Fin r) (v : Word 2) : Straight pub s m (.line (.constant dst v)) rs
      (Function.update rs dst (Fin.ofNat (2^w) v.val)) := .line rfl

private def postRegs {code : Flow r k} {pub : Fin k → Word w} {s m rs out}
    (_ : Straight pub s m code rs out) : Regs w r := out

/-- Exact register effects at the continuation of threshold preparation. The
hypotheses concern only the two final natural bounds, since the intermediate
word computations agree with the integer expressions modulo the word modulus. -/
theorem prepareBounds_exec (factor denominator u : ℕ) (pub : Fin d → Word w)
    (s : Word w) (m : Memory w) (rs : Regs w (6+d)) (hu : (rs (low d 2)).val = u)
    (hcap : u * factor * denominator + 1 < 2^w)
    (hlimit : (u * factor)^2 * denominator + 1 < 2^w) :
    ∃ out, Flow.Exec pub s (prepareBounds d factor denominator) rs m
        (List.replicate (prepareBounds d factor denominator).length .tick) out m ∧
      out (low d 0) = 0 ∧ out (low d 1) = 0 ∧ out (low d 2) = rs (low d 2) ∧
      (out (low d 3)).val = u * factor * denominator + 1 ∧ out (low d 4) = 0 ∧
      (out (low d 5)).val = (u * factor)^2 * denominator + 1 ∧ ∀ j, out (slot j) = rs (slot j) := by
  have h₁ := scaleFixed_straight (low d 4) (low d 2) (by simp (config := {decide := true})) factor pub s m rs
  have h₂ := scaleFixed_straight (low d 3) (low d 4) (by simp (config := {decide := true})) denominator pub s m (postRegs h₁)
  have h₃ := binary_straight pub s m (postRegs h₂) .mul (low d 1) (low d 4) (low d 4)
  have h₄ := scaleFixed_straight (low d 5) (low d 1) (by simp (config := {decide := true})) denominator pub s m (postRegs h₃)
  have h₅ := const_straight pub s m (postRegs h₄) (low d 0) 1
  have h₆ := binary_straight pub s m (postRegs h₅) .add (low d 3) (low d 3) (low d 0)
  have h₇ := binary_straight pub s m (postRegs h₆) .add (low d 5) (low d 5) (low d 0)
  have h₈ := const_straight pub s m (postRegs h₇) (low d 4) 0
  have h₉ := const_straight pub s m (postRegs h₈) (low d 0) 0
  have h₁₀ := const_straight pub s m (postRegs h₉) (low d 1) 0
  have hr := seq_straight h₁ (seq_straight h₂ (seq_straight h₃ (seq_straight h₄ (seq_straight h₅
    (seq_straight h₆ (seq_straight h₇ (seq_straight h₈ (seq_straight h₉ h₁₀))))))))
  have castu : (u : Word w) = rs (low d 2) := by rw [← hu]; simp
  have hc : ((u * factor * denominator + 1 : ℕ) : Word w).val = u * factor * denominator + 1 :=
    Nat.mod_eq_of_lt hcap
  have hl : (((u * factor)^2 * denominator + 1 : ℕ) : Word w).val = (u * factor)^2 * denominator + 1 :=
    Nat.mod_eq_of_lt hlimit
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, pow_two, castu] at hc hl
  refine ⟨postRegs h₁₀, hr, ?_⟩
  simp (config := {decide := true}) [postRegs, BinaryOp.eval, Function.update, hc, hl, pow_two]

private theorem tickBits (n : ℕ) : choiceBits (List.replicate n (Event.tick : Event w)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,choiceBits] using ih

/-- Linked native execution of the preparation table reaches the choice block
with the exact cap and limit, without consuming a branch bit or making a probe. -/
theorem prepareBounds_execute {p : ℕ} (factor denominator u : ℕ) {M : Machine w p (6+d) d}
    {label : (prepareBounds d factor denominator).Label → Fin p} {stop bad : Fin p}
    (hc : Flow.Linked M (prepareBounds d factor denominator) label stop bad) (hbad : M.code bad = .reject)
    (s : Word w) (priv : Word w → Word w) (m : Memory w) (rs : Regs w (6+d)) (hu : (rs (low d 2)).val = u)
    (hcap : u * factor * denominator + 1 < 2^w)
    (hlimit : (u * factor)^2 * denominator + 1 < 2^w) :
    ∃ out, (∀ (fuel : ℕ) (bits : List Bool),
      execute M.program ((prepareBounds d factor denominator).length + fuel)
        ⟨label (prepareBounds d factor denominator).entry,s,rs,priv⟩ m bits =
      (execute M.program fuel ⟨stop,s,out,priv⟩ m bits).map
        (Flow.prependEvents (List.replicate (prepareBounds d factor denominator).length .tick))) ∧
      out (low d 0) = 0 ∧ out (low d 1) = 0 ∧ out (low d 2) = rs (low d 2) ∧
      (out (low d 3)).val = u * factor * denominator + 1 ∧ out (low d 4) = 0 ∧
      (out (low d 5)).val = (u * factor)^2 * denominator + 1 ∧ ∀ j, out (slot j) = rs (slot j) := by
  obtain ⟨out,hr,hs⟩ := prepareBounds_exec factor denominator u M.publicData s m rs hu hcap hlimit
  refine ⟨out,fun fuel bits => ?_,hs⟩
  simpa only [List.length_replicate,tickBits,List.nil_append] using hr.execute hc hbad priv fuel bits

end CompressorRecords.MotifChoiceRAM

namespace CompressorRecords.MotifChoiceRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- The compiled call enters with the repetition count as its persistent word.
All private registers and memory start with the usual machine reset. -/
def choiceCall (n : ℕ) (factor denominator : ℕ) : Flow (6+n) n :=
  .seq (.line (.stateWord (low n 2))) <| .seq (prepareBounds n factor denominator) (choosePayload n)

/-- At every sufficiently wide word size the same fixed instruction table has
one successful stream per admitted outer index. This call begins at the native
machine entry point and includes all threshold preparation. -/
theorem compiled_outer_choices {n : ℕ} (order : Fin n ≃ S) (hq : ∀ e, 0 < q e) :
    ∃ K : ℕ, ∀ M (demand : D → ℕ), (∀ i, demand i ≤ M) → ∀ w,
      K + 2 * Nat.clog 2 (M + 1) ≤ w →
      let factor := B.scale * B.radius.num.natAbs
      let denominator := MotifAdmission.denominator q
      let code := choiceCall n factor denominator
      let weights := fun i => Fin.ofNat (2^w) (MotifAdmission.weight q (order i) * B.radius.den^2)
      let machine := (code.template none).instantiate w weights
      let fuel := 1 + (prepareBounds n factor denominator).length + (n * (4*w+10) + 3)
      let initial := machine.program.start (Fin.ofNat (2^w) (repetitions B demand))
      ∃ hw : outerCap B demand < 2^w, ∀ mem bits,
        (execute machine.program fuel initial mem bits).isSome ↔
          ∃ v, (outerReader B order hq demand w hw).read bits = some (v, []) := by
  obtain ⟨K, hK⟩ := native_word_fit p q B.scale B.scale_pos B.radius
  refine ⟨K, fun M demand hD w hW => ?_⟩
  obtain ⟨hu, hc, hl, hs, ht⟩ := hK M demand hD
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hW
  let factor := B.scale * B.radius.num.natAbs
  let denom := MotifAdmission.denominator q
  let code := choiceCall n factor denom
  let pub (i : Fin n) : BurstRAM.Word w := Fin.ofNat _ (MotifAdmission.weight q (order i) * B.radius.den^2)
  let machine := (code.template none).instantiate w pub
  let state : BurstRAM.Word w := Fin.ofNat _ (repetitions B demand)
  let regs := Function.update (fun _ : Fin (6+n) => (0 : BurstRAM.Word w)) (low n 2) state
  have hstate : state.val = repetitions B demand := Nat.mod_eq_of_lt (hu.trans_le hpow)
  have hpub (i : Fin n) : (machine.publicData i).val = MotifAdmission.weight q (order i) * B.radius.den^2 :=
    Nat.mod_eq_of_lt ((ht (order i)).trans_le hpow)
  have hstop : machine.code code.exitPC = .accept := by
    change ((code.template none).code code.exitPC).resize w = _
    rw [Flow.template_exit]; rfl
  have hbad : machine.code code.rejectPC = .reject := by
    change ((code.template none).code code.rejectPC).resize w = _
    rw [Flow.template_reject]; rfl
  have hlink := Flow.template_linked (w := w) code none pub
  have hbox : outerCap B demand + 1 < 2^w := hc.trans_le hpow
  refine ⟨(Nat.lt_succ_self _).trans hbox, fun mem bits => ?_⟩
  obtain ⟨out, hrun, _, _, h2, h3, h4, h5, _⟩ := prepareBounds_execute factor denom
    (repetitions B demand) hlink.seqRight.seqLeft hbad state (fun _ => 0) mem regs (by simp [regs, hstate])
    (by simpa [factor, Nat.mul_assoc, MotifAdmission.payloadCap] using hbox)
    (by simpa [factor, denom, repetitions, Nat.mul_assoc] using hl.trans_le hpow)
  let cfg : Config w (code.length+2) (6+n) :=
    ⟨code.pc (.inr (.inr (choosePayload n).entry)),state,out,fun _ => 0⟩
  have cap : (cfg.reg (low n 3)).val = outerCap B demand + 1 := by
    simpa [cfg, factor, denom, MotifAdmission.payloadCap, Nat.mul_assoc] using h3
  have sc : score (List.finRange n) machine.publicData (fun _ => cfg.reg (low n 3)) < 2 ^ w := by
    rw [full_score order q B.radius _ _ hpub]
    simpa [cap, outerCap, repetitions] using hs.trans_le hpow
  have hchoose := choosePayload_execute_iff B order hq demand hlink.seqRight.seqRight hstop hbad cfg rfl
    hpub (by simp [cfg, h2, regs, hstate]) cap (by simp [cfg, h4])
    (by simpa [cfg, factor, Nat.mul_assoc] using h5) sc mem bits
  have hread : Flow.Exec pub state (.line (.stateWord (low n 2))) (fun _ => 0) mem [.tick] regs mem := .line rfl
  let prep := prepareBounds n factor denom
  let remaining := n * (4*w+10) + 3
  have hpre := hrun remaining bits
  have hinit := hread.execute hlink.seqLeft hbad (fun _ => 0) (prep.length + remaining) bits
  simp only [List.length_cons, List.length_nil, choiceBits, List.nil_append] at hinit
  let mid : Config w (code.length+2) (6+n) :=
    ⟨code.pc (.inr (.inl prep.entry)),state,regs,fun _ => 0⟩
  change execute machine.program (1 + (prep.length + remaining)) (machine.program.start state) mem bits =
    (execute machine.program (prep.length + remaining) mid mem bits).map _ at hinit
  change execute machine.program (prep.length + remaining) mid mem bits =
    (execute machine.program remaining cfg mem bits).map _ at hpre
  change (execute machine.program (1 + prep.length + remaining) (machine.program.start state) mem bits).isSome ↔ _
  rw [Nat.add_assoc]
  rw [hinit, Option.isSome_map, hpre, Option.isSome_map]
  exact hchoose

end CompressorRecords.MotifChoiceRAM

end VPVNP
end Computability
end OAI
