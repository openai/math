import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Reading the base slots at lane zero

In a lifted slot graph the target of an outgoing slot at lane zero contains the destination
base vertex, its incoming slot, and the displacement. Appendix E uses one scan of these
slots to emit both base incidence tables and the displacement table of the next level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BaseOutput

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression IncidenceDirectory
open CursorRAM (encode)

variable {w a l : ℕ} (T : IncidenceDirectory w) (X : State a l)

/-- Persistent state is the next base slot. The fixed public parameters give the two
radices and the addresses of the one input and three output columns. -/
def params (T : IncidenceDirectory w) (a l : ℕ) : Fin 6 → Word w :=
  ![encode w (2^a), encode w (2^l), T.actualOut, T.baseOut, T.baseIn, T.shift]

/-- Native visit that reads an actual mate at lane zero and emits its base mate, inverse mate,
and displacement. -/
def visit : List (Op 8 6) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1,
   .binary .div 3 0 1, .binary .mod 4 0 1, .binary .mul 3 3 2, .binary .mul 3 3 1,
   .binary .add 3 3 4, .publicWord 5 2, .binary .add 5 5 3, .read 6 5,
   .binary .mod 4 6 1, .binary .div 3 6 1, .binary .mod 6 3 2, .binary .div 3 3 2,
   .binary .mul 3 3 1, .binary .add 3 3 4, .publicWord 5 3, .binary .add 5 5 0,
   .write 5 3, .publicWord 5 4, .binary .add 5 5 3, .write 5 0,
   .publicWord 5 5, .binary .add 5 5 0, .write 5 6, .constant 7 1, .binary .add 0 0 7]

variable (p : Fin 6 → Word w)

/-- Convert a packed base slot index into the actual slot index of that vertex and port at lane
zero. -/
def source (i : Word w) := BinaryOp.div.eval i (p 0) * p 1 * p 0 + BinaryOp.mod.eval i (p 0)

/-- Read the actual outgoing mate of a lane-zero source slot. -/
def mate (m : Memory w) (i : Word w) := m (p 2 + source p i).val

/-- Discard the lane from an actual mate index to recover its destination base slot. -/
def destination (y : Word w) :=
  BinaryOp.div.eval (BinaryOp.div.eval y (p 0)) (p 1) * p 0 + BinaryOp.mod.eval y (p 0)

/-- Extract the destination lane of a lane-zero arc, which equals its displacement. -/
def displacement (y : Word w) := BinaryOp.mod.eval (BinaryOp.div.eval y (p 0)) (p 1)

/-- Install the base mate, reverse mate, and displacement recovered from a single lane-zero
lookup. -/
def update (m : Memory w) (i : Word w) : Memory w :=
  let j := destination p (mate p m i)
  writeMemory (writeMemory (writeMemory m (p 3+i) j) (p 4+j) i) (p 5+i) (displacement p (mate p m i))

/-- The 28-event trace of one base-output visit, with one actual-mate read and three
base-column writes. -/
def events (m : Memory w) (i : Word w) : List (Event w) :=
  let y := mate p m i
  let j := destination p y
  [.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.read (p 2 + source p i) y,
   .tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.write (p 3+i) j,
   .tick,.tick,.write (p 4+j) i,.tick,.tick,.write (p 5+i) (displacement p y),.tick,.tick]

theorem events_work (m : Memory w) (i : Word w) :
    (events p m i).length = 28 ∧ countProbes (events p m i) = 4 := ⟨rfl,rfl⟩

theorem events_after (m : Memory w) (i : Word w) : after m (events p m i) = update p m i := rfl

private theorem visit_trace (m : Memory w) (i : Word w) (rs : Regs w 8) :
    ∃ out, trace p i visit rs m = some (events p m i, out, update p m i) ∧ out 0 = i+1 := by
  simp (config := {decide := true}) [visit, events, update, source, mate, destination, displacement,
    trace, Op.effect, BinaryOp.eval, Function.update]
  rfl

theorem visit_native (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 29 (M.program.start i) m [] = some ⟨events p m i, some (i+1)⟩ := by
  obtain ⟨out, ht, hret⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hret]

/-- Number of base slots, counting every local port of each base vertex. -/
abbrev baseCount := Fintype.card X.Base * 2^a

/-- Number of actual slots, including all binary lanes at each base vertex and port. -/
abbrev actualCount := Fintype.card X.Base * 2^l * 2^a

private theorem counts : baseCount X ≤ actualCount X :=
  Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l))

private theorem base_val (layout : T.Layout X) (e : X.Base × Fin (2^a)) :
    (basePort (w := w) X e).val = (baseOrder X e).val := by
  rw [basePort_number]
  exact Nat.mod_eq_of_lt ((baseOrder X e).isLt.trans_le ((counts X).trans layout.fit))

private theorem actual_val (layout : T.Layout X) (e : (X.Base × BitWord l) × Fin (2^a)) :
    (actualPort (w := w) X e).val = (actualOrder X e).val := by
  rw [actualPort_number]
  exact Nat.mod_eq_of_lt ((actualOrder X e).isLt.trans_le layout.fit)

private theorem unpack {x d : Word w} {hi lo : ℕ} (h : x.val = hi * d.val + lo) (hl : lo < d.val) :
    (BinaryOp.div.eval x d).val = hi ∧ (BinaryOp.mod.eval x d).val = lo := by
  have hd : 0 < d.val := Nat.zero_lt_of_lt hl
  have hq : x.val / d.val = hi := by
    rw [h, Nat.mul_comm hi, Nat.mul_add_div hd, Nat.div_eq_of_lt hl, Nat.add_zero]
  have hr : x.val % d.val = lo := by rw [h, Nat.mul_add_mod_of_lt hl]
  exact ⟨(Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)).trans hq,
    (Nat.mod_eq_of_lt ((Nat.mod_lt _ hd).trans d.isLt)).trans hr⟩

/-- The one actual read at lane zero decodes the base mate and its residual displacement. -/
theorem read_row (layout : T.Layout X) (m : Memory w) (actual : T.ActualColumns X m)
    (e : X.Base × Fin (2^a)) :
    let p := params T a l
    let y := mate p m (basePort X e)
    destination p y = basePort X (X.slots.base.target e) ∧
      displacement p y = encode w (bitWordFinEquiv l (X.slots.displacement e)).val := by
  let p := params T a l
  have hc : 1 < Fintype.card X.Base :=
    Fintype.one_lt_card_iff.mpr ⟨_, _, X.slots.base.ends_ne e⟩
  have hR : 2^l < Fintype.card X.Base * 2^l := by
    simpa using Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos l)
  have hD : 2^a < actualCount X := by
    have := Nat.mul_lt_mul_of_pos_right (show 1 < Fintype.card X.Base * 2^l by
      have := Nat.two_pow_pos l; omega) (Nat.two_pow_pos a)
    simpa using this
  have hd : (p 0).val = 2^a := Nat.mod_eq_of_lt (hD.trans_le layout.fit)
  have hl : (p 1).val = 2^l :=
    Nat.mod_eq_of_lt ((hR.trans_le (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))).trans_le layout.fit)
  have hu := unpack (hi := (X.baseIndex e.1).val) (lo := e.2.val) (x := basePort (w := w) X e) (d := p 0)
    (by rw [base_val T X layout, baseOrder_val, hd]) (by rw [hd]; exact e.2.isLt)
  have hz : (bitWordFinEquiv l 0).val = 0 := by simpa using bitWordFinEquiv_add_val (0 : BitWord l) 0
  have hs : source p (basePort X e) = actualPort X ((e.1,0),e.2) := by
    apply Fin.ext
    rw [source, Fin.val_add, Fin.val_mul, Fin.val_mul, hu.1, hu.2, hd, hl, actualPort_number]
    change _ = (actualOrder X ((e.1,0),e.2)).val % _
    rw [actualOrder_val, hz, Nat.add_zero, Nat.mod_mul_mod, Nat.mod_add_mod]
  let f := X.slots.base.target e
  let s := X.slots.displacement e
  let y := mate p m (basePort X e)
  have hm : y = actualPort X ((f.1,s),f.2) := by
    change m (T.actualOut + source p (basePort X e)).val = _
    rw [hs, actual.actualOut, LiftedSlots.actualGraph_target, zero_add]
  have hyv : y.val = ((X.baseIndex f.1).val * (p 1).val + (bitWordFinEquiv l s).val) * (p 0).val + f.2.val := by
    rw [hm, actual_val T X layout, actualOrder_val, hd, hl]
  have hy := unpack hyv (by rw [hd]; exact f.2.isLt)
  have hy' := unpack (d := p 1) hy.1 (by rw [hl]; exact (bitWordFinEquiv l s).isLt)
  constructor
  · apply Fin.ext
    change (destination p y).val = (basePort (w := w) X f).val
    rw [destination, Fin.val_add, Fin.val_mul, hy'.1, hy.2, hd, Nat.mod_add_mod, basePort_number]
    change _ = (baseOrder X f).val % _
    rw [baseOrder_val]
  · apply Fin.ext
    change (BinaryOp.mod.eval (BinaryOp.div.eval y (p 0)) (p 1)).val = _ % _
    rw [hy'.2, Nat.mod_eq_of_lt ((bitWordFinEquiv l s).isLt.trans (hl ▸ (p 1).isLt))]

private def writeBase (m : Memory w) (i j shift : Word w) : Memory w :=
  writeMemory (writeMemory (writeMemory m (T.baseOut+i) j) (T.baseIn+j) i) (T.shift+i) shift

private theorem update_row (layout : T.Layout X) (m : Memory w) (actual : T.ActualColumns X m)
    (e : X.Base × Fin (2^a)) :
    update (params T a l) m (basePort X e) = writeBase T m (basePort X e)
      (basePort X (X.slots.base.target e)) (encode w (bitWordFinEquiv l (X.slots.displacement e)).val) := by
  obtain ⟨hd,hs⟩ := read_row T X layout m actual e
  simp only [update, hd, hs, writeBase]
  rfl

private theorem cell_write (layout : T.Layout X) (m : Memory w) (i j shift : Word w)
    (hi : i.val < actualCount X) (hj : j.val < actualCount X) (c : Fin 6) (x : Word w)
    (hx : x.val < actualCount X) :
    writeBase T m i j shift (T.column c + x).val =
      if c = 2 ∧ x = i then shift else if c = 1 ∧ x = j then i
      else if c = 0 ∧ x = i then j else m (T.column c + x).val := by
  change writeMemory (writeMemory (writeMemory m (T.column 0+i) j) (T.column 1+j) i)
    (T.column 2+i) shift (T.column c+x).val = _
  simp only [writeMemory, layout.apart c 2 x i hx hi, layout.apart c 1 x j hx hj,
    layout.apart c 0 x i hx hi]

/-- Slots already visited in the lane-zero pass, indexed by the source.
The inverse column is indexed by the matched destination. -/
structure Prefix (m : Memory w) (k : ℕ) : Prop where
  actual : T.ActualColumns X m
  rows : ∀ e, (baseOrder X e).val < k →
    m (T.baseOut + basePort X e).val = basePort X (X.slots.base.target e) ∧
    m (T.baseIn + basePort X (X.slots.base.target e)).val = basePort X e ∧
    m (T.shift + basePort X e).val = encode w (bitWordFinEquiv l (X.slots.displacement e)).val

private theorem base_injective (layout : T.Layout X) : Function.Injective (basePort (w := w) X) := by
  intro e f h
  apply (baseOrder X).injective
  exact Fin.ext ((base_val T X layout e).symm.trans ((congrArg Fin.val h).trans (base_val T X layout f)))

private theorem step (layout : T.Layout X) (m : Memory w) (e : X.Base × Fin (2^a))
    (cur : Prefix T X m (baseOrder X e).val) :
    Prefix T X (update (params T a l) m (basePort X e)) ((baseOrder X e).val+1) := by
  rw [update_row T X layout m cur.actual]
  have hb (b : X.Base × Fin (2^a)) : (basePort (w := w) X b).val < actualCount X := by
    rw [base_val T X layout]; exact (baseOrder X b).isLt.trans_le (counts X)
  have ha (b : (X.Base × BitWord l) × Fin (2^a)) : (actualPort (w := w) X b).val < actualCount X := by
    rw [actual_val T X layout]; exact (actualOrder X b).isLt
  let f := X.slots.base.target
  let sh := encode w (bitWordFinEquiv l (X.slots.displacement e)).val
  have cells := cell_write T X layout m (basePort X e) (basePort X (f e)) sh (hb e) (hb (f e))
  constructor
  · constructor
    · intro z
      change writeBase T m _ _ _ (T.column 3 + actualPort X z).val = _
      rw [cells 3 _ (ha z)]
      simp; exact cur.actual.actualOut z
    · intro z
      change writeBase T m _ _ _ (T.column 4 + actualPort X z).val = _
      rw [cells 4 _ (ha z)]
      simp; exact cur.actual.actualIn z
    · intro z
      change writeBase T m _ _ _ (T.column 5 + actualPort X z).val = _
      rw [cells 5 _ (ha z)]
      simp; exact cur.actual.width z
  · intro z hz
    change writeBase T m _ _ _ (T.column 0 + basePort X z).val = basePort X (f z) ∧
      writeBase T m _ _ _ (T.column 1 + basePort X (f z)).val = basePort X z ∧
      writeBase T m _ _ _ (T.column 2 + basePort X z).val = _
    rw [cells 0 _ (hb z), cells 1 _ (hb (f z)), cells 2 _ (hb z)]
    by_cases he : z = e
    · subst z; simp [sh]
    · have hsrc : basePort (w := w) X z ≠ basePort X e := fun h => he (base_injective T X layout h)
      have hdst : basePort (w := w) X (f z) ≠ basePort X (f e) :=
        fun h => he (f.injective (base_injective T X layout h))
      have hne : (baseOrder X z).val ≠ (baseOrder X e).val :=
        fun h => he ((baseOrder X).injective (Fin.ext h))
      simp [hsrc,hdst]; exact cur.rows z (by omega)

/-- A memory address disjoint from all three written base columns. -/
def Outside (addr : ℕ) : Prop :=
  ∀ j : Word w, j.val < baseCount X →
    addr ≠ (T.baseOut+j).val ∧ addr ≠ (T.baseIn+j).val ∧ addr ≠ (T.shift+j).val

/-- All lane-zero calls through the given cursor, with unchanged memory outside the output
columns. Neither the inverse actual column nor the width column is read by these calls. -/
theorem scan_run (layout : T.Layout X) (m : Memory w) (k calls : ℕ)
    (cur : Prefix T X m k) (room : k + calls ≤ baseCount X) :
    let M := (template visit 0).instantiate w (params T a l)
    ∃ rs, runSegment M.program 29 (some (Fin.ofNat (2^w) k)) m (List.replicate calls []) = some rs ∧
      Prefix T X (after m (eventLog rs)) (k + calls) ∧
      (∀ addr, Outside T X addr → after m (eventLog rs) addr = m addr) ∧
      rs.length = calls ∧ ∀ r ∈ rs, r.events.length = 28 ∧ countProbes r.events = 4 := by
  let p := params T a l
  let M := (template visit 0).instantiate w p
  induction calls generalizing k m with
  | zero => exact ⟨[],rfl,cur,fun _ _ => rfl,rfl,by simp⟩
  | succ s ih =>
    have hk : k < baseCount X := by omega
    let e := (baseOrder X).symm ⟨k,hk⟩
    let i := basePort (w := w) X e
    have he : (baseOrder X e).val = k := by simp [e]
    have hi : i.val = k := (base_val T X layout e).trans he
    have hiw : Fin.ofNat (2^w) k = i := by apply Fin.ext; rw [← hi]; exact Nat.mod_eq_of_lt i.isLt
    have hn := step T X layout m e (he ▸ cur)
    have hnext : i + 1 = Fin.ofNat (2^w) (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', hi, Nat.add_mod_mod]; rfl
    let r : Report w := ⟨events p m i, some (i+1)⟩
    obtain ⟨rs,run,rows,frame,hl,hw⟩ := ih (update p m i) (k+1) (he ▸ hn) (by omega)
    have hm : after m (eventLog (r :: rs)) = after (update p m i) (eventLog rs) := by
      change List.foldl BurstRAM.update m (events p m i ++ eventLog rs) = _
      rw [List.foldl_append]; rfl
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hl], ?_⟩
    · change runSegment M.program 29 (some (Fin.ofNat (2^w) k)) m (List.replicate (s+1) []) = _
      rw [hiw, List.replicate_succ, runSegment, visit_native p m i]
      change runSegment M.program 29 (some (Fin.ofNat (2^w) (k+1))) (update p m i) (List.replicate s []) = some rs at run
      simp only [r, events_after, hnext, run, Option.map_some]
    · simpa [hm, Nat.add_assoc, Nat.add_comm 1 s] using rows
    · intro addr outside
      rw [hm, frame addr outside]
      change update (params T a l) m (basePort X e) addr = _
      rw [update_row T X layout m cur.actual]
      have hs := outside i (hi ▸ hk)
      have hd := outside (basePort X (X.slots.base.target e))
        (by rw [base_val T X layout]; exact (baseOrder X _).isLt)
      change writeBase T m i (basePort X (X.slots.base.target e)) _ addr = _
      simp [writeBase, writeMemory, hs.1, hs.2.2, hd.2.1]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact events_work p m i
      · exact hw q hq

private theorem pass_cost {rs : List (Report w)} (hw : ∀ r ∈ rs, countProbes r.events = 4) :
    RAMBuckets.cost (fun r : Report w => countProbes r.events) rs = 5 * rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [RAMBuckets.cost, hw r (List.mem_cons_self ..), ih (fun q h => hw q (List.mem_cons_of_mem _ h)),
      List.length_cons, Nat.mul_succ]
    omega

/-- One call for each base slot recovers the entire base matching, its inverse, and its
displacement. Together with the actual columns these give the complete level directory. -/
theorem base_pass (m : Memory w) (layout : T.Layout X) (actual : T.ActualColumns X m) :
    let M := (template visit 0).instantiate w (params T a l)
    ∃ rs, runSegment M.program 29 (some 0) m (List.replicate (baseCount X) []) = some rs ∧
      T.Represents X (after m (eventLog rs)) ∧
      (∀ addr, Outside T X addr → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost (fun r : Report w => countProbes r.events) rs = 5 * baseCount X ∧
      rs.length = baseCount X ∧ ∀ r ∈ rs, r.events.length = 28 ∧ countProbes r.events = 4 := by
  have init : Prefix T X m 0 := ⟨actual, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  obtain ⟨rs,run,rows,frame,hl,hw⟩ := scan_run T X layout m 0 (baseCount X) init (by simp)
  have full (e) := rows.rows e (by simpa only [Nat.zero_add] using (baseOrder X e).isLt)
  refine ⟨rs,run,?_,frame,(pass_cost (fun r h => (hw r h).2)).trans (by rw [hl]),hl,hw⟩
  refine ⟨fun e => (full e).1, fun e => ?_, fun e => (full e).2.2,
    rows.actual.actualOut, rows.actual.actualIn, rows.actual.width⟩
  simpa only [Equiv.apply_symm_apply] using (full (X.slots.base.target.symm e)).2.1

end CompressorRecords.BaseOutput

end VPVNP
end Computability
end OAI
