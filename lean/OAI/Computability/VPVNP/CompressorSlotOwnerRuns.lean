import OAI.Computability.VPVNP.CompressorSlotOwners
import OAI.Computability.VPVNP.CompressorSlotOwnerPass
import OAI.Computability.VPVNP.RAMWork

/-!
# The two native endpoint-owner scans

The genuine scan reads the role, the chosen site, the CD indicator, and the
subdivision count. The padding scan reads the cyclic successor of a site.
Disjointness of those inputs from the output interval suffices to compute
both scans from the original descriptor memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwners

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ} {C : Type*}

private abbrev word (i : ℕ) : Word w := Fin.ofNat _ i

/-- The four external addresses consulted by the genuine worker. The second
read depends on the role word returned by the first. -/
def genuineInputs (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : List (Word w) :=
  let f := digits p i
  let role := roleAddress p f
  let old := oldAddress p f
  [role, old + m role.val, old + 3, subdivAddress p f]

private theorem genuine_congr (p : Fin 8 → Word w) (i : Word w) {mem ref : Memory w}
    (reads : ∀ a ∈ genuineInputs p ref i, mem a.val = ref a.val) :
    genuineOwner p mem i = genuineOwner p ref i := by
  let f := digits p i
  let role := roleAddress p f
  let old := oldAddress p f
  have hrole := reads role (by simp [genuineInputs, role, f])
  have hsite := reads (old + ref role.val) (by simp [genuineInputs, old, role, f])
  have hcd := reads (old + 3) (by simp [genuineInputs, old, f])
  have hsub := reads (subdivAddress p f) (by simp [genuineInputs, f])
  dsimp only [f, old, role] at hrole hsite hcd hsub
  simp only [genuineOwner, hrole, hsite, hcd, hsub]

private theorem dummy_congr (p : Fin 3 → Word w) (i : Word w) {mem ref : Memory w}
    (read : mem (p 1 + dummySource p i).val = ref (p 1 + dummySource p i).val) :
    dummyOwner p mem i = dummyOwner p ref i := by
  simp only [dummyOwner, read]

private theorem word_add (base : Word w) (i : ℕ) : base + word i = word (base.val+i) := by
  apply Fin.ext
  simp only [word, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]

private theorem word_succ (i : ℕ) : word (w := w) i + 1 = word (i+1) := by
  apply Fin.ext
  simp [word, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

/-- A complete worker scan starts at cursor zero and fills its output cells
in address order. The frame covers arbitrary external addresses. -/
structure FilledRun (P : Program w C) (fuel probes ticks count : ℕ)
    (base : Word w) (value : ℕ → Word w) (initial : Memory w) (rs : List (Report w)) : Prop where
  executed : runSegment P fuel (some 0) initial (List.replicate count []) = some rs
  cursor : endState (some 0) rs = some (Fin.ofNat _ count)
  filled : ∀ i < count, after initial (eventLog rs) (base.val+i) = value i
  frame : ∀ a, a < base.val ∨ base.val+count ≤ a → after initial (eventLog rs) a = initial a
  length : rs.length = count
  calls : ∀ r ∈ rs, r.probes = probes ∧ r.events.length = ticks
  cost : RAMBuckets.cost Report.probes rs = (1+probes)*count

/-- Start a sequential output worker at zero and package its interval and frame. -/
theorem filled_run (P : Program w C) (fuel probes ticks count : ℕ)
    (base : Word w) (value : ℕ → Word w) (initial : Memory w) (fit : base.val+count ≤ 2^w)
    (visit : SlotOwnerPass.Visit P fuel probes ticks base.val 0 count value initial) :
    ∃ rs, FilledRun P fuel probes ticks count base value initial rs := by
  obtain ⟨rs,hr,hs,hf,ho,hl,hc,hcost⟩ :=
    SlotOwnerPass.run P fuel probes ticks base.val 0 count value initial (by simpa using fit) visit
  exact ⟨rs, hr, by simpa using hs, fun i hi => hf i (Nat.zero_le i) (by simpa using hi),
    fun a ha => ho a (by simpa using ha), hl, hc, hcost⟩

/-- Read four input words and write one genuine-field owner at each cursor. -/
theorem genuine_run (p : Fin 8 → Word w) (initial : Memory w) (count : ℕ)
    (fit : (p 7).val+count ≤ 2^w)
    (reads : ∀ i < count, ∀ a ∈ genuineInputs p initial (word i),
      a.val < (p 7).val ∨ (p 7).val+count ≤ a.val) :
    let P := ((template genuine 0).instantiate w p).program
    ∃ rs, FilledRun P 49 5 48 count (p 7) (fun i => genuineOwner p initial (word i)) initial rs := by
  intro P
  apply filled_run P 49 5 48 count (p 7) _ initial fit
  intro i _ hi mem frame
  have lt : i < count := by simpa using hi
  have eq := genuine_congr p (word i) (mem := mem) (ref := initial) (fun a ha => by
    have h := reads i lt a ha
    exact frame a.val (by omega))
  refine ⟨genuineEvents p mem (word i), ?_, ?_, (genuine_work ..).2, (genuine_work ..).1⟩
  · rw [genuine_native, word_succ]
  · rw [genuine_after, eq, word_add]

/-- Read one cyclic successor and write one dummy-field owner at each cursor. -/
theorem dummy_run (p : Fin 3 → Word w) (initial : Memory w) (count : ℕ)
    (fit : (p 2).val+count ≤ 2^w)
    (reads : ∀ i < count, let a := p 1 + dummySource p (word i)
      a.val < (p 2).val ∨ (p 2).val+count ≤ a.val) :
    let P := ((template dummy 0).instantiate w p).program
    ∃ rs, FilledRun P 20 2 19 count (p 2) (fun i => dummyOwner p initial (word i)) initial rs := by
  intro P
  apply filled_run P 20 2 19 count (p 2) _ initial fit
  intro i _ hi mem frame
  have lt : i < count := by simpa using hi
  let a := p 1 + dummySource p (word i)
  have h : a.val < (p 2).val ∨ (p 2).val+count ≤ a.val := reads i lt
  have eq : mem a.val = initial a.val := frame a.val (by omega)
  refine ⟨dummyEvents p mem (word i), ?_, ?_, (dummy_work ..).2, (dummy_work ..).1⟩
  · rw [dummy_native, word_succ]
  · rw [dummy_after, word_add]
    rw [dummy_congr p (word i) eq]

/-- Execute the genuine and dummy workers in sequence, resetting the cursor
between phases. The final table gives each endpoint the owner computed from
the original descriptor memory. The two calls-plus-probes costs add exactly. -/
theorem owner_runs (g : Fin 8 → Word w) (d : Fin 3 → Word w) (initial : Memory w)
    (ng nd : ℕ) (adjacent : (d 2).val = (g 7).val + ng) (fit : (d 2).val+nd ≤ 2^w)
    (greads : ∀ i < ng, ∀ a ∈ genuineInputs g initial (word i),
      a.val < (g 7).val ∨ (d 2).val+nd ≤ a.val)
    (dreads : ∀ i < nd, let a := d 1 + dummySource d (word i)
      a.val < (g 7).val ∨ (d 2).val+nd ≤ a.val) :
    let Pg := ((template genuine 0).instantiate w g).program
    let Pd := ((template dummy 0).instantiate w d).program
    ∃ gr dr, let mid := after initial (eventLog gr)
             let final := after mid (eventLog dr)
             FilledRun Pg 49 5 48 ng (g 7) (fun i => genuineOwner g initial (word i)) initial gr ∧
             FilledRun Pd 20 2 19 nd (d 2) (fun i => dummyOwner d initial (word i)) mid dr ∧
             (∀ i < ng, final ((g 7).val+i) = genuineOwner g initial (word i)) ∧
             (∀ a, a < (g 7).val ∨ (d 2).val+nd ≤ a → final a = initial a) ∧
             RAMBuckets.cost Report.probes (gr ++ dr) = 6*ng + 3*nd := by
  intro Pg Pd
  obtain ⟨gr, gh⟩ := genuine_run g initial ng (by omega) (fun i hi a ha => by
    have := greads i hi a ha
    omega)
  let mid := after initial (eventLog gr)
  obtain ⟨dr, dh⟩ := dummy_run d mid nd fit (fun i hi => by
    have h := dreads i hi
    dsimp only at h ⊢
    omega)
  have same (i : ℕ) (hi : i < nd) : dummyOwner d mid (word i) = dummyOwner d initial (word i) := by
    apply dummy_congr
    apply gh.frame
    have h := dreads i hi
    dsimp only at h
    omega
  refine ⟨gr, dr, gh, {dh with filled := fun i hi => (dh.filled i hi).trans (same i hi)}, ?_, ?_, ?_⟩
  · intro i hi
    exact (dh.frame _ (.inl (by omega))).trans (gh.filled i hi)
  · intro a ha
    exact (dh.frame a (by omega)).trans (gh.frame a (by omega))
  · rw [RAMBuckets.cost_append, gh.cost, dh.cost]

private theorem div_value (x y : Word w) : (BinaryOp.div.eval x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem mod_value (x y : Word w) : (BinaryOp.mod.eval x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

/-- The four read addresses stay in the original-arc records, the eight role
entries, and the four subdivision counts, respectively. -/
theorem genuine_inputs_ranges (p : Fin 8 → Word w) (m : Memory w) (i : Word w)
    (arcsFit : (p 3).val + 4 * ((p 2).val * (p 0).val) ≤ 2^w)
    (rolesFit : (p 4).val + 8 ≤ 2^w) (subdivFit : (p 5).val + 4 ≤ 2^w)
    (roles : ∀ j < 8, (m ((p 4).val+j)).val < 3)
    (hi : i.val < 4*(p 2).val*(p 1).val*(p 0).val*2) :
    ∀ a ∈ genuineInputs p m i,
      ((p 3).val ≤ a.val ∧ a.val < (p 3).val+4*((p 2).val*(p 0).val)) ∨
      ((p 4).val ≤ a.val ∧ a.val < (p 4).val+8) ∨
      ((p 5).val ≤ a.val ∧ a.val < (p 5).val+4) := by
  let f := digits p i
  have htwo : (2 : Word w).val = 2 := Nat.mod_eq_of_lt (by omega : 2 < 2^w)
  have oldPos : 0 < (p 2).val := by by_contra! h; simp [show (p 2).val = 0 by omega] at hi
  have subPos : 0 < (p 1).val := by by_contra! h; simp [show (p 1).val = 0 by omega] at hi
  have lanePos : 0 < (p 0).val := by by_contra! h; simp [show (p 0).val = 0 by omega] at hi
  have ht : f.edgeType.val < 4 := by
    change ((BinaryOp.div.eval _ (p 2)).val < 4)
    simp only [div_value, htwo, Nat.div_lt_iff_lt_mul oldPos, Nat.div_lt_iff_lt_mul subPos,
      Nat.div_lt_iff_lt_mul lanePos, Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
    exact hi
  have hs : f.side.val < 2 := by
    change (BinaryOp.mod.eval i 2).val < 2
    rw [mod_value, htwo]
    exact Nat.mod_lt _ (by decide)
  have hb : f.oldArc.val < (p 2).val*(p 0).val := by
    let arc := BinaryOp.div.eval i 2
    let b := BinaryOp.div.eval (BinaryOp.div.eval arc (p 0)) (p 1)
    have hbase := Nat.mod_lt b.val oldPos
    have hlane := Nat.mod_lt arc.val lanePos
    have bound := Nat.mul_le_mul_right (p 0).val (Nat.succ_le_of_lt hbase)
    rw [Nat.succ_mul] at bound
    change ((BinaryOp.mod.eval b (p 2)) * p 0 + BinaryOp.mod.eval arc (p 0)).val < _
    rw [Fin.val_add, Fin.val_mul, mod_value, mod_value, Nat.mod_add_mod]
    exact (Nat.mod_le ..).trans_lt (by omega)
  let r := roleAddress p f
  let old := oldAddress p f
  have hr : r.val = (p 4).val + (2*f.edgeType.val + f.side.val) := by
    simp only [r, roleAddress, Fin.val_add, Fin.val_mul, htwo, Nat.mod_add_mod, Nat.add_mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hrole : (m r.val).val < 3 := by rw [hr]; exact roles _ (by omega)
  have hold : old.val = (p 3).val + 4*f.oldArc.val := by
    simp only [old, oldAddress, Fin.val_add, Fin.val_mul, htwo, Nat.mod_mul_mod, Nat.add_mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hc : (old + 3).val = old.val+3 := by
    rw [Fin.val_add, show (3 : Word w).val = 3 from Nat.mod_eq_of_lt (by omega : 3 < 2^w),
      Nat.mod_eq_of_lt (by omega)]
  have hsite : (old + m r.val).val = old.val+(m r.val).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have hsub : (subdivAddress p f).val = (p 5).val+f.edgeType.val := by
    rw [subdivAddress, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  intro a ha
  change a ∈ [r, old + m r.val, old + 3, subdivAddress p f] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (by omega))

/-- Placing the three input arrays below the output suffices for every genuine
read. The role words are offsets in the three-site part of each four-word record. -/
theorem genuine_inputs_before (p : Fin 8 → Word w) (m : Memory w) (i stop : Word w)
    (arcsEnd : (p 3).val + 4 * ((p 2).val * (p 0).val) ≤ stop.val)
    (rolesEnd : (p 4).val + 8 ≤ stop.val) (subdivEnd : (p 5).val + 4 ≤ stop.val)
    (roles : ∀ j < 8, (m ((p 4).val+j)).val < 3)
    (hi : i.val < 4*(p 2).val*(p 1).val*(p 0).val*2) :
    ∀ a ∈ genuineInputs p m i, a.val < stop.val := by
  intro a ha
  rcases genuine_inputs_ranges p m i (arcsEnd.trans stop.isLt.le) (rolesEnd.trans stop.isLt.le)
      (subdivEnd.trans stop.isLt.le) roles hi a ha with h | h | h <;> omega

/-- Both endpoints of a dummy arc probe its original site in the cyclic successor array. -/
theorem dummy_input_range (p : Fin 3 → Word w) (i : Word w) (sites : ℕ)
    (fit : (p 1).val+sites ≤ 2^w) (hw : 2 < 2^w)
    (hi : i.val < sites*(p 0).val*2) :
    (p 1).val ≤ (p 1+dummySource p i).val ∧ (p 1+dummySource p i).val < (p 1).val+sites := by
  have hp : 0 < (p 0).val := by by_contra! h; simp [show (p 0).val = 0 by omega] at hi
  have hs : (dummySource p i).val < sites := by
    change (BinaryOp.div.eval (BinaryOp.div.eval i 2) (p 0)).val < _
    rw [div_value, div_value, show (2 : Word w).val = 2 from Nat.mod_eq_of_lt hw,
      Nat.div_lt_iff_lt_mul hp, Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
    exact hi
  rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A cyclic-successor array of one word per site suffices for both sides of
each dummy arc, including all copies of a padding slot. -/
theorem dummy_input_before (p : Fin 3 → Word w) (i stop : Word w) (sites : ℕ)
    (endOfTable : (p 1).val+sites ≤ stop.val) (hw : 2 < 2^w)
    (hi : i.val < sites*(p 0).val*2) : (p 1+dummySource p i).val < stop.val :=
  (dummy_input_range p i sites (endOfTable.trans stop.isLt.le) hw hi).2.trans_le endOfTable

/-- Straight-line templates use registers and external memory, so an
instruction never scans the private write log. This holds at every program
counter, for every allowance and stream of read bits. -/
theorem template_opcode_work {r k : ℕ} (ops : List (Op r k)) (result : Fin r)
    (pub : Fin k → Word w) (fuel : ℕ) (l : LogConfig w (ops.length+2) r)
    (allowance : ℕ) (bits : List Bool) :
    ((template ops result).instantiate w pub).loggedDispatchWork fuel l allowance bits ≤ 6*fuel := by
  let M := (template ops result).instantiate w pub
  have noLog (c : LogConfig w (ops.length+2) r) : (M.code c.pc).actualLogWork c = 0 := by
    simp only [M, Template.instantiate, template]
    split
    · cases ops[c.pc.val] <;> rfl
    · split <;> rfl
  change M.loggedDispatchWork fuel l allowance bits ≤ _
  induction fuel generalizing l allowance bits with
  | zero => rfl
  | succ f ih =>
    rw [Machine.loggedDispatchWork, noLog, Nat.add_zero]
    have h := (M.code l.pc).wordWork_le
    split
    · omega
    · rename_i l' a' bs' _
      have := ih l' a' bs'
      omega

/-- A genuine-owner call dispatches at most 49 instructions. -/
theorem genuine_opcode_work (pub : Fin 8 → Word w) (i : Word w)
    (allowance : ℕ) (bits : List Bool) :
    let M := (template genuine 0).instantiate w pub
    M.loggedDispatchWork 49 (M.logProgram.start i) allowance bits ≤ 294 :=
  template_opcode_work genuine 0 pub 49 _ allowance bits

/-- A dummy-owner call dispatches at most 20 instructions. -/
theorem dummy_opcode_work (pub : Fin 3 → Word w) (i : Word w)
    (allowance : ℕ) (bits : List Bool) :
    let M := (template dummy 0).instantiate w pub
    M.loggedDispatchWork 20 (M.logProgram.start i) allowance bits ≤ 120 :=
  template_opcode_work dummy 0 pub 20 _ allowance bits

end CompressorRecords.SlotOwners

end VPVNP
end Computability
end OAI
