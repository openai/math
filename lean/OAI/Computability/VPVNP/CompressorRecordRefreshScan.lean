import OAI.Computability.VPVNP.CompressorRecordRefresh
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Complete external-bundle pass of Appendix E

The segment scan visits all old actual arc numbers in increasing order. Each bundle's
accumulator is independent. Both endpoint arrays receive the prefix in source order and
the incoming array receives the source's width, including at an empty segment. The scan
runs from zeroed bundle totals and preserves the read-only directory and old widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Directory and old wire lengths, in the word format used by `visit`. -/
structure Input (w : ℕ) where
  /-- The old outgoing width at each source-ordered segment ordinal. -/
  width : Word w → Word w
  /-- The translated destination bundle number at each source bundle ordinal. -/
  target : Word w → Word w
  /-- The binary port displacement associated with each source bundle. -/
  shift : Word w → Word w

/-- Compute the destination segment ordinal from the immutable bundle target and port-shift
functions. -/
def Input.dest (A : Input w) (p : Fin 8 → Word w) (i : Word w) : Word w :=
  let b := bundle p i
  A.target b * p 0 + BinaryOp.bitXor.eval (BinaryOp.mod.eval i (p 0)) (A.shift b)

/-- Width accumulated in a given bundle in the first `k` visits. -/
def prefixTotal (p : Fin 8 → Word w) (A : Input w) : ℕ → Word w → ℕ
  | 0, _ => 0
  | k+1, b => prefixTotal p A k b +
      if bundle p (Fin.ofNat (2^w) k) = b then (A.width (Fin.ofNat (2^w) k)).val else 0

/-- Read the indexed word of the table whose base is the selected public operand. -/
def cell (p : Fin 8 → Word w) (m : Memory w) (t : Fin 8) (i : Word w) : Word w := m (p t + i).val

/-- The nonzero public indices name the seven arrays. All array indices are below `n`. -/
structure Regions (p : Fin 8 → Word w) (n : ℕ) : Prop where
  fits : n ≤ 2 ^ w
  apart : ∀ (t u : Fin 8), t ≠ 0 → u ≠ 0 → ∀ (i j : Word w), i.val < n → j.val < n →
    ((p t + i).val = (p u + j).val ↔ t = u ∧ i = j)

/-- Seven consecutive arrays of the same capacity satisfy the address condition. -/
theorem Regions.packed (p : Fin 8 → Word w) {base n : ℕ} (hfit : base + 7 * n ≤ 2 ^ w)
    (haddr : ∀ t : Fin 8, t ≠ 0 → (p t).val = base + (t.val - 1) * n) : Regions p n := by
  constructor
  · omega
  · intro t u ht hu i j hi hj
    have addr (c : Fin 8) (hc : c ≠ 0) (x : Word w) (hx : x.val < n) :
        (p c + x).val = base + (c.val - 1) * n + x.val := by
      have hl : (c.val - 1 + 1) * n ≤ 7 * n := Nat.mul_le_mul_right _ (by have := c.isLt; omega)
      rw [Nat.add_mul, Nat.one_mul] at hl
      rw [Fin.val_add, haddr _ hc, Nat.mod_eq_of_lt (by omega)]
    rw [addr _ ht _ hi, addr _ hu _ hj]
    constructor
    · intro he
      have ha : (t.val - 1) * n + i.val = (u.val - 1) * n + j.val := by omega
      have hi' := Nat.mul_add_mod_of_lt hi (a := t.val-1)
      have hj' := Nat.mul_add_mod_of_lt hj (a := u.val-1)
      have hij : i = j := Fin.ext (hi'.symm.trans ((congrArg (· % n) ha).trans hj'))
      subst j
      have htu := Nat.eq_of_mul_eq_mul_right (by omega : 0 < n) (Nat.add_right_cancel ha)
      have tpos : t.val ≠ 0 := fun h => ht (Fin.ext h)
      have upos : u.val ≠ 0 := fun h => hu (Fin.ext h)
      exact ⟨Fin.ext (by omega), rfl⟩
    · rintro ⟨rfl,rfl⟩; rfl

/-- `dest` permutes the scanned interval and all computed bundle totals fit in a word. -/
structure Legal (p : Fin 8 → Word w) (n : ℕ) (A : Input w) : Prop where
  dst_lt : ∀ i : Word w, i.val < n → (A.dest p i).val < n
  dst_inj : ∀ i j : Word w, i.val < n → j.val < n → A.dest p i = A.dest p j → i = j
  total_lt : ∀ i : Word w, i.val < n → prefixTotal p A i.val (bundle p i) + (A.width i).val < 2^w

/-- Exactly the directory entries reached by old outgoing slot identifiers. -/
def LiveBundle (p : Fin 8 → Word w) (n : ℕ) (b : Word w) : Prop :=
  ∃ i : Word w, i.val < n ∧ bundle p i = b

private theorem LiveBundle.lt {p : Fin 8 → Word w} {n : ℕ} {b : Word w} (h : LiveBundle p n b) : b.val < n := by
  obtain ⟨i,hi,rfl⟩ := h
  exact ((Nat.mod_le _ _).trans (Nat.div_le_self ..)).trans_lt hi

/-- Physical contents at the scan cursor. Unvisited output entries may contain arbitrary
words. Every incoming entry below the cursor is keyed by the translated destination. -/
structure AtCursor (p : Fin 8 → Word w) (n : ℕ) (A : Input w) (m : Memory w) (k : ℕ) : Prop where
  old : ∀ i : Word w, i.val < n → cell p m 1 i = A.width i
  target : ∀ b : Word w, LiveBundle p n b → cell p m 2 b = A.target b
  shift : ∀ b : Word w, LiveBundle p n b → cell p m 3 b = A.shift b
  totals : ∀ b : Word w, LiveBundle p n b → cell p m 4 b = Fin.ofNat _ (prefixTotal p A k b)
  done : ∀ i : Word w, i.val < k →
    cell p m 5 i = Fin.ofNat _ (prefixTotal p A i.val (bundle p i)) ∧
    cell p m 6 (A.dest p i) = Fin.ofNat _ (prefixTotal p A i.val (bundle p i)) ∧
    cell p m 7 (A.dest p i) = A.width i

/-- At cursor zero only the old tables and zeroed bundle totals need initialization. -/
theorem AtCursor.start {p : Fin 8 → Word w} {n : ℕ} {A : Input w} {m : Memory w}
    (old : ∀ i : Word w, i.val < n → cell p m 1 i = A.width i)
    (target : ∀ b : Word w, LiveBundle p n b → cell p m 2 b = A.target b)
    (shift : ∀ b : Word w, LiveBundle p n b → cell p m 3 b = A.shift b)
    (totals : ∀ b : Word w, LiveBundle p n b → cell p m 4 b = 0) : AtCursor p n A m 0 :=
  ⟨old, target, shift, totals, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩

/-- Under the one-word width bound the two offset cells carry the exact natural prefix. -/
theorem AtCursor.exact {p : Fin 8 → Word w} {n k : ℕ} {A : Input w} {m : Memory w}
    (h : AtCursor p n A m k) (legal : Legal p n A) (hk : k ≤ n) (i : Word w) (hi : i.val < k) :
    (cell p m 5 i).val = prefixTotal p A i.val (bundle p i) ∧
      (cell p m 6 (A.dest p i)).val = prefixTotal p A i.val (bundle p i) ∧
      cell p m 7 (A.dest p i) = A.width i := by
  obtain ⟨out,inc,len⟩ := h.done i hi
  have fit := (Nat.le_add_right _ _).trans_lt (legal.total_lt i (hi.trans_le hk))
  exact ⟨(congrArg Fin.val out).trans (Nat.mod_eq_of_lt fit),
    (congrArg Fin.val inc).trans (Nat.mod_eq_of_lt fit), len⟩

private theorem bundle_le (p : Fin 8 → Word w) (i : Word w) : (bundle p i).val ≤ i.val :=
  (Nat.mod_le _ _).trans (Nat.div_le_self ..)

private theorem destination_at {p : Fin 8 → Word w} {A : Input w} {n k : ℕ} {m : Memory w}
    (h : AtCursor p n A m k) (i : Word w) (hi : i.val < n) : destination p m i = A.dest p i := by
  have hb : LiveBundle p n (bundle p i) := ⟨i,hi,rfl⟩
  change cell p m 2 (bundle p i) * _ + BinaryOp.bitXor.eval _ (cell p m 3 (bundle p i)) = _
  rw [h.target _ hb, h.shift _ hb]
  rfl

private theorem cell_update {p : Fin 8 → Word w} {A : Input w} {n : ℕ} {m : Memory w}
    (reg : Regions p n) (legal : Legal p n A) (i : Word w) (hi : i.val < n)
    (h : AtCursor p n A m i.val) (t : Fin 8) (ht : t ≠ 0) (x : Word w) (hx : x.val < n) :
    let b := bundle p i
    let off : Word w := Fin.ofNat _ (prefixTotal p A i.val b)
    cell p (update p m i) t x =
      if t = 4 ∧ x = b then off + A.width i
      else if t = 7 ∧ x = A.dest p i then A.width i
      else if t = 6 ∧ x = A.dest p i then off
      else if t = 5 ∧ x = i then off else cell p m t x := by
  have hb := (bundle_le p i).trans_lt hi
  have hd := legal.dst_lt i hi
  have hd' := destination_at h i hi
  have h₁ := h.old i hi
  have h₄ := h.totals _ ⟨i,hi,rfl⟩
  dsimp only [cell] at h₁ h₄ ⊢
  simp only [update, hd', h₁, h₄, writeMemory, reg.apart t 4 ht (by decide) x _ hx hb,
    reg.apart t 7 ht (by decide) x _ hx hd, reg.apart t 6 ht (by decide) x _ hx hd,
    reg.apart t 5 ht (by decide) x i hx hi]

/-- A native segment visit preserves the scan invariant. -/
theorem cursor_step {p : Fin 8 → Word w} {A : Input w} {n : ℕ} {m : Memory w}
    (reg : Regions p n) (legal : Legal p n A) (i : Word w) (hi : i.val < n)
    (h : AtCursor p n A m i.val) : AtCursor p n A (update p m i) (i.val+1) := by
  have step := cell_update reg legal i hi h
  have castI : Fin.ofNat (2^w) i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  constructor
  · intro j hj; simpa using (step 1 (by decide) j hj).trans (by simpa using h.old j hj)
  · intro j hj; simpa using (step 2 (by decide) j hj.lt).trans (by simpa using h.target j hj)
  · intro j hj; simpa using (step 3 (by decide) j hj.lt).trans (by simpa using h.shift j hj)
  · intro b hb
    rw [step 4 (by decide) b hb.lt]
    by_cases he : b = bundle p i
    · subst b
      simp only [prefixTotal, castI, true_and, ite_true]
      apply Fin.ext
      simp [Fin.val_add, Fin.ofNat, Nat.mod_add_mod]
    · simpa [prefixTotal, castI, he, Ne.symm he] using h.totals b hb
  · intro j hj
    have hjn : j.val < n := by omega
    have hd := legal.dst_lt j hjn
    rw [step 5 (by decide) j hjn, step 6 (by decide) (A.dest p j) hd, step 7 (by decide) (A.dest p j) hd]
    by_cases he : j = i
    · subst j; simp
    · have hn : A.dest p j ≠ A.dest p i := fun hh => he (legal.dst_inj j i hjn hi hh)
      have hlt : j.val < i.val := by have := Fin.val_ne_of_ne he; omega
      simpa [he, hn] using h.done j hlt

/-- The external pass writes the total and three segment columns, indexed below `n`. -/
def outsideScan (p : Fin 8 → Word w) (n addr : ℕ) : Prop :=
  ∀ t : Fin 8, 4 ≤ t.val → ∀ i : Word w, i.val < n → addr ≠ (p t + i).val

/-- All native calls of the external scan and all records through the resulting cursor. -/
theorem scan_run {p : Fin 8 → Word w} {A : Input w} {n k : ℕ} {m : Memory w}
    (reg : Regions p n) (legal : Legal p n A) (h : AtCursor p n A m k)
    (steps : ℕ) (hb : k + steps ≤ n) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 33 (some (Fin.ofNat (2^w) k)) m (List.replicate steps []) = some rs ∧
      AtCursor p n A (after m (eventLog rs)) (k + steps) ∧
      (∀ addr, outsideScan p n addr → after m (eventLog rs) addr = m addr) ∧ rs.length = steps ∧
      ∀ r ∈ rs, r.events.length = 32 ∧ countProbes r.events = 8 := by
  let M := (template visit 0).instantiate w p
  induction steps generalizing k m with
  | zero => exact ⟨[], rfl, h, fun _ _ => rfl, rfl, by simp⟩
  | succ s ih =>
    let i := Fin.ofNat (2^w) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by have := reg.fits; omega)
    have hi : i.val < n := by omega
    have hn := cursor_step reg legal i hi (hv ▸ h)
    have hn' : i + 1 = Fin.ofNat (2^w) (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', hv, Nat.add_mod_mod]
      rfl
    let r : Report w := ⟨events p m i, some (i+1)⟩
    obtain ⟨rs,hr,hc,frame,hlen,hw⟩ := ih (k := k+1) (hv ▸ hn) (by omega)
    have hm : after m (eventLog (r :: rs)) = after (update p m i) (eventLog rs) := by
      change List.foldl BurstRAM.update m (events p m i ++ eventLog rs) = _
      rw [List.foldl_append]; rfl
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hlen], ?_⟩
    · change runSegment M.program 33 (some i) m (List.replicate (s+1) []) = _
      rw [List.replicate_succ, runSegment, visit_native p m i]
      simp only [M, r, events_after, hn', hr, Option.map_some]
    · simpa [hm, Nat.add_assoc, Nat.add_comm 1 s] using hc
    · intro addr outside
      rw [hm, frame addr outside]
      have hd : (destination p m i).val < n := (destination_at (hv ▸ h) i hi) ▸ legal.dst_lt i hi
      simp only [update, writeMemory, ite_eq_right (outside 4 (by decide) _ ((bundle_le p i).trans_lt hi)),
        ite_eq_right (outside 7 (by decide) _ hd), ite_eq_right (outside 6 (by decide) _ hd),
        ite_eq_right (outside 5 (by decide) _ hi)]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact events_work p m i
      · exact hw q hq

/-- The exact call-plus-probe cost through all visited segments. -/
theorem scan_cost {rs : List (Report w)} (h : ∀ r ∈ rs, countProbes r.events = 8) :
    RAMBuckets.cost (fun r : Report w => countProbes r.events) rs = 9 * rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [RAMBuckets.cost, h r (List.mem_cons_self ..), ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      List.length_cons, Nat.mul_succ]
    omega

end CompressorRecords.RefreshRAM

end VPVNP
end Computability
end OAI
