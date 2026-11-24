import OAI.Computability.VPVNP.CompressorRecordRefreshExternal
import OAI.Computability.VPVNP.DegreeRefreshPass

/-!
# Gathering the old actual widths in source-port order

The old directory stores widths by site and outgoing slot. The degree refresh consumes
a port prefix of the old lane. A scan decodes the bundle, residual lane and port fields,
reads each old slot’s width directly and writes it in source-port order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

private def digits : List (ZMod 2) → ℕ
  | [] => 0
  | b :: bs => b.val * 2 ^ bs.length + digits bs

private theorem digits_append (u v : List (ZMod 2)) :
    digits (u ++ v) = digits u * 2 ^ v.length + digits v := by
  induction u with
  | nil => simp [digits]
  | cons b u ih => simp only [List.cons_append, digits, List.length_append, pow_add, ih]; ring

private theorem digits_ofFn {n : ℕ} (x : BitWord n) : digits (List.ofFn x) = (bitWordFinEquiv n x).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, digits, List.length_ofFn, bitWordFinEquiv_val, ← ih (Fin.tail x)]
    change _ * _ + digits (List.ofFn (Fin.tail x)) = _
    rw [Nat.mul_comm, Nat.add_comm]

/-- The port is the high field of the old lane number and the residual lane its low field. -/
theorem splitBitWord_number (a g : ℕ) (x : BitWord (a+g)) :
    (bitWordFinEquiv (a+g) x).val =
      (bitWordFinEquiv a ((splitBitWord a g x).1)).val * 2 ^ g + (bitWordFinEquiv g ((splitBitWord a g x).2)).val := by
  rw [← digits_ofFn, List.ofFn_add, digits_append, List.length_ofFn, digits_ofFn, digits_ofFn]
  rfl

end Compression

namespace CompressorRecords.RefreshGather

open Compression BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Source order is `(base arc, residual lane, port)`. The old width column uses
`(base vertex, port, residual lane, slot)`. -/
def oldIndex (D R i : Word w) : Word w :=
  let b := BinaryOp.div.eval i D
  let port := BinaryOp.mod.eval i D
  let arc := BinaryOp.div.eval b R
  ((BinaryOp.div.eval arc D * D + port) * R + BinaryOp.mod.eval b R) * D + BinaryOp.mod.eval arc D

theorem oldIndex_val (D R i : Word w) {x j g : ℕ} (hj : j < D.val) (hg : g < R.val)
    (hi : i.val = (x * R.val + g) * D.val + j) :
    (oldIndex D R i).val = (((x / D.val * D.val + j) * R.val + g) * D.val + x % D.val) % 2^w := by
  have divVal (a b : Word w) : (BinaryOp.div.eval a b).val = a.val / b.val :=
    Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt a.isLt)
  have modVal (a b : Word w) : (BinaryOp.mod.eval a b).val = a.val % b.val :=
    Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt a.isLt)
  have hd : 0 < D.val := (Nat.zero_le j).trans_lt hj
  have hr : 0 < R.val := (Nat.zero_le g).trans_lt hg
  have hrow : i.val % D.val = j := hi ▸ Nat.mul_add_mod_of_lt hj
  have hb : i.val / D.val = x * R.val + g := by
    rw [hi, Nat.mul_comm _ D.val, Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hbase : (x * R.val + g) / R.val = x := by
    rw [Nat.mul_comm x, Nat.mul_add_div hr, Nat.div_eq_of_lt hg, Nat.add_zero]
  simp only [oldIndex, Fin.val_add, Fin.val_mul, divVal, modVal, hb, hbase, hrow,
    Nat.mul_add_mod_of_lt hg, Nat.mod_add_mod, Nat.mod_mul_mod ]

/-- Public fields are port count, residual-lane count, old actual-width base and new
width-array base. Persistent state is the source-ordered segment index. -/
def gather : List (Op 9 4) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .binary .div 3 0 1, .binary .mod 4 0 1,
    .binary .div 5 3 2, .binary .mod 6 3 2, .binary .mod 7 5 1, .binary .div 5 5 1,
    .binary .mul 5 5 1, .binary .add 5 5 4, .binary .mul 5 5 2, .binary .add 5 5 6,
    .binary .mul 5 5 1, .binary .add 5 5 7, .publicWord 7 2, .binary .add 7 7 5,
    .read 6 7, .publicWord 7 3, .binary .add 7 7 0, .write 7 6,
    .constant 8 1, .binary .add 0 0 8]

/-- Locate an old actual width by converting a source-ordered segment ordinal to its old
outgoing-slot index. -/
def widthAddress (p : Fin 4 → Word w) (i : Word w) := p 2 + oldIndex (p 0) (p 1) i

/-- Read the old actual width selected by a segment ordinal. -/
def readWidth (p : Fin 4 → Word w) (m : Memory w) (i : Word w) := m (widthAddress p i).val

/-- The 23-event gather visit reads the old slot width and writes it at the source-ordered
segment index. -/
def events (p : Fin 4 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let a := widthAddress p i
  [.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,.tick,
    .read a (m a.val),.tick,.tick,.write (p 3 + i) (m a.val),.tick,.tick]

theorem gather_work (p : Fin 4 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 23 ∧ countProbes (events p m i) = 2 := ⟨rfl,rfl⟩

theorem gather_after (p : Fin 4 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) = writeMemory m (p 3 + i) (readWidth p m i) := rfl

private theorem gather_trace (p : Fin 4 → Word w) (m : Memory w) (i : Word w) (regs : Regs w 9) :
    ∃ rs, trace p i gather regs m = some (events p m i, rs, writeMemory m (p 3+i) (readWidth p m i)) ∧
      rs 0 = i + 1 := by
  simp (config := {decide := true}) [gather, trace, Op.effect, BinaryOp.eval, Function.update, events,
    widthAddress, readWidth, oldIndex]
  rfl

/-- A complete native call fetches the named old width, writes the source-ordered width
and returns the next segment number. -/
theorem gather_native (p : Fin 4 → Word w) (m : Memory w) (i : Word w) :
    let M := (template gather 0).instantiate w p
    execute M.program 24 (M.program.start i) m [] = some ⟨events p m i, some (i+1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := gather_trace p m i (fun _ => 0)
  let M := (template gather 0).instantiate w p
  change execute M.program (1 + gather.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]; simp [hr]

/-- The old and new width columns occupy distinct cells. -/
def SourcesDisjoint (p : Fin 4 → Word w) (n : ℕ) : Prop :=
  ∀ (i j : Word w), i.val < n → j.val < n →
    (widthAddress p i).val ≠ (p 3 + j).val

/-- Completed rows and the exact frame after `k` gather calls. -/
structure Gathered (p : Fin 4 → Word w) (old m : Memory w) (k : ℕ) : Prop where
  rows : ∀ i : Word w, i.val < k → m (p 3 + i).val = readWidth p old i
  frame : ∀ addr : ℕ, (∀ i : Word w, i.val < k → addr ≠ (p 3 + i).val) → m addr = old addr

private theorem gather_step {p : Fin 4 → Word w} {n : ℕ} {old m : Memory w}
    (apart : SourcesDisjoint p n) (i : Word w) (hi : i.val < n) (h : Gathered p old m i.val) :
    Gathered p old (writeMemory m (p 3 + i) (readWidth p m i)) (i.val+1) := by
  have hr : readWidth p m i = readWidth p old i :=
    h.frame _ (fun j hj => apart i j hi (hj.trans hi))
  constructor
  · intro j hj
    by_cases he : i = j
    · subst j; simpa [writeMemory] using hr
    · have hne : (p 3 + j).val ≠ (p 3 + i).val := fun hv => he (add_left_cancel (Fin.ext hv)).symm
      rw [writeMemory, ite_eq_right hne]
      exact h.rows j (by have := Fin.val_ne_of_ne he; omega)
  · intro addr outside
    rw [writeMemory, ite_eq_right (outside i (Nat.lt_succ_self _))]
    exact h.frame addr (fun j hj => outside j (Nat.lt_succ_of_lt hj))

/-- The full native gather pass copies every width and changes only completed output rows. -/
theorem gather_run {p : Fin 4 → Word w} {n k : ℕ} {old m : Memory w}
    (fit : n ≤ 2^w) (apart : SourcesDisjoint p n) (h : Gathered p old m k)
    (steps : ℕ) (hk : k + steps ≤ n) :
    let M := (template gather 0).instantiate w p
    ∃ rs, runSegment M.program 24 (some (Fin.ofNat (2^w) k)) m (List.replicate steps []) = some rs ∧
      Gathered p old (after m (eventLog rs)) (k + steps) ∧ rs.length = steps ∧
      ∀ r ∈ rs, r.events.length = 23 ∧ countProbes r.events = 2 := by
  let M := (template gather 0).instantiate w p
  induction steps generalizing k m with
  | zero => exact ⟨[], rfl, h, rfl, by simp⟩
  | succ s ih =>
    let i := Fin.ofNat (2^w) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by omega)
    have next := gather_step apart i (by omega) (hv ▸ h)
    have hn : i + 1 = Fin.ofNat (2^w) (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', hv, Nat.add_mod_mod]; rfl
    let r : Report w := ⟨events p m i, some (i+1)⟩
    obtain ⟨rs,hr,hc,hl,hw⟩ := ih (k := k+1) (hv ▸ next) (by omega)
    refine ⟨r :: rs, ?_, ?_, by simp [hl], ?_⟩
    · change runSegment M.program 24 (some i) m (List.replicate (s+1) []) = _
      rw [List.replicate_succ, runSegment, gather_native p m i]
      simp only [M, r, gather_after, hn, hr, Option.map_some]
    · have he : after m (eventLog (r :: rs)) =
          after (writeMemory m (p 3 + i) (readWidth p m i)) (eventLog rs) := by
        change List.foldl BurstRAM.update m (events p m i ++ eventLog rs) = _
        rw [List.foldl_append]; rfl
      simpa [he, Nat.add_assoc, Nat.add_comm 1 s] using hc
    · intro rep hrep
      rcases List.mem_cons.mp hrep with rfl | hr
      · exact gather_work p m i
      · exact hw rep hr

/-- A segment read reaches the exact old outgoing slot in the unsplit lane numbering. -/
theorem original_lane_index {a g : ℕ} (p : Fin 4 → Word w) (i : Word w) (arc : ℕ)
    (oldLane : BitWord (a+g)) (hd : (p 0).val = 2^a) (hg : (p 1).val = 2^g)
    (hi : i.val = (arc * 2^g + (bitWordFinEquiv g ((splitBitWord a g oldLane).2)).val) * 2^a +
      (bitWordFinEquiv a ((splitBitWord a g oldLane).1)).val)
    : oldIndex (p 0) (p 1) i = Fin.ofNat _
        ((arc / 2^a * 2^(a+g) + (bitWordFinEquiv (a+g) oldLane).val) * 2^a + arc % 2^a) := by
  apply Fin.ext
  rw [splitBitWord_number, pow_add]
  have key := oldIndex_val (p 0) (p 1) i (x := arc)
    (j := (bitWordFinEquiv a ((splitBitWord a g oldLane).1)).val)
    (g := (bitWordFinEquiv g ((splitBitWord a g oldLane).2)).val)
    (by rw [hd]; exact (bitWordFinEquiv a _).isLt) (by rw [hg]; exact (bitWordFinEquiv g _).isLt)
    (by simpa only [hd,hg] using hi)
  rw [key,hd,hg]
  congr 1
  ring

open Refresh (groupedWidths splitWidths)
open PortRefresh

/-- Widths at the directly addressed old sites and outgoing slots. -/
def HasOldWidths {a g n : ℕ} (X : State a (a+g)) (base : X.Base × Fin (2^a) ≃ Fin n)
    (p : Fin 4 → Word w) (m : Memory w) : Prop :=
  ∀ (b : X.Base × Fin (2^a)) (l : BitWord (a+g)),
    let oldArc := (base b).val
    let key := (oldArc / 2^a * 2^(a+g) + (bitWordFinEquiv (a+g) l).val) * 2^a + oldArc % 2^a
    (m (p 2 + Fin.ofNat (2^w) key).val).val = X.width (b,l)

/-- The physical width read by the gather call is precisely the source-port field of the
actual dyadic compression state in the common incidence-directory format. -/
theorem read_state_width {a g n : ℕ} (X : State a (a+g)) (base : X.Base × Fin (2^a) ≃ Fin n)
    (ord : (X.Base × BitWord g) × Fin (2^a) ≃ Fin (n*2^g))
    (ho : ∀ b, (ord b).val = (base (b.1.1,b.2)).val * 2^g + (bitWordFinEquiv g b.1.2).val)
    (p : Fin 4 → Word w) (m : Memory w) (old : HasOldWidths X base p m)
    (hd : (p 0).val = 2^a) (hg : (p 1).val = 2^g) (fit : n*2^g*2^a ≤ 2^w)
    (e : DyadicArc X.Base (BitWord g) a) :
    (readWidth p m (idWord ord fit e)).val = groupedWidths (bitWordFinEquiv a) (splitWidths X) e := by
  obtain ⟨⟨⟨v,g'⟩,s⟩,j⟩ := e
  let lane := (splitBitWord a g).symm ((bitWordFinEquiv a).symm j,g')
  let b := ((v,g'),s)
  let i := idWord ord fit (b,j)
  have hi : i.val = ((base (v,s)).val * 2^g + (bitWordFinEquiv g g').val) * 2^a + j.val := by
    change (numbered ord (b,j)).val = _
    rw [numbered_val, ho]
  have hold := original_lane_index p i (base (v,s)).val lane hd hg
    (by simpa [lane] using hi)
  change (m (p 2 + oldIndex (p 0) (p 1) i).val).val = X.width ((v,s),lane)
  rw [hold]
  exact old (v,s) lane

end CompressorRecords.RefreshGather

end VPVNP
end Computability
end OAI
