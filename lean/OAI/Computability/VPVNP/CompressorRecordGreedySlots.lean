import OAI.Computability.VPVNP.CompressorRecordGreedy
import OAI.Computability.VPVNP.SlotGreedyScan
import OAI.Computability.VPVNP.BitSlotXor

/-!
# Descriptor rows for the greedy vertex scan

Each record lists addresses of the fields needed for its comparisons.
The pointer-row invariant is independent of the current partial assignment.
Reading through those pointers in the native template recovers the forbidden
indices of the mathematical scan, including at as-yet unassigned neighbors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.SlotGraph

variable {w : ℕ}

/-- Consecutive descriptor words, in word-address order. -/
def Stores (m : Memory w) : Word w → List (Word w) → Prop
  | _, [] => True
  | base, x :: xs => m base.val = x ∧ Stores m (base + 1) xs

/-- Advance a word address by one cell for each of the given number of steps. -/
def advance : Word w → ℕ → Word w
  | base, 0 => base
  | base, n + 1 => advance (base + 1) n

theorem stores_append (m : Memory w) (base : Word w) (xs ys : List (Word w)) :
    Stores m base (xs ++ ys) ↔ Stores m base xs ∧ Stores m (advance base xs.length) ys := by
  induction xs generalizing base with
  | nil => simp [Stores, advance]
  | cons x xs ih => simp [Stores, advance, ih, and_assoc]

/-- Dereference each operand address before taking the bitwise sum. -/
def rowValue (m : Memory w) (xs : List (Word w)) (acc : Word w) : Word w :=
  xs.foldl (fun v p => BinaryOp.bitXor.eval v (m p.val)) acc

theorem readExpression_stored {m : Memory w} {base : Word w} {xs : List (Word w)}
    (hs : Stores m base xs) (acc : Word w) :
    readExpression m xs.length base acc = (advance base xs.length, rowValue m xs acc) := by
  induction xs generalizing base acc with
  | nil => rfl
  | cons x xs ih => simp [readExpression, advance, rowValue, hs.1, ih hs.2]

theorem readRows_stored (m : Memory w) (arity : ℕ) (base : Word w)
    (rows : List (List (Word w))) (size : ∀ row ∈ rows, row.length = arity)
    (hs : Stores m base rows.flatten) :
    readRows m arity rows.length base = rows.map (fun row => rowValue m row 0) := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨hrow, hrest⟩ := (stores_append m base row rows.flatten).mp hs
    have hlen := size row List.mem_cons_self
    simp only [List.length_cons, readRows, ← hlen, readExpression_stored hrow, List.map_cons]
    congr 1
    simpa only [← hlen] using ih _ (fun r hr => size r (List.mem_cons_of_mem _ hr)) hrest

/-- The result and the exact accounting of the call from a fresh private state. -/
def Returns (m : Memory w) (base : Word w) (arity n result : ℕ) : Prop :=
  let code := chooseFromState arity n
  let M := (template code 2).instantiate w Fin.elim0
  ∃ es, execute M.program (1 + code.length) (M.program.start base) m [] =
      some ⟨es, some (Fin.ofNat _ result)⟩ ∧
    es.length = 3 + ((4 * arity + 4) * n + 4) * n ∧ countProbes es = 2 * arity * n * n

private theorem indexed_returns {T : Type*} {J : ℕ} (tests : List T) (covers : ∀ t, t ∈ tests)
    (forbid : T → Fin J) (chosen : Fin J) (absent : ∀ t, chosen ≠ forbid t)
    (early : ∀ k < chosen, ∃ t, forbid t = k)
    (m : Memory w) (base : Word w) (arity : ℕ) (ptrs : T → List (Word w))
    (hlen : ∀ t, (ptrs t).length = arity) (hs : Stores m base (tests.map ptrs).flatten)
    (hvalue : ∀ t, (rowValue m (ptrs t) 0).val = (forbid t).val)
    (hfit : tests.length < 2 ^ w) :
    Returns m base arity tests.length chosen.val := by
  have hread := readRows_stored m arity base (tests.map ptrs)
    (by intro row hr; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr; exact hlen _) hs
  simp only [List.length_map] at hread
  have hm (i : ℕ) : i ∈ (readRows m arity tests.length base).map Fin.val ↔
      ∃ t, (forbid t).val = i := by
    rw [hread]
    simp only [List.map_map, List.mem_map, Function.comp_apply, hvalue, covers, true_and]
  apply choose_native m base arity tests.length chosen.val hfit
  · intro h
    obtain ⟨t, he⟩ := (hm _).mp h
    exact absent t (Fin.ext he.symm)
  · intro i hi
    obtain ⟨t, ht⟩ := early (⟨i, hi.trans chosen.isLt⟩ : Fin J) hi
    exact (hm _).mpr ⟨t, congrArg Fin.val ht⟩

variable {V : Type*} {d : ℕ}

/-- Direction then local port, with both incidences even on a parallel edge. -/
def incidences (d : ℕ) : List (Bool × Fin d) := [true, false] ×ˢ List.finRange d

@[simp] theorem incidences_length (d : ℕ) : (incidences d).length = 2 * d := by
  simp [incidences, two_mul]

theorem incidences_cover (t : Bool × Fin d) : t ∈ incidences d := by
  obtain ⟨b, i⟩ := t; cases b <;> simp [incidences]

/-- Find the adjacent vertex at a directed incidence, following the target for outgoing ports
or its inverse for incoming ports. -/
def neighbor (G : SlotGraph V d) (x : V) : Bool × Fin d → V
  | (true, i) => (G.target (x, i)).1
  | (false, i) => (G.target.symm (x, i)).1

/-- Every color row has one operand, the address of the neighboring label. -/
def colorRows (G : SlotGraph V d) (x : V) (address : V → Word w) :
    List (List (Word w)) := (incidences d).map fun t => [address (neighbor G x t)]

theorem color_returns (G : SlotGraph V d) (x : V) (f : V → Fin (2 * d + 1))
    (m : Memory w) (base : Word w) (address : V → Word w)
    (labels : ∀ y, (m (address y).val).val = (f y).val)
    (stored : Stores m base (colorRows G x address).flatten) (hfit : 2 * d < 2 ^ w) :
    Returns m base 1 (2 * d) (G.chooseColor x f).val := by
  obtain ⟨habs, hearly⟩ := G.chooseColor_spec x f
  have hval (t : Bool × Fin d) :
      (rowValue m [address (neighbor G x t)] 0).val = (G.colorForbidden x f t).val := by
    have h (v : Word w) : BinaryOp.bitXor.eval 0 v = v := by
      apply Fin.ext
      simp [BinaryOp.eval]
    obtain ⟨b, i⟩ := t
    cases b <;> simp [rowValue, h, labels, neighbor, colorForbidden]
  simpa using indexed_returns (incidences d) incidences_cover (G.colorForbidden x f)
    (G.chooseColor x f) habs hearly m base 1 (fun t => [address (neighbor G x t)])
    (fun _ => rfl) stored hval (by simpa using hfit)

/-- Enumerate zero and all the outgoing tag increments, with multiplicities. -/
def increments (d : ℕ) : List (Option (Fin d)) := none :: (List.finRange d).map some

private theorem increments_cover (a : Option (Fin d)) : a ∈ increments d := by
  cases a <;> simp [increments]

/-- Local exclusions come first, followed by all pairs of increments. -/
def tagTests (d : ℕ) : List (TagTests d) :=
  incidences d ×ˢ ((increments d).map Sum.inl ++ (increments d ×ˢ increments d).map Sum.inr)

@[simp] theorem tagTests_length (d : ℕ) :
    (tagTests d).length = 2 * d * ((d + 1) + (d + 1) ^ 2) := by
  simp [tagTests, List.length_product, increments, pow_two]
  exact Or.inl (by ring)

theorem tagTests_cover (t : TagTests d) : t ∈ tagTests d := by
  obtain ⟨p, a | ⟨a, b⟩⟩ := t <;>
    simp [tagTests, List.mem_product, incidences_cover, increments_cover]


/-- The immutable displacement cells and the current mutable assignment cells. -/
structure TagAddresses (V : Type*) (d w : ℕ) where
  /-- Address of the constant zero word used for absent tag increments. -/
  zero : Word w
  /-- Address of the displacement word for a specified outgoing arc. -/
  displacement : V × Fin d → Word w
  /-- Address of the current tag assignment for a specified vertex. -/
  label : V → Word w

/-- Select the displacement address for a present local port and the zero cell for an absent
port. -/
def TagAddresses.increment (A : TagAddresses V d w) (x : V) : Option (Fin d) → Word w
  | none => A.zero
  | some i => A.displacement (x, i)

/-- The four operands of a local or a two-end tag exclusion. Padding a local
test with two references to the zero cell permits one fixed instruction table. -/
def tagPointers (G : SlotGraph V d) (A : TagAddresses V d w) (x : V) : TagTests d → List (Word w)
  | ((true, i), .inl a) => [A.displacement (x, i), A.increment x a, A.zero, A.zero]
  | ((false, i), .inl a) => [A.displacement (G.target.symm (x, i)), A.increment x a, A.zero, A.zero]
  | ((true, i), .inr (a, b)) =>
    let y := (G.target (x, i)).1
    [A.displacement (x, i), A.increment x a, A.increment y b, A.label y]
  | ((false, i), .inr (a, b)) =>
    let e := G.target.symm (x, i)
    [A.displacement e, A.increment e.1 a, A.increment x b, A.label e.1]

variable {j : ℕ}

/-- The addressed cells contain zero and the word encodings of the specified displacements and
vertex tags. -/
structure TagAddresses.Represents (A : TagAddresses V d w) (hw : j ≤ w)
    (m : Memory w) (τ : V × Fin d → BitWord j) (f : V → BitWord j) : Prop where
  zero : m A.zero.val = 0
  displacement : ∀ e, m (A.displacement e).val = tagWord hw (τ e)
  label : ∀ y, m (A.label y).val = tagWord hw (f y)

theorem tagPointers_value (G : SlotGraph V d) (A : TagAddresses V d w)
    (hw : j ≤ w) (m : Memory w) (τ : V × Fin d → BitWord j) (f : V → BitWord j)
    (rep : A.Represents hw m τ f) (x : V) (t : TagTests d) :
    rowValue m (tagPointers G A x t) 0 = tagWord hw (G.tagForbidden τ x f t) := by
  have inc (y : V) (a : Option (Fin d)) :
      m (A.increment y a).val = tagWord hw (tagIncrement τ y a) := by
    cases a with
    | none => simpa [TagAddresses.increment, tagIncrement] using rep.zero
    | some i => exact rep.displacement (y, i)
  have zx (u : Word w) : BinaryOp.bitXor.eval 0 u = u := by apply Fin.ext; simp [BinaryOp.eval]
  have xz (u : Word w) : BinaryOp.bitXor.eval u 0 = u := by apply Fin.ext; simp [BinaryOp.eval]
  have neg (u : BitWord j) : -u = u := funext fun i => CharTwo.neg_eq (u i)
  obtain ⟨⟨b, i⟩, a | ⟨a, c⟩⟩ := t
  all_goals cases b
  all_goals simp only [rowValue, tagPointers, List.foldl_cons, List.foldl_nil, zx, tagForbidden,
    rep.displacement, inc, rep.zero, xz, rep.label, tagWord_xor, sub_eq_add_neg, neg]

/-- For a partially filled offset table the native output is exactly the
index used by the next visit in `orderedTagOffsets`. -/
theorem tag_returns (G : SlotGraph V d) (x : V) (τ : V × Fin d → BitWord j) (f : V → BitWord j)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < 2 ^ j) (hw : j ≤ w)
    (m : Memory w) (base : Word w) (A : TagAddresses V d w) (rep : A.Represents hw m τ f)
    (stored : Stores m base ((tagTests d).map (tagPointers G A x)).flatten) :
    Returns m base 4 (2 * d * ((d + 1) + (d + 1) ^ 2))
      (bitWordFinEquiv j (G.chooseTag (bitWordFinEquiv j) τ hcard x f)).val := by
  obtain ⟨habs, hearly⟩ := G.chooseTag_spec (bitWordFinEquiv j) τ hcard x f
  have size (t : TagTests d) : (tagPointers G A x t).length = 4 := by
    obtain ⟨⟨b, i⟩, a | ⟨a, c⟩⟩ := t <;> cases b <;> rfl
  simpa using indexed_returns (tagTests d) tagTests_cover
    (fun t => bitWordFinEquiv j (G.tagForbidden τ x f t))
    (bitWordFinEquiv j (G.chooseTag (bitWordFinEquiv j) τ hcard x f)) habs hearly m base 4
    (tagPointers G A x) size stored
    (fun t => congrArg Fin.val (tagPointers_value G A hw m τ f rep x t))
    (by simpa using hcard.trans_le (Nat.pow_le_pow_right (by decide) hw))


theorem Returns.visit {m : Memory w} {base : Word w} {arity n result : ℕ}
    (hr : Returns m (base + 1 + 1) arity n result) (hfit : n < 2 ^ w) :
    Visit m base arity n (Fin.ofNat _ result) := by
  let rows := base + 1 + 1
  obtain ⟨events, he, _, _⟩ := hr
  let M := (template (chooseFromState arity n) 2).instantiate w Fin.elim0
  change execute M.program (1 + (chooseFromState arity n).length)
    ⟨M.entry, rows, fun _ => 0, fun _ => 0⟩ m [] = _ at he
  let rs : Regs w 8 := Function.update (fun _ => 0) 0 rows
  obtain ⟨es, c, hc, _, _, hv⟩ := choose_trace rows m arity n rs hfit
  have hi : trace Fin.elim0 rows [.stateWord 0] (fun _ : Fin 8 => 0) m =
      some ([.tick], rs, m) := rfl
  rw [execute_template, run_eq_trace, chooseFromState, trace_append, hi] at he
  simp only [Option.bind_some, hc, Option.map_some, Option.some.injEq, Report.mk.injEq] at he
  apply visit_native _ _ _ _ _ hfit
  have hval := congrArg Fin.val he.2
  simpa [rs, rows] using hv.symm.trans hval

theorem color_visit (G : SlotGraph V d) (x : V) (f : V → Fin (2 * d + 1))
    (m : Memory w) (base : Word w) (address : V → Word w)
    (labels : ∀ y, (m (address y).val).val = (f y).val)
    (stored : Stores m (base + 1 + 1) (colorRows G x address).flatten) (hfit : 2 * d < 2 ^ w) :
    Visit m base 1 (2 * d) (Fin.ofNat _ (G.chooseColor x f).val) :=
  (color_returns G x f m _ address labels stored hfit).visit hfit

theorem tag_visit (G : SlotGraph V d) (x : V) (τ : V × Fin d → BitWord j) (f : V → BitWord j)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < 2 ^ j) (hw : j ≤ w)
    (m : Memory w) (base : Word w) (A : TagAddresses V d w) (rep : A.Represents hw m τ f)
    (stored : Stores m (base + 1 + 1) ((tagTests d).map (tagPointers G A x)).flatten) :
    Visit m base 4 (2 * d * ((d + 1) + (d + 1) ^ 2))
      (tagWord hw (G.chooseTag (bitWordFinEquiv j) τ hcard x f)) := by
  let t := G.chooseTag (bitWordFinEquiv j) τ hcard x f
  have h : Fin.ofNat (2 ^ w) (bitWordFinEquiv j t).val = tagWord hw t := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (tagWord hw t).isLt
  rw [← h]
  exact (tag_returns G x τ f hcard hw m _ A rep stored).visit
    (hcard.trans_le (Nat.pow_le_pow_right (by decide) hw))

end CompressorRecords.Greedy

end VPVNP
end Computability
end OAI
