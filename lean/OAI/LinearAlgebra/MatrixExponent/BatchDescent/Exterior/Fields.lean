import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Header
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Observed

/-!
# Summing the port tape

Use an independent service to check the original exterior positions.
The zero pad outside the image of the pin embedding ensures that every
setting of the free interior wires contributes once.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Assembly Coloring Transcript Classical

variable {F X : Type} [Field F] {S : Scheme F} {r : S.format.obj}
    {u v K p d a : ℕ} {l : Inventory (2 ^ S.m) (2 ^ S.h) d}

namespace Wires
variable (T : Wires S u v K p a (X ⊕ Tape u v K p))

def correctPacket (A : Pieces S r l v p) (L : PackRows.Layout l u v K)
    (π : PacketPlan (Address v K) a) : Prop :=
  ∀ y : Tape u v K p → Bool, Links.pad (A.inside L) y →
    ((∀ i, (π.head i).1 = true → Function.curry y (π.peer i) = Function.curry y i) ↔
      ∀ i j, S.Joins r i j → y (A.inside L i) = y (A.inside L j))

def correctExterior (A : Pieces S r l v p) (L : PackRows.Layout l u v K) (z : S.exposed r → Bool)
    (g : (X ⊕ Tape u v K p → Bool) → F) (x : X → Bool) : Prop :=
  ∀ y, Links.pad (A.inside L) y →
    g (Sum.elim x y) = if ∀ i, y (A.inside L i.val) = z i then 1 else 0

local instance : DecidableEq (Tape u v K p) := Classical.decEq _

omit [Field F] in
private theorem condition (p q : Prop) [Decidable p] [Decidable q] {d : Decidable (p ∧ q)} (a b : F) :
    @ite F (p ∧ q) d a b = if p then if q then a else b else b := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem sum_tape (x : X → Bool) (A : Pieces S r l v p) (L : PackRows.Layout l u v K)
    (π : PacketPlan (Address v K) a) (z : S.exposed r → Bool)
    (g : (X ⊕ Tape u v K p → Bool) → F)
    (hr : ∀ y, T.read (Sum.elim x y) = y)
    (hp : correctPacket A L π) (he : correctExterior A L z g x) :
    (∑ y, T.test A L π (Sum.elim x y) * g (Sum.elim x y)) = S.eval r z := by
  let e := A.inside L
  have hi : Function.Injective (Links.put e) := by
    intro a b eq
    rw [← Links.read_put e a, eq, Links.read_put]
  symm
  unfold Scheme.eval
  refine Fintype.sum_of_injective (Links.put e) hi _ _ ?_ ?_
  · intro y hy
    have hn : ¬ Links.pad e y := fun h => hy ⟨_, Links.put_read _ h⟩
    simp [test, hr, hn, e]
  · intro y
    have h := Links.padded e y
    have hy := Links.read_put e y
    have hj (i) : Links.put e y (e i) = y i := congrFun hy i
    unfold test
    rw [hr, he _ h]
    simp only [hp _ h, hj, Scheme.Agrees, ← Function.comp_assoc, show A.inside L = e from rfl,
      h, true_and, hy, mul_ite, mul_one, mul_zero]
    exact condition (∀ i : S.exposed r, y i.val = z i) (∀ i j, S.Joins r i j → y i = y j) _ _

theorem evaluator [Fintype X] {w j cap m : ℕ} {U : Set (Table F)}
    (ok : Fits S u v K p a w j cap) (hU : SortTables F w ⊆ U)
    (g : (X ⊕ Tape u v K p → Bool) → F) (hg : WideWeight F cap U g m) :
    ∃ f : (X → Bool) → F, WideWeight F cap U f
        (10000000 * (Fintype.card X + 2 ^ j * (1 + w) + m)) ∧
      ∀ (r : S.format.obj) (d : ℕ) (l : Inventory (2 ^ S.m) (2 ^ S.h) d)
        (A : Pieces S r l v p) (ha : Pieces.Room (l := l) (u := u))
        (L : PackRows.Layout l u v K) (π : PacketPlan (Address v K) a)
        (z : S.exposed r → Bool) (x : X → Bool),
        (∀ y, T.Supplied A ha L π.head (Sum.elim x y)) → (∀ y, T.read (Sum.elim x y) = y) →
        correctPacket A L π → correctExterior A L z g x → f x = S.eval r z := by
  obtain ⟨f, hf, he⟩ := T.service ok
  let Y := Tape u v K p
  let cost := 500000 * (Fintype.card (X ⊕ Y) + 2 ^ j * (1 + w))
  let job (b : Bool) := if b then f else g
  let charge (b : Bool) := if b then cost else m
  have H (b : Bool) : WideWeight F cap U (job b) (charge b) := by
    cases b
    · exact hg
    · intro v i
      obtain ⟨k, hk, h⟩ := hf v i
      exact ⟨k, hk, h.mono le_rfl hU⟩
  have net := wide_sum job (fun _ => id) charge ok.gates H
  have hY : Fintype.card Y ≤ 2 ^ j * w := by
    simp only [Y, Fintype.card_prod, Fintype.card_fin]
    apply Nat.mul_le_mul ok.slots
    have := ok.move
    have := ok.upper
    change 2 * u * bundleSize v p ≤ w
    omega
  refine ⟨fun x => ∑ y : Y → Bool, f (Sum.elim x y) * g (Sum.elim x y), ?_, ?_⟩
  · intro v i
    obtain ⟨k, hk, hn⟩ := net v i
    refine ⟨k, ?_, ?_⟩
    · simp only [Fintype.sum_bool, charge, Bool.false_eq_true, ite_true, ite_false, cost,
        Fintype.card_sum] at hk
      have small : Fintype.card Y ≤ 2 ^ j * (1 + w) := hY.trans (Nat.mul_le_mul_left _ (by omega))
      dsimp only [Y] at small hk; omega
    · simpa [weightedSum, job] using hn
  · intro r d l A ha L π z x hs hr hp hg
    trans ∑ y, T.test A L π (Sum.elim x y) * g (Sum.elim x y)
    · exact Finset.sum_congr rfl (fun y _ => congrArg (· * _) (he _ _ _ _ _ _ _ _ (hs y)))
    · exact T.sum_tape x A L π z g hr hp hg

end Wires
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Computing exterior controls from one host's short labels

Each block lists only channel, stack number and segment. Count distinct
stacks, order them by the fixed stack index, and take prefixes across
blocks. Global exterior names do not enter this computation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
open Packing Finset
open scoped Classical

variable (D : Dimensions) {J : Type} {H k : ℕ}

def listed (l : D.Source) (c : Fin D.d) :=
  univ.filter fun s : Cell D.h => ∃ i t, l i = some (c, s, t)

def countAt (l : D.Source) (c : Fin D.d) := (listed D l c).card * D.b

def prior (l : D.Source) (c : Fin D.d) (s : Cell D.h) :=
  ((listed D l c).filter fun t => Fintype.equivFin (Cell D.h) t < Fintype.equivFin _ s).card

def ordinal (l : Fin k → D.Source) (c : Fin D.d) (t : Fin k) (s : Cell D.h) :=
  PackRows.start (fun x => (listed D (l x) c).card) t + prior D (l t) c s

def occupied (l : Fin k → D.Source) (c : Fin D.d) (r : Fin D.v) (i : Fin D.q) (s : Cell D.h) : Prop :=
  ∃ t, s ∈ listed D (l t) c ∧
    ordinal D l c t s / D.q = r.val ∧ ordinal D l c t s % D.q = i.val

def readAddr (l : Fin k → D.Source) (c : Fin D.d) (r : Fin D.v) (i : Fin D.q) : Option (Cell D.h) :=
  if h : ∃ s, occupied D l c r i s then some h.choose else none

def program (rows : Fin k → D.Source) (channel : Fin D.d) (ord : Fin D.v) : D.ExteriorBits → Bool
  | .inl _ => decide (∃ i s, occupied D rows channel ord i s)
  | .inr (i, j) => encode ((readAddr D rows channel ord i).map D.cellCode) j

variable (loc : J → Cell D.h → Fin H × Fin k) (χ : Fin H → J → Fin D.d)
  (rows : Fin H → Fin k → D.Source)

def Accurate : Prop := ∀ i j c s, s ∈ listed D (rows i j) c ↔ ∃ t, loc t s = (i, j) ∧ χ i t = c

def Separate : Prop :=
  ∀ i j a b, (loc i a).1 = (loc j b).1 → χ (loc i a).1 i = χ (loc j b).1 j → i = j

namespace Accurate
variable {D loc χ rows} (a : Accurate D loc χ rows) (sep : Separate D loc χ)
include a sep

theorem listed_eq (i : J) (s : Cell D.h) (t : Fin k) :
    let v := (loc i s).1
    listed D (rows v t) (χ v i) = univ.filter (fun j => loc i j = (v, t)) := by
  intro v
  ext j
  rw [a, mem_filter_univ]
  refine ⟨?_, fun h => ⟨i, h, rfl⟩⟩
  rintro ⟨l, hl, hc⟩
  have hv : (loc l j).1 = (loc i s).1 := by rw [hl]
  have e := sep l i j s hv (by rwa [hv])
  subst l; exact hl

theorem prior_eq (i : J) (s : Cell D.h) :
    prior D (rows (loc i s).1 (loc i s).2) (χ (loc i s).1 i) s =
      (univ.filter fun t => loc i t = loc i s ∧
        Fintype.equivFin (Cell D.h) t < Fintype.equivFin _ s).card := by
  rw [prior, a.listed_eq sep i s, filter_filter]

variable [Fintype J]

theorem counts_eq (v : Fin H) (t : Fin k) (c : Fin D.d) :
    counts loc χ v t c = (listed D (rows v t) c).card := by
  have hf := lengths_eq loc χ 1 v t c
  simp only [lengths, mul_one] at hf
  rw [hf]
  apply card_bij (fun x _ => x.2)
  · intro x hx
    obtain ⟨hl, hc⟩ := (mem_filter.mp hx).2
    exact (a _ _ _ _).mpr ⟨x.1, hl, by simpa only [hl] using hc⟩
  · intro x hx y hy he
    obtain ⟨hl, hc⟩ := (mem_filter.mp hx).2
    obtain ⟨hl', hc'⟩ := (mem_filter.mp hy).2
    exact Prod.ext (sep _ _ _ _ (congrArg Prod.fst (hl.trans hl'.symm)) (hc.trans hc'.symm)) he
  · intro i hi
    obtain ⟨j, hj, hc⟩ := (a _ _ _ _).mp hi
    exact ⟨(j, i), mem_filter.mpr ⟨mem_univ _, hj, by simpa only [hj] using hc⟩, rfl⟩

theorem countAt (v : Fin H) (t : Fin k) (c : Fin D.d) :
    Exterior.countAt D (rows v t) c = lengths loc χ D.b v t c := by
  rw [lengths, Exterior.countAt, a.counts_eq sep]

theorem point_slot (i : J) (s : Cell D.h) (q : Fin D.b) :
    (point loc χ D.b ((i, s), q)).2.2.2.val =
      prior D (rows (loc i s).1 (loc i s).2) (χ (loc i s).1 i) s * D.b + q.val := by
  rw [Exterior.point_slot, stack_slot loc χ sep, a.prior_eq sep]

theorem rank (i : J) (s : Cell D.h) : PackRows.rank _ (stack loc χ (i, s)) =
    ordinal D (rows (loc i s).1) (χ (loc i s).1 i) (loc i s).2 s := by
  unfold PackRows.rank ordinal
  rw [stack_slot loc χ sep, a.prior_eq sep]
  congr 2
  funext t
  exact a.counts_eq sep _ _ _

end Accurate
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior
end

/-! # Reading the exterior stacks of a registered assignment -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
open Packing Coloring PackRows Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Dimensions} {S : Scheme F} {G : Diagram F x y}
  (t : Assignment D S G) (hw : t.Fits)

theorem accurate {rows : B S.m → B S.h → D.Source} (h : t.Registered hw rows) :
    Exterior.Accurate D t.loc t.lane rows := by
  intro i j c s
  simp only [Exterior.listed, Finset.mem_filter_univ]
  constructor
  · rintro ⟨k, b, hh⟩
    obtain ⟨a, h₁, h₂, _⟩ := (h _ _ _ _ _ _).mp hh
    exact ⟨a, h₁, h₂⟩
  · rintro ⟨a, h₁, h₂⟩
    let b : Fin D.b := ⟨0, D.bpos⟩
    exact ⟨t.coordinate hw (t.endpoint a s b), b, (h _ _ _ _ _ _).mpr ⟨a, h₁, h₂, rfl⟩⟩

def descriptor : Exterior.Descriptor (Stack.Outer x y) (Cell D.h) D.Addr (Fin D.q) D.n :=
  (Exterior.make_descriptor t.loc t.lane t.inject_names D.bpos D.qpos t.cap
    (by simpa using D.cover) D.width _ (t.layout hw)).choose

theorem placement (i : Stack.Outer x y) (s : Cell D.h) (k : Fin D.b) :
    let slot := (t.layout hw).portSlots (t.endpoint i s k)
    slot.1 = ((t.descriptor hw).place (i, s)).1 ∧
      slot.2.val = ((t.descriptor hw).place (i, s)).2.val * D.b + k.val :=
  (Exterior.make_descriptor t.loc t.lane t.inject_names D.bpos D.qpos t.cap
    (by simpa using D.cover) D.width _ (t.layout hw)).choose_spec i s k

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
end

/-! # Correct exterior fields at every occupied port -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
open Packing Coloring PackRows Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Dimensions} {S : Scheme F} {G : Diagram F x y}
  (t : Assignment D S G) (hw : t.Fits)

private theorem portrow_iff {H m d u : ℕ} {l : Inventory H m d} (s : Endpoints l) (r : PortRows l u) :
    portRow l u s = r ↔ s.1 = r.1 ∧ s.2.2.1 = r.2.1 ∧ rank l s / (2 * u) = r.2.2.val := by
  constructor
  · intro h; subst r; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨v, c, k⟩ := r
    rintro ⟨rfl, rfl, he⟩
    exact congrArg (fun z => (⟨s.1, s.2.2.1, z⟩ : PortRows l u)) (Fin.ext he)

/-- Identify a stack at an inside address by its host, channel, and
ordinal in the concatenation of the blocks of that channel. -/
theorem placed_iff (r : PortRows t.inventory D.u) (q : Fin D.q) (i : Stack.Outer x y) (s : Cell D.h) :
    let n := rank _ (Exterior.stack t.loc t.lane (i, s))
    (t.descriptor hw).place (i, s) = ((t.layout hw).portLoc r, q) ↔
      (t.loc i s).1 = r.1 ∧ Fin.natAdd (2 * 2 ^ S.d) (t.lane (t.loc i s).1 i) = r.2.1 ∧
        n / D.q = r.2.2.val ∧ n % D.q = q.val := by
  intro n
  let j : Fin D.b := ⟨0, D.bpos⟩
  have h := t.placement hw i s j
  have eq : rank t.inventory (t.endpoint i s j) = n * D.b := by
    unfold endpoint inventory outerCount
    rw [rank_extendR, Exterior.point_rank]; rfl
  have col : ((t.descriptor hw).place (i, s)).2.val = n % D.q := by
    have hh := h.2
    rw [(t.layout hw).ordinal, eq, ← D.width, Nat.mul_mod_mul_right] at hh
    exact Nat.mul_right_cancel D.bpos hh.symm
  rw [Prod.ext_iff, ← h.1, (t.layout hw).locate, (t.layout hw).portLoc.injective.eq_iff,
    portrow_iff, eq, ← D.width, Nat.mul_div_mul_right _ _ D.bpos]
  simp only [Fin.ext_iff, col, and_assoc]
  rfl

variable {rows : B S.m → B S.h → D.Source} (ok : t.Registered hw rows)
  (r : PortRows t.inventory D.u) (c : Fin D.d) (o : Fin D.v)
  (hc : r.2.1 = Fin.natAdd (2 * 2 ^ S.d) c) (hr : r.2.2.val = o.val)
include ok hc hr

theorem occupied_iff (q : Fin D.q) (s : Cell D.h) :
    Exterior.occupied D (rows r.1) c o q s ↔
      ∃ i, (t.descriptor hw).place (i, s) = ((t.layout hw).portLoc r, q) := by
  have ac := t.accurate hw ok
  constructor
  · rintro ⟨j, hj, h₁, h₂⟩
    obtain ⟨i, hi, he⟩ := (ac _ _ _ _).mp hj
    refine ⟨i, (t.placed_iff hw r q i s).mpr ?_⟩
    simp only [ac.rank t.inject_names, hi, he, hc, hr, h₁, h₂, and_self]
  · rintro ⟨i, h⟩
    obtain ⟨hi, he, h₁, h₂⟩ := (t.placed_iff hw r q i s).mp h
    rw [hc, Fin.natAdd_inj, hi] at he
    rw [ac.rank t.inject_names, hi, he] at h₁ h₂
    exact ⟨(t.loc i s).2, (ac _ _ _ _).mpr ⟨i, Prod.ext hi rfl, he⟩, h₁.trans hr, h₂⟩

theorem program_active :
    Exterior.program D (rows r.1) c o (.inl ()) = ((t.descriptor hw).owner ((t.layout hw).portLoc r)).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [Exterior.program, decide_eq_true_eq, Option.isSome_iff_exists]
  constructor
  · rintro ⟨q, s, h⟩
    obtain ⟨i, hi⟩ := (t.occupied_iff hw ok r c o hc hr q s).mp h
    exact ⟨i, ((t.descriptor hw).addr_eq _ _ _ _).mpr hi |>.1⟩
  · rintro ⟨i, hi⟩
    obtain ⟨s, hs⟩ := ((t.descriptor hw).owner_eq _ _).mp hi
    exact ⟨_, s, (t.occupied_iff hw ok r c o hc hr _ s).mpr ⟨i, Prod.ext hs rfl⟩⟩

theorem program_addr (q : Fin D.q) {i : Stack.Outer x y}
    (hi : (t.descriptor hw).owner ((t.layout hw).portLoc r) = some i) :
    (fun j => Exterior.program D (rows r.1) c o (.inr (q, j))) =
      Exterior.encode (((t.descriptor hw).addr ((t.layout hw).portLoc r) q).map D.cellCode) := by
  have eq s : Exterior.occupied D (rows r.1) c o q s ↔
      (t.descriptor hw).addr ((t.layout hw).portLoc r) q = some s := by
    rw [t.occupied_iff hw ok r c o hc hr]
    simp only [← (t.descriptor hw).addr_eq, hi, Option.some.injEq, exists_eq_left']
  have he : Exterior.readAddr D (rows r.1) c o q =
      (t.descriptor hw).addr ((t.layout hw).portLoc r) q := by
    unfold Exterior.readAddr
    split
    · rename_i h
      exact ((eq _).mp h.choose_spec).symm
    · rename_i h
      cases hx : (t.descriptor hw).addr _ q with
      | none => rfl
      | some s => exact (h ⟨s, (eq s).mpr hx⟩).elim
  simp only [Exterior.program, he]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
end

/-!
# Fixed taps for the two terminal checks

A complete row groups stacks for the exterior test. The same offsets
are read as finest bundles for the table and internal-wire tests.
No payload bits are identified when forming the arrays.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Coloring PackRows Classical

variable {F X : Type} {x y : Wire} {S : Scheme F} {D : Dimensions}

abbrev Dimensions.Tape (D : Dimensions) := PackRows.Tape D.u D.v D.K D.p

def Dimensions.userBit (D : Dimensions) (S : Scheme F) (i : D.Addr) (k : D.ExteriorBits) :
    D.Decisions S := .inl (i.1, .inr (i.2, .inr (.inr (.inr k))))

def Dimensions.offset (D : Dimensions) (j : Fin D.q) (p : D.StackBits) : Body D.u D.v D.p :=
  ((finProdFinEquiv (j, p.1)).cast D.width, finProdFinEquiv.symm p.2)

structure Screen (D : Dimensions) (S : Scheme F) (x y : Wire) (X : Type) where
  source : D.Originals x y → X
  tape : D.Decisions S → X
  names : Stack.Outer x y ↪ (D.Names → Bool)

namespace Screen
variable (Q : Screen D S x y X)

def int : Wires S D.u D.v D.K D.p D.a (X ⊕ D.Tape) where
  control i k := .inl (.inl (Q.tape (.inl (i, .inl k))))
  format i k := .inl (.inl (Q.tape (.inl (i.1, .inr (i.2, .inl k)))))
  head i k := .inl (.inl (Q.tape (.inr (i, .inl k))))
  body i := .inl (.inr i)

def ext : Exterior.Input (X ⊕ D.Tape) D.Addr (Stack.Outer x y) (Packing.Cell D.h)
    (Fin D.q) D.Names (Fin D.h) D.StackBits where
  names := Q.names
  keys := D.cellCode
  header i
    | none => .inl (.inl (Q.tape (D.userBit S i (.inl ()))))
    | some k => .inl (.inl (Q.tape (.inr (i, .inr k))))
  body i
    | (j, .inl k) => .inl (.inl (Q.tape (D.userBit S i (.inr (j, k)))))
    | (j, .inr p) => .inl (.inr (i, D.offset j p))
  source i s k := .inl (Q.source ((i, s), k))

variable [Field F] {G : Diagram F x y} (t : Assignment D S G) (hw : t.Fits)

def Flags (hn : 2 * S.m + D.r ≤ D.a) (z : X → Bool) : Prop :=
  let L := t.layout hw
  let c := z ∘ Q.tape
  (∀ i b, c (.inl (i, .inl b)) = L.moves i b) ∧
  (∀ i b, c (.inl (i.1, .inr (i.2, .inl b))) = L.format (t.index hw) (labels S t.rows) i b) ∧
  (∀ i b, c (.inr (i, .inl b)) =
    bits (word (D.a + 2)) (t.inner.header L hw.position (Channels.code hn) i) b) ∧
  (∀ i, Exterior.flag (c (D.userBit S i (.inl ()))) (fun b => c (.inr (i, .inr b))) =
    ((t.descriptor hw).owner i).map Q.names) ∧
  ∀ i j, (t.descriptor hw).owner i = some j → ∀ k,
    Exterior.decode (fun b => c (D.userBit S i (.inr (k, b)))) =
      ((t.descriptor hw).addr i k).map D.cellCode

def supplied (z : X → Bool) (i : S.exposed t.rows) : Bool :=
  let a := (Exterior.ports t.post).symm i
  z (Q.source (a.1.1, a.1.2, a.2))

theorem supplied_at (z : X → Bool) (i : Stack.Outer x y) (s : Packing.Cell D.h)
    (j : Fin D.b) (k : Fin D.z) :
    Q.supplied t z (Exterior.ports t.post (((i, s), j), k)) = z (Q.source ((i, s), j, k)) := by
  simp [supplied]

theorem inside_at (i : Stack.Outer x y) (s : Packing.Cell D.h) (j : Fin D.b) (k : Fin D.z) :
    t.pieces.inside (t.layout hw) (Exterior.ports t.post (((i, s), j), k)).val =
      (((t.descriptor hw).place (i, s)).1, D.offset ((t.descriptor hw).place (i, s)).2 (j, k)) := by
  unfold Pieces.inside
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, t.end_bit]
  obtain ⟨ha, hb⟩ := t.placement hw i s j
  refine Prod.ext ha (Prod.ext (Fin.ext ?_) rfl)
  change _ = j.val + D.b * ((t.descriptor hw).place (i, s)).2.val
  exact hb.trans (by ring)

theorem correct_ext (z : X → Bool) (v : D.Tape → Bool) :
    Q.ext.Supplied (Sum.elim z v) (t.descriptor hw).owner (t.descriptor hw).addr ↔
      ∀ i, v (t.pieces.inside (t.layout hw) i.val) = Q.supplied t z i := by
  rw [Exterior.Descriptor.supplied]
  constructor
  · intro h i
    obtain ⟨⟨⟨⟨j, s⟩, u⟩, k⟩, rfl⟩ := (Exterior.ports t.post).surjective i
    rw [inside_at, Q.supplied_at]
    exact h j s (u, k)
  · rintro h j s ⟨u, k⟩
    specialize h (Exterior.ports t.post (((j, s), u), k))
    rw [inside_at, Q.supplied_at] at h
    exact h

end Screen
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Capacity bounds for checking the exterior and interior arrays -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
open PackRows

variable {F : Type} (D : Dimensions) (S : Assembly.Scheme F)

/-- A stack has one activity bit, its address and its payload. -/
abbrev recordWidth := D.h + 1 + D.b * D.z

structure FitsScreen (x y : Wire) (w j cap : ℕ) : Prop where
  core : Wires.Fits S D.u D.v D.K D.p D.a w j cap
  code : 2 * S.m + D.r ≤ D.a
  wide : w ≤ D.e + D.q * D.recordWidth + 2
  narrow : D.e + D.q * D.recordWidth + 2 ≤ 4 * w
  small : 2 * (D.q * D.recordWidth + 1) < j
  slots : D.K * (2 * D.v) + (wd x + wd y) * D.n ≤ 2 ^ j
  arity : 2 * 2 ^ (D.h + 2) * (D.recordWidth + 1) ≤ min cap (min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)))

variable {D S} {x y : Wire} {w j cap : ℕ}

theorem FitsScreen.tape (f : D.FitsScreen S x y w j cap) :
    Fintype.card D.Tape ≤ 2 ^ j * w := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  apply Nat.mul_le_mul f.core.slots
  change 2 * D.u * D.z ≤ w
  have hm := f.core.move
  have := f.core.upper
  change (4 * D.v * D.u) ^ 2 + 2 * (2 * D.u * D.z) < j at hm
  omega

theorem FitsScreen.supply (f : D.FitsScreen S x y w j cap) :
    (wd x + wd y) * 2 ^ (D.h + 2) * (D.h + D.b * D.z + 3) ≤ 6 * 2 ^ j * w := by
  have h := f.small
  have := f.core.upper
  have hw : D.q * D.recordWidth ≤ w := by omega
  have hr : D.h + D.b * D.z + 3 ≤ 3 * D.recordWidth := by unfold recordWidth; omega
  have hs : (wd x + wd y) * D.n ≤ 2 ^ j := (Nat.le_add_left ..).trans f.slots
  calc
    _ ≤ (wd x + wd y) * 2 ^ (D.h + 2) * (3 * D.recordWidth) := Nat.mul_le_mul_left _ hr
    _ = 6 * ((wd x + wd y) * D.n) * (D.q * D.recordWidth) := by
      rw [show 2 ^ (D.h + 2) = 2 * (D.n * D.q) by rw [D.cover, pow_add]; ring]
      ring
    _ ≤ 6 * 2 ^ j * w := Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) hw

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
end

/-!
# A single terminal evaluator for all supported layouts

The same weighted network receives original data and all row decisions.
Its scalar value is the ordered-span contraction named by the decisions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Screen
open Assembly PackRows Transcript Classical

variable {F X : Type} [Field F] {x y : Wire} {S : Scheme F} {D : Dimensions}
    (Q : Screen D S x y X) {w j cap : ℕ}

private theorem valid {G : Diagram F x y} (t : Assignment D S G) (hw : t.Fits)
    (hn : 2 * S.m + D.r ≤ D.a) (x : X → Bool) (hx : Q.Flags t hw hn x) (y : D.Tape → Bool) :
    Q.ext.Valid D.n (Sum.elim x y) (t.descriptor hw).owner (t.descriptor hw).addr :=
  (t.descriptor hw).valid _ _ hx.2.2.2.1 hx.2.2.2.2

variable [Fintype X]

private theorem exterior (h : D.FitsScreen S x y w j cap) :
    ∃ g : (X ⊕ D.Tape → Bool) → F,
      WideWeight F cap (Allowed F w) g (10000000 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (G : Diagram F x y) (t : Assignment D S G) (hw : t.Fits) b,
        Q.Flags t hw h.code b →
        Wires.correctExterior t.pieces (t.layout hw) (Q.supplied t b) g b := by
  have hc : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ cap := by
    apply le_trans _ h.core.large
    have := h.core.upper
    gcongr; omega
  have hcard : Fintype.card (Exterior.Body (Fin D.q) (Fin D.h) D.StackBits) = D.q * D.recordWidth := by
    simp [Dimensions.recordWidth]
  have hsrc : Fintype.card (Stack.Outer x y) = wd x + wd y := by simp
  have room : Fintype.card (Packing.Cell D.h) + D.n * Fintype.card (Fin D.q) ≤ 2 ^ (D.h + 2) := by
    rw [Packing.card_cell, Fintype.card_fin, D.cover, pow_add]
    omega
  obtain ⟨g, hg, he⟩ := Q.ext.supply (F := F) h.core.gates h.core.lower h.core.upper hc
    (by rw [hcard, Fintype.card_fin]; exact h.wide)
    (by rw [hcard, Fintype.card_fin]; exact h.narrow)
    (by rw [hcard]; exact h.small)
    (by rw [hsrc, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; exact h.slots) room
    (by
      simp only [Fintype.card_fin, Fintype.card_prod]
      have hr := h.arity
      rw [show D.recordWidth + 1 = D.h + D.b * D.z + 2 by unfold Dimensions.recordWidth; omega] at hr
      exact hr)
  refine ⟨g, ?_, fun G t hw b hb y _ => ?_⟩
  · intro a i
    obtain ⟨v, hv, hnet⟩ := hg a i
    refine ⟨v, ?_, hnet⟩
    rw [hsrc, Fintype.card_sum, Fintype.card_fin,
      show Fintype.card D.StackBits = D.b * D.z by simp] at hv
    have ht := h.tape
    have hS := h.supply
    rw [mul_assoc 6] at hS
    have := Nat.mul_le_mul_left (2 ^ j) (Nat.le_add_left w 1)
    omega
  · rw [he _ _ _ (Q.valid t hw h.code b hb y), Q.correct_ext]
    split <;> rfl

theorem run (h : D.FitsScreen S x y w j cap) :
    ∃ g : (X → Bool) → F, WideWeight F cap (Allowed F w) g
        (10 ^ 15 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (G : Diagram F x y) (t : Assignment D S G) (hw : t.Fits) b,
        Q.Flags t hw h.code b → g b = S.eval t.rows (Q.supplied t b) := by
  obtain ⟨f, hf, ef⟩ := Q.exterior h
  obtain ⟨g, hg, eg⟩ := Q.int.evaluator h.core sort_allowed f hf
  refine ⟨g, ?_, fun G t hw b hb => ?_⟩
  · intro a i
    obtain ⟨v, hv, hnet⟩ := hg a i
    exact ⟨v, by omega, hnet⟩
  · obtain ⟨π, hπ, hlinks⟩ := t.post.core_plan D.zpos (t.strips.uniform D.zpos) t.external
      t.ext_location (t.layout hw) hw.position (Channels.code h.code)
    apply eg _ _ _ t.pieces hw.room (t.layout hw) π (Q.supplied t b) b _
      (fun _ => rfl) hlinks (ef _ _ _ _ hb)
    intro y
    rw [hπ]
    exact ⟨fun i => funext (hb.1 i), fun i => funext (hb.2.1 i),
      fun i => funext fun k => (hb.2.2.1 i k).symm⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Screen
end
