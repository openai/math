import OAI.Hierarchy.DescentBoundedBitHistory

namespace OAI
/-! # Whole payload operands of an ordinary retained local history -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Finset
open scoped BigOperators Classical
noncomputable section

variable {A H B Tag S F : Type} {w : A→ℕ} {v : B→ℕ} {p : ℕ}

/-- The physical address names one complete aligned payload. -/
structure BlockRef (p : ℕ) (w : A→ℕ) where
  port : A
  block : ℕ
  fits : (block+1)*p ≤ w port

def BlockRef.atBit (b : BlockRef p w) (d : Fin p) : BitRef w :=
  ⟨b.port,b.block*p+d.val,(Nat.add_lt_add_left d.isLt _).trans_le (by simpa [Nat.succ_mul] using b.fits)⟩

/-- Changing only the physical name preserves the ordinal within the word. -/
def BlockRef.rename (f : A→B) (same : ∀a,w a=v (f a)) (b : BlockRef p w) : BlockRef p v :=
  ⟨f b.port,b.block,(same b.port) ▸ b.fits⟩

structure BlockMap (p : ℕ) (w : A→ℕ) (v : B→ℕ) (route : BitRef w→BitRef v) where
  map : BlockRef p w→BlockRef p v
  read : ∀b d,(map b).atBit d=route (b.atBit d)

/-- Read a logical operand lane from its residual offset and stride. Each table entry is
one entire physically addressed block. -/
structure Slice (p : ℕ) (α : Type) where
  start : ℕ
  stride : ℕ
  count : ℕ
  residue : start<p
  bound : count≤stride+1
  fits : ∀ d : Fin p,(start+stride*d.val)/p<count
  get : Fin count→α

def Slice.index {α : Type} (s : Slice p α) (d : Fin p) : Fin s.count :=
  ⟨(s.start+s.stride*d.val)/p,s.fits d⟩

def Slice.offset {α : Type} (s : Slice p α) (d : Fin p) : Fin p :=
  ⟨(s.start+s.stride*d.val)%p,Nat.mod_lt _ (Nat.zero_lt_of_lt d.isLt)⟩

def Slice.map {α β : Type} (s : Slice p α) (f : α→β) : Slice p β := {s with get := f ∘ s.get}

def Slice.whole {α : Type} (hp : 0<p) (x : α) : Slice p α where
  start := 0
  stride := 1
  count := 1
  residue := hp
  bound := by decide
  fits d := by simp [Nat.div_eq_of_lt d.isLt]
  get _ := x

def decode {hw : H→ℕ} (s : Slice p (BlockRef p w⊕BlockRef p hw)) (d : Fin p) : BitRef w⊕BitRef hw :=
  (s.get (s.index d)).map (fun b=>b.atBit (s.offset d)) (fun b=>b.atBit (s.offset d))

@[simp] theorem decode_whole {hw : H→ℕ} (hp : 0<p) (a : BlockRef p w⊕BlockRef p hw) (d : Fin p) :
    decode (Slice.whole hp a) d=a.map (fun b=>b.atBit d) (fun b=>b.atBit d) := by
  have off : (Slice.whole hp a).offset d=d := Fin.ext (by simp [Slice.offset,Slice.whole,Nat.mod_eq_of_lt d.isLt])
  change a.map (fun b=>b.atBit ((Slice.whole hp a).offset d)) (fun b=>b.atBit ((Slice.whole hp a).offset d))=_
  rw [off]

/-- Every argument of the existing scalar table is read using a number of descriptors
proportional to its length measured in whole payloads. Hidden words use the same units. -/
structure Shape (p : ℕ) (r : BitRecipe Tag A w) where
  hiddenMultiple : ∀x,p∣r.hiddenWidth x
  groups : (u : r.Node)→Fin (r.arity u)→ℕ
  size_eq : ∀u j,r.size u j=groups u j*p
  chunk : (u : r.Node)→(j : Fin (r.arity u))→Fin (groups u j)→Slice p (BlockRef p w⊕BlockRef p r.hiddenWidth)
  read : ∀u j (g : Fin (groups u j)) (d : Fin p), decode (chunk u j g) d=
    r.arg u j (Fin.cast (size_eq u j).symm (finProdFinEquiv (g,d)))

variable {r : BitRecipe Tag A w}

/-- A permutation, split or relabeling of whole physical words changes neither the
number of operands nor any stride or control count. -/
def Shape.reroute (s : Shape p r) {route : BitRef w→BitRef v} (f : BlockMap p w v route) :
    Shape p (r.reroute route) where
  hiddenMultiple := s.hiddenMultiple
  groups := s.groups
  size_eq := s.size_eq
  chunk u j g := (s.chunk u j g).map (Sum.map f.map id)
  read u j g d := by
    change decode ((s.chunk u j g).map (Sum.map f.map id)) d =
      (r.arg u j (Fin.cast (s.size_eq u j).symm (finProdFinEquiv (g,d)))).map route id
    refine Eq.trans ?_ (congrArg (Sum.map route id) (s.read u j g d))
    let lane := s.chunk u j g
    let off := lane.offset d
    change (((lane.get (lane.index d)).map f.map id).map (fun b=>b.atBit off) (fun b=>b.atBit off))=
      (((lane.get (lane.index d)).map (fun b=>b.atBit off) (fun b=>b.atBit off)).map route id)
    cases lane.get (lane.index d) with
    | inl b => exact congrArg Sum.inl (f.read b off)
    | inr b => rfl

def Shape.retag (s : Shape p r) (f : Tag→S) : Shape p (r.retag f) where
  hiddenMultiple := s.hiddenMultiple
  groups := s.groups
  size_eq := s.size_eq
  chunk := s.chunk
  read := s.read

/-- The address headers, including the residual offset, stride and number of physical words per ordered group. -/
def Shape.headers (s : Shape p r) : ℕ := ∑u,∑j,∑g,((s.chunk u j g).count+3)

theorem Shape.headers_bound (s : Shape p r) (R : ℕ) (stride : ∀u j g,(s.chunk u j g).stride≤R) :
    s.headers*p ≤ (R+4)*(∑u,r.nodeBits u) := by
  unfold Shape.headers BitRecipe.nodeBits
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro j _
  rw [s.size_eq]
  calc
    _ ≤ ∑_g : Fin (s.groups u j),(R+4)*p := sum_le_sum fun g _ =>
      Nat.mul_le_mul_right _ (by have := (s.chunk u j g).bound;have := stride u j g;omega)
    _ = _ := by simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

/-- Address rows alone count repeated reads of physical words, without charging
any scalar descriptor control entries. -/
theorem Shape.addresses_bound (s : Shape p r) (R : ℕ) (stride : ∀u j g,(s.chunk u j g).stride≤R) :
    (∑u,∑j,∑g,(s.chunk u j g).count)*p ≤ (R+1)*(∑u,r.nodeBits u) := by
  unfold BitRecipe.nodeBits
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro j _
  rw [s.size_eq]
  calc
    _ ≤ ∑_g : Fin (s.groups u j),(R+1)*p := sum_le_sum fun g _ =>
      Nat.mul_le_mul_right _ ((s.chunk u j g).bound.trans (Nat.add_le_add_right (stride u j g) 1))
    _ = _ := by simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

/-- One local summation label represents a complete hidden payload, including labels
whose values never reach an external port. -/
def privateGrains (p : ℕ) (r : BitRecipe Tag A w) : ℕ := ∑h,r.hiddenWidth h/p

theorem Shape.privateGrains_mul (s : Shape p r) : privateGrains p r*p=∑h,r.hiddenWidth h := by
  unfold privateGrains
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun h _=>Nat.div_mul_cancel (s.hiddenMultiple h)

/-- Count node and argument delimiters, the offset/stride/count and true operand addresses,
and the private summation labels of the contracted scalar table. -/
def Shape.entries (s : Shape p r) := (∑u,(r.arity u+1))+s.headers+privateGrains p r

theorem Shape.entries_mul_le (s : Shape p r) (R : ℕ) (bound : ∀u j g,(s.chunk u j g).stride≤R) :
    s.entries*p ≤ (∑u,(r.arity u+1))*p+(R+4)*(∑u,r.nodeBits u)+(∑h,r.hiddenWidth h) := by
  unfold Shape.entries
  rw [Nat.add_mul,Nat.add_mul,s.privateGrains_mul]
  exact Nat.add_le_add_right (Nat.add_le_add_left (s.headers_bound R bound) _) _

end
end Hierarchy.DescentBundleHistory

end OAI
