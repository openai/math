import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork

/-!
# Sorting dictionary and query records

A dictionary row has its marker set and carries a count as payload. A query
row has zero padding. At a given key, all its queries precede the unique
dictionary row. The sorting hypothesis below concerns only inputs of this
form and requires the complete ordered output.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

abbrev count (a : Wire) := word (wd a + 1)
abbrev row (a : Wire) := Wire.pair a (.pair .bit (count a))
abbrev state (a : Wire) := Wire.pair .bit (count a)

def zero : (n : ℕ) → Val (word n)
  | 0 => ()
  | n + 1 => (false, zero n)

def inc : (n : ℕ) → Val (word n) → Val (word n)
  | 0, _ => ()
  | n + 1, x => (!x.1, if x.1 then inc n x.2 else x.2)

def value : (n : ℕ) → Val (word n) → ℕ
  | 0, _ => 0
  | n + 1, x => x.1.toNat + 2 * value n x.2

def bits (n k : ℕ) : Val (word n) := (inc n)^[k] (zero n)

def step (a : Wire) (s : Val (state a)) (r : Val (row a)) : Val (state a) :=
  if r.2.1 then (s.1 && decide (s.2 = r.2.2), zero _) else (s.1, inc _ s.2)

def scan (a : Wire) (l : ℕ) (x : Val (tree l (row a))) : Bool :=
  ((flatten l x).foldl (step a) (true, zero _)).1

def query (a : Wire) (x : Val a) : Val (row a) := (x, false, zero _)

def queries (a : Wire) : (l : ℕ) → Val (tree l a) → Val (tree l (row a))
  | 0, x => query a x
  | l + 1, x => (queries a l x.1, queries a l x.2)

def dict (a : Wire) :
    (l : ℕ) → Val (tree l a) → Val (tree l (count a)) → Val (tree l (row a))
  | 0, z, c => (z, true, c)
  | l + 1, z, c => (dict a l z.1 c.1, dict a l z.2 c.2)

def group (a : Wire) (xs : List (Val a)) (r : Val (row a)) : List (Val (row a)) :=
  List.replicate (xs.count r.1) (query a r.1) ++ [r]

/-- The ordinary-width sorting bound restricted to dictionary and query rows.
The keys enumerate all addresses once in key order. The second sort key is
the dictionary marker. Identical query rows require no tie breaking. -/
def Sorting (F : Type) [Field F] (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ a : Wire, let t := wd a
    ∃ (keys : Val (tree t a))
      (sort : Val (tree (t + 1) (row a)) → Val (tree (t + 1) (row a))) (m : ℕ),
      (flatten t keys).Nodup ∧ (∀ z : Val a, z ∈ flatten t keys) ∧
      DNet F (tree (t + 1) (row a)) (tree (t + 1) (row a)) sort m ∧
      (m : ℝ) ≤ C * (2 : ℝ) ^ t * (1 + (t : ℝ)) ^ p ∧
      ∀ (x : Val (tree t a)) (c : Val (tree t (count a))),
        flatten (t + 1) (sort (queries a t x, dict a t keys c)) =
          (flatten t (dict a t keys c)).flatMap (group a (flatten t x))

end OAI.LinearAlgebra.MatrixExponent.Lookup
