import OAI.LinearAlgebra.MatrixExponent.ListBounds

/-!
# Trivalent bit networks

A bundle is a binary tree of bit positions. Rewiring only permutes the
positions (with changes of parenthesization). Networks are built by
juxtaposing vertex tables and joining wires, summing over their shared
values. Trace allows internal cycles. Size counts vertices and exterior bits.
-/

namespace OAI.LinearAlgebra.MatrixExponent

inductive Wire
  | bit
  | unit
  | pair (a b : Wire)

abbrev Val : Wire → Type
  | .bit => Bool
  | .unit => Unit
  | .pair a b => Val a × Val b

instance valFintype : (a : Wire) → Fintype (Val a)
  | .bit => inferInstanceAs (Fintype Bool)
  | .unit => inferInstanceAs (Fintype Unit)
  | .pair a b =>
    letI := valFintype a
    letI := valFintype b
    inferInstanceAs (Fintype (Val a × Val b))

instance valDecidableEq : (a : Wire) → DecidableEq (Val a)
  | .bit => inferInstanceAs (DecidableEq Bool)
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .pair a b =>
    letI := valDecidableEq a
    letI := valDecidableEq b
    inferInstanceAs (DecidableEq (Val a × Val b))

def wd : Wire → ℕ
  | .bit => 1
  | .unit => 0
  | .pair a b => wd a + wd b

inductive Rewire : (a b : Wire) → (Val a → Val b) → Prop
  | id (a) : Rewire a a (fun x => x)
  | swap (a b) : Rewire (.pair a b) (.pair b a) (fun x => (x.2, x.1))
  | assoc (a b c) : Rewire (.pair (.pair a b) c) (.pair a (.pair b c))
      (fun x => (x.1.1, x.1.2, x.2))
  | assoc' (a b c) : Rewire (.pair a (.pair b c)) (.pair (.pair a b) c)
      (fun x => ((x.1, x.2.1), x.2.2))
  | unit (a) : Rewire (.pair a .unit) a (fun x => x.1)
  | unit' (a) : Rewire a (.pair a .unit) (fun x => (x, ()))
  | comp {a b c f g} : Rewire a b f → Rewire b c g → Rewire a c (fun x => g (f x))
  | par {a b c d f g} : Rewire a b f → Rewire c d g →
      Rewire (.pair a c) (.pair b d) (fun x => (f x.1, g x.2))

/-- The last index counts vertices, excluding exterior wires. -/
inductive Net (F : Type) [Field F] : (a b : Wire) → (Val a → Val b → F) → ℕ → Prop
  | empty : Net F .unit .unit (fun _ _ => 1) 0
  | table (a b) (k : Val a → Val b → F) (h : wd a + wd b ≤ 3) : Net F a b k 1
  | par {a b c d k l m n} : Net F a b k m → Net F c d l n →
      Net F (.pair a c) (.pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) (m + n)
  | comp {a b c k l m n} : Net F a b k m → Net F b c l n →
      Net F a c (fun x z => ∑ y : Val b, k x y * l y z) (m + n)
  | trace {a b c k m} : Net F (.pair a c) (.pair b c) k m →
      Net F a b (fun x y => ∑ z : Val c, k (x, z) (y, z)) m
  | pre {a b c f k m} : Net F b c k m → Rewire a b f →
      Net F a c (fun x y => k (f x) y) m
  | post {a b c f k m} : Net F a b k m → Rewire c b f →
      Net F a c (fun x y => k x (f y)) m

abbrev word : ℕ → Wire
  | 0 => .unit
  | n + 1 => .pair .bit (word n)

abbrev tree : ℕ → Wire → Wire
  | 0, a => a
  | w + 1, a => .pair (tree w a) (tree w a)

def flatten {a : Wire} : (w : ℕ) → Val (tree w a) → List (Val a)
  | 0, x => [x]
  | w + 1, x => flatten w x.1 ++ flatten w x.2

abbrev lists (w : ℕ) : ℕ → Wire
  | 0 => .unit
  | t + 1 => .pair (tree w (word (2 * w))) (lists w t)

def distinctPower (F : Type) [Field F] (w : ℕ) : (t : ℕ) → Val (lists w t) → F
  | 0, _ => 1
  | t + 1, x => (if (flatten w x.1).Nodup then 1 else 0) * distinctPower F w t x.2

def Realizes (F : Type) [Field F] (w t m : ℕ) : Prop :=
  ∃ v, Net F (lists w t) .unit (fun x _ => distinctPower F w t x) v ∧ m = v + t * listBits w

end OAI.LinearAlgebra.MatrixExponent
