import OAI.ThreeFlat.Diagonal.CanonicalFixing
import OAI.ThreeFlat.BitNetwork

namespace OAI
/-! # Address translation for the approximating block

Every input bit of a collapse trace comes from the shared advice, a public
constant, one of four tick fields, or one of the two catalyst indices.
The same translation is used for physical bit values and for wire addresses.
-/

namespace ThreeFlat.Diagonal

inductive ApproximatePort (I : Type*) (d n a : ℕ) where
  | publicBit (i : Fin d)
  | literal (b : Bool)
  | leftChunk (tick : Fin (n+1)) (bit : Fin a)
  | rightChunk (tick : Fin (n+1)) (bit : Fin a)
  | leftAux (tick : Fin (n+1)) (bit : Fin a)
  | rightAux (tick : Fin (n+1)) (bit : Fin a)
  | leftCatalyst (i : I) (bit : Fin a)
  | rightCatalyst (i : I) (bit : Fin a)

namespace ApproximatePort

variable {I F α β : Type*} {d n a q : ℕ}
abbrev BitState (I α : Type*) (a : ℕ) := MachineState I (Fin a → α) (Fin a → α)

/-- Read from a complete fixing and the two inactive halves. -/
def read (D : Fin d → Bool) (f : BlockFixing (n+1) (Fin a → Bool) (Fin a → Bool))
    (l r : I → Fin a → Bool) : ApproximatePort I d n a → Bool
  | .publicBit j => D j
  | .literal b => b
  | .leftChunk j k => f.1 j k
  | .rightChunk j k => f.2.1 j k
  | .leftAux j k => Fin.cons (α := fun _ => Fin a → Bool) f.2.2.1 (Fin.init f.2.2.2) j k
  | .rightAux j k => f.2.2.2 j k
  | .leftCatalyst j k => l j k
  | .rightCatalyst j k => r j k

/-- The public lengths and indices determine each source address; there is
one intermediate auxiliary word per interior tick boundary. -/
def route (D : Fin d → α) (lit : Bool → α) (atSlot : Fin (n+1) → I) (active : Bool)
    (x y : BitState I α a) (mid : Fin n → Fin a → α) : ApproximatePort I d n a → α
  | .publicBit j => D j
  | .literal b => lit b
  | .leftChunk j k => x.1 active (atSlot j) k
  | .rightChunk j k => y.1 active (atSlot j) k
  | .leftAux j k => Fin.cons (α := fun _ => Fin a → α) x.2 mid j k
  | .rightAux j k => Fin.snoc (α := fun _ => Fin a → α) mid y.2 j k
  | .leftCatalyst j k => x.1 (!active) j k
  | .rightCatalyst j k => y.1 (!active) j k

def mapState (g : α → β) (x : BitState I α a) : BitState I β a :=
  (fun h i j => g (x.1 h i j), fun j => g (x.2 j))

theorem route_map (g : α → β) (D : Fin d → α) (lit : Bool → α)
    (atSlot : Fin (n+1) → I) (active : Bool) (x y : BitState I α a) (mid : Fin n → Fin a → α)
    (s : ApproximatePort I d n a) :
    g (route D lit atSlot active x y mid s) =
      route (g ∘ D) (g ∘ lit) atSlot active (mapState g x) (mapState g y)
        (fun i j => g (mid i j)) s := by
  cases s with
  | publicBit _ | literal _ | leftChunk _ _ | rightChunk _ _ | leftCatalyst _ _ | rightCatalyst _ _ => rfl
  | leftAux i j => cases i using Fin.cases <;> simp [route, mapState]
  | rightAux i j => cases i using Fin.lastCases <;> simp [route, mapState]

theorem read_canonical (D : Fin d → Bool) (atSlot : Fin (n+1) → I) (active : Bool)
    (x y : BitState I Bool a) (mid : Fin n → Fin a → Bool) (s : ApproximatePort I d n a) :
    read D (canonicalFixing atSlot active x y mid) (x.1 (!active)) (y.1 (!active)) s =
      route D id atSlot active x y mid s := by
  cases s <;> simp [read, canonicalFixing, route, Function.comp_def]

/-- Read the catalyst as computed by a physical collapse trace. -/
def catalyst [CommSemiring F] (N : BitNetwork F q) (select : Fin q → ApproximatePort I d n a)
    (D : Fin d → Bool) (f : BlockFixing (n+1) (Fin a → Bool) (Fin a → Bool)) :
    Matrix (I → Fin a → Bool) (I → Fin a → Bool) F :=
  fun l r => N.eval (read D f l r ∘ select)

theorem fixing_sum [Field F] [Fintype I] [DecidableEq I] (N : BitNetwork F q)
    (select : Fin q → ApproximatePort I d n a) (D : Fin d → Bool)
    (atSlot : Fin (n+1) → I) (active : Bool) (x y : BitState I Bool a) :
    (∑ f, physicalFixing atSlot active f (catalyst N select D f)) x y =
      if ∀ i ∉ Finset.univ.image atSlot, x.1 active i = y.1 active i then
        ∑ mid : Fin n → Fin a → Bool,
          N.eval (route D id atSlot active x y mid ∘ select)
      else 0 := by
  rw [approximate_fixings_entry]
  simp only [catalyst, Function.comp_def, read_canonical]

end ApproximatePort
end ThreeFlat.Diagonal

end OAI
