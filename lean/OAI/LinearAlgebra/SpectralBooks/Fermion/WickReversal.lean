import OAI.LinearAlgebra.SpectralBooks.Fermion.WickOrder

/-! # Interchanging the two blocks of a Wick matching -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

variable {α : Type*}

/-- Keep a new first field of the right block unpaired. -/
def skipCol (x : α) : {l r : List α} → Matching l r → Matching l (x :: r)
  | [], _, _ => ()
  | _ :: _, _, .inl p => .inl (skipCol x p)
  | _ :: _, _, .inr ⟨j, p⟩ => .inr ⟨j.succ, skipCol x p⟩

/-- Insert a pair joining the row at position `j` to a new right-hand field `x`. -/
def pairAt (x : α) : {l r : List α} → (j : Fin l.length) →
    Matching (l.eraseIdx j.val) r → Matching l (x :: r)
  | [], _, j, _ => Fin.elim0 j
  | _ :: _, _, ⟨0, _⟩, p => .inr ⟨0, p⟩
  | _ :: l, r, ⟨j+1, h⟩, p =>
    match (p : Matching (_ :: l.eraseIdx j) r) with
    | .inl q => .inl (pairAt x ⟨j, Nat.lt_of_succ_lt_succ h⟩ q)
    | .inr ⟨k,q⟩ => .inr ⟨k.succ, pairAt x ⟨j, Nat.lt_of_succ_lt_succ h⟩ q⟩

/-- The empty matching against a block of length zero. -/
def noCols : (l : List α) → Matching l []
  | [] => ()
  | _ :: l => .inl (noCols l)

/-- The same edges, with the left and right blocks exchanged. -/
def reverse : {l r : List α} → Matching l r → Matching r l
  | [], r, _ => noCols r
  | x :: _, _, .inl p => skipCol x (reverse p)
  | x :: _, _, .inr ⟨j,p⟩ => pairAt x j (reverse p)


end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
