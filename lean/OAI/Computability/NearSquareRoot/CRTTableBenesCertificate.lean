import OAI.Computability.NearSquareRoot.CRTTableBenesQuery
import OAI.Computability.NearSquareRoot.CRTTableWordPorts
import OAI.Computability.NearSquareRoot.CRTTableWordEquiv

/-! # Correctness of CRT word tables supplied to the Beneš compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

variable {d : ℕ} (a w : Fin d → ℕ) {E : Fin d → Type}
  (pad : ∀ g, E g → Fin (2^w g - a g)) [∀ j, NeZero (a j)]

/-- The encoded program queried at a fixed external setting supplies the
complete duplicate-free graph of this controlled binary port permutation.
This is the table invariant used by the verified Beneš switch compiler. -/
theorem targetWordRows_represents (hwidth : ∀ j, a j ≤ 2^w j)
    (hdense : ∀ j, 2^w j ≤ 2*a j) (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (j : Fin (CRTTree.level n (List.finRange d)).length)
    (y : CRT.Address a E) (inv : Bool) :
    let s := Stage.atLevel d n hn j
    ∀ i : Fin (CRTTree.right s.node).length,
      let g := (CRTTree.right s.node)[i.val]
      let δ := CRT.mergeOffset (s.left a E) y g
      let π := portPerm (hwidth g) (bif inv then -δ else δ)
      let e := wordEquiv (w g)
      let bits := packedControl n (List.finRange d) (addressField a w pad y)
      Benes.RawRepresents (e.symm.trans (π.trans e))
        (targetWordRows (tagAt a w n j.val i.val inv,bits)) := by
  intro s i
  dsimp only
  rw [targetWordRows_at a w pad n hn.le j i y inv]
  obtain ⟨hlen,entries⟩ := levelTables_portPerm a w pad hwidth hdense hcop n hn j y inv i
  apply wordRows_represents _ _ _ hlen
  intro u
  simpa only [List.getElem?_eq_getElem (by rw [hlen]; exact u.isLt), Option.getD_some] using entries u

end CRTTable

end NearSquareRoot
end Computability
end OAI
