import OAI.Hierarchy.DescentSortedRosterPadding
import OAI.Hierarchy.DescentPaddedRasterValue
import OAI.Hierarchy.DescentScalarBookColumns

namespace OAI
/-! Preservation of every gathered range word under the actual prefix embedding of host names. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentHaloWalkRAM DescentScalarBookReshape DescentOrdinaryRasterReturn
noncomputable section

structure Values.Prefix {D k K cap H H' G a nb mb : ℕ} (wide : H ≤ H')
    (v : Values D k K cap H G a nb mb) (v' : Values D k K cap H' G a nb mb) : Prop where
  walks : ∀ h j, v'.walks (h.castLE wide) j = (v.walks h j).map (Fin.castLEEmb wide)
  old : ∀ b h g, v'.old b (h.castLE wide) g = v.old b h g
  born : ∀ b s j h g, v'.born b s j (h.castLE wide) g = v.born b s j h g
  wanted : ∀ h g, v'.wanted (h.castLE wide) g = v.wanted h g
  venues : ∀ h g, v'.venues (h.castLE wide) g = v.venues h g
  counts : ∀ h g, v'.counts (h.castLE wide) g = v.counts h g

variable {D k K cap H H' G a nb mb Q r : ℕ} {wide : H ≤ H'}

theorem Values.Prefix.book {v : Values D k K cap H G a nb mb} {v' : Values D k K cap H' G a nb mb}
    (p : Values.Prefix wide v v') (K' : ℕ) (h : Fin H) (g : Fin G) :
    v'.book K' (h.castLE wide) g = v.book K' h g := by
  unfold Values.book
  simp only [p.wanted,p.venues,p.counts]
  congr 1
  apply congrArg (encode _ _)
  funext j
  have preserved := DescentSortedRoster.indexed_pad wide v.walks v'.walks h (p.walks h)
    (bookRoot D k K cap j)
  simp only [Fin.coe_castLEEmb] at preserved
  rw [preserved]
  cases loc : DescentSortedRoster.indexed v.walks h (bookRoot D k K cap j) with
  | none => rfl
  | some x =>
    simp only [Option.map_some,Option.elim_some]
    unfold item
    cases pick : finSumFinEquiv.symm (bookItem D k K cap j) with
    | inl prior => simp [p.old]
    | inr fresh => simp [p.born]

theorem Values.Prefix.returned {v : Fin Q→Values D k K cap H (G*r) a nb mb}
    {v' : Fin Q→Values D k K cap H' (G*r) a nb mb} (p : ∀ q, Values.Prefix wide (v q) (v' q))
    (K' : ℕ) (x : Fin r) (h : Fin (H*Q)) (g : Fin G) :
    DescentScalarBookReshape.book (fun q h g => (v' q).book K' h g) x (widen wide h) g =
      DescentScalarBookReshape.book (fun q h g => (v q).book K' h g) x h g := by
  unfold DescentScalarBookReshape.book
  rw [endpoints wide h]
  exact (p _).book K' _ _

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
