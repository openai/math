import OAI.Hierarchy.DescentScalarBookReshape

namespace OAI
/-! The public RAM register transposition preserves the selected integer. -/
namespace Hierarchy.DescentScalarBookReshape
open DescentSIMDLookup DescentPackedZip
noncomputable section

/-- A change of coordinate types in a public layout preserves the integer of the
single original host, low slot and group that feeds this physical output. -/
theorem book_val_cast {Q Q' H J J' r r' a a' : ℕ}
    (pitch : Q=Q') (groups : J=J') (radix : r=r')
    (left : Fin Q→Fin H→Fin (J*r)→Cell a) (right : Fin Q'→Fin H→Fin (J'*r')→Cell a')
    (read : ∀l h g,(left l h g).val=(right (l.cast pitch) h (g.cast (congrArg₂ (·*·) groups radix))).val)
    (b : Fin r) (h : Fin (H*Q')) (g : Fin J') :
    (book left b (h.cast (congrArg (H*·) pitch.symm)) (g.cast groups.symm)).val=
      (book right (b.cast radix) h g).val :=by
  cases pitch
  cases groups
  cases radix
  exact read _ _ _

end
end Hierarchy.DescentScalarBookReshape

end OAI
