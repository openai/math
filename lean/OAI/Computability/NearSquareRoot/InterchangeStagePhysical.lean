import OAI.Computability.NearSquareRoot.InterchangeStageFamily
import OAI.Computability.NearSquareRoot.InterchangeStagePrepare

/-!
# The rectangle address layout on the entire tape

Original label addresses use the early reserve and the selected main pair. An
endpoint prepares its reserve once before the batch of queries. The rectangle
address uses a common basis for all its endpoints. The two diagram identities
hold on the entire physical address, including occupied spare coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.RectangleAtlas

open InterchangeStageLift IntegerMultiplication.Port StageLedger

variable {L B : Type} {r : B → Rectangle L} {a m : ℕ}

/-- View one catalog incidence as an oriented rectangle endpoint. -/
def point {s : Bool} (u : Endpoint r s) : RectanglePoint (r u.2) :=
  ⟨(s,u.1),u.2.property⟩

noncomputable def labelPerm (A : RectangleAtlas r a) (s : Bool) (j : Fin m) (v : L) :
    Equiv.Perm (Duplex (Fin (a+m+a)) ℚ) :=
  perm (querySlots a j) (A.label s v).toEquiv

/-- The original reserve basis change and the occupied reserve exchanges do
not depend on the query. -/
noncomputable def preparePerm (A : RectangleAtlas r a) (m : ℕ) {s : Bool}
    (u : Endpoint r s) : Equiv.Perm (Duplex (Fin (a+m+a)) ℚ) :=
  (perm (earlySlots a m) (reserveMap (A.size _) (A.prepare _ (point u))).toEquiv).trans
    (reserveShift (A.size u.2))

noncomputable def localPerm (A : RectangleAtlas r a) {s : Bool} (j : Fin m)
    (u : Endpoint r s) : Equiv.Perm (Duplex (Fin (a+m+a)) ℚ) :=
  perm (rectSlots (A.size _) j)
    (endpointAddress (A.early _ (point u)) (A.late _ (point u))).toEquiv

noncomputable def commonPerm (A : RectangleAtlas r a) (j : Fin m) (t : B) :
    Equiv.Perm (Duplex (Fin (a+m+a)) ℚ) :=
  (perm (rectSlots (A.size t) j) ((A.common t).trans (shuffleLinear ℚ ℚ (A.size t))).toEquiv).trans
    (reserveShift (A.size t))

theorem physical_triangle (A : RectangleAtlas r a) {s : Bool} (j : Fin m)
    (u : Endpoint r s) :
    (A.preparePerm m u).trans ((A.localPerm j u).trans (A.commonPerm j u.2)) = A.labelPerm s j u.1 := by
  apply Equiv.ext
  exact lift_prepared_diagram (A.size u.2) j (A.prepare _ (point u)) _ (A.common _) _
    (A.triangle _ (point u))

/-- Rectangle diagrams satisfying the routed stage semantics at every physical
address and every query in a group of `m`. -/
noncomputable def physicalLayout (A : RectangleAtlas r a) (m : ℕ) :
    StageRoute.Layout r (Fin m) (Duplex (Fin (a+m+a)) ℚ) where
  S := A.labelPerm false
  T := A.labelPerm true
  C := A.commonPerm
  prepareSrc := A.preparePerm m
  prepareDst := A.preparePerm m
  localSrc := A.localPerm
  localDst := A.localPerm
  source_triangle := A.physical_triangle
  target_triangle := A.physical_triangle

/-- The original source and target for a label differ by the selected physical
pivot. Every other main pair and every reserve field retain their values. -/
theorem physical_diagonal (A : RectangleAtlas r a) (j : Fin m) (v : L) :
    ((A.physicalLayout m).S j v).trans ((A.physicalLayout m).T j v).symm =
      perm (querySlots a j) (querySwap a ℚ) := by
  change (perm _ _).trans (perm _ _).symm = _
  rw [perm_symm,perm_trans]
  congr 1
  apply Equiv.ext
  intro x
  exact A.diagonal v x

end Interchange.RectangleAtlas

end NearSquareRoot
end Computability
end OAI
