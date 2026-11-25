import OAI.Computability.NearSquareRoot.InterchangeStagePhysical
import OAI.Computability.NearSquareRoot.InterchangeStageLocalWord
import OAI.Computability.NearSquareRoot.InterchangeStageReserveWord
import OAI.Computability.NearSquareRoot.InterchangeStageScriptCost

/-!
# Supported matrix instructions of the shared interchange stage

Every paid conversion touches at most the two reserves and a single main
pair. The endpoint preparations occur once per incidence. The triangular
conversions for individual queries have zero recursive price.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.RectangleAtlas

open InterchangeStageLift IntegerMultiplication.Port StageLedger StageRoute

variable {L B H : Type} {r : B → Rectangle L} {a m : ℕ}

/-- Convert an original label's selected pair to its common address order. -/
noncomputable def labelWord (A : RectangleAtlas r a) (s : Bool) (j : Fin m) (v : L) :
    Support.Word (Fin (a+m+a)) Fin.val :=
  .atom (.dense (querySlots a j) (A.label s v))

/-- Place the endpoint reserve for the entire batch of main queries. -/
noncomputable def prepareWord (A : RectangleAtlas r a) (m : ℕ) {s : Bool} (u : Endpoint r s) :
    Support.Word (Fin (a+m+a)) Fin.val :=
  .seq (.atom (.dense (earlySlots a m) (reserveMap (A.size _) (A.prepare _ (point u)))))
    (reserveWord Fin.val (A.size u.2))

noncomputable def localWord (A : RectangleAtlas r a) {s : Bool} (j : Fin m) (u : Endpoint r s) :
    Support.Word (Fin (a+m+a)) Fin.val :=
  endpointWord (A.size _) j (A.early _ (point u)) (A.late _ (point u))

/-- Apply the common frame, then return its occupied coordinates to the
original order used by every label. -/
noncomputable def commonWord (A : RectangleAtlas r a) (j : Fin m) (t : B) :
    Support.Word (Fin (a+m+a)) Fin.val :=
  .seq (.atom (.dense (rectSlots (A.size t) j) ((A.common t).trans (shuffleLinear ℚ ℚ (A.size t)))))
    (reserveWord Fin.val (A.size t))

@[simp] theorem labelWord_address (A : RectangleAtlas r a) (s : Bool) (j : Fin m) (v : L) :
    (A.labelWord s j v).address.toEquiv = A.labelPerm s j v := rfl

@[simp] theorem prepareWord_address (A : RectangleAtlas r a) (m : ℕ) {s : Bool} (u : Endpoint r s) :
    (A.prepareWord m u).address.toEquiv = A.preparePerm m u := by
  change Equiv.trans _ (reserveWord Fin.val _).address.toEquiv = Equiv.trans _ _
  rw [reserveWord_address]
  rfl

@[simp] theorem localWord_address (A : RectangleAtlas r a) {s : Bool} (j : Fin m) (u : Endpoint r s) :
    (A.localWord j u).address.toEquiv = A.localPerm j u := rfl

@[simp] theorem commonWord_address (A : RectangleAtlas r a) (j : Fin m) (t : B) :
    (A.commonWord j t).address.toEquiv = A.commonPerm j t := by
  change Equiv.trans _ (reserveWord Fin.val _).address.toEquiv = Equiv.trans _ _
  rw [reserveWord_address]
  rfl

@[simp] theorem labelWord_price (A : RectangleAtlas r a) (s : Bool) (j : Fin m) (v : L) :
    (A.labelWord s j v).price = 18 * (a+2) := rfl

@[simp] theorem prepareWord_price (A : RectangleAtlas r a) (m : ℕ) {s : Bool} (u : Endpoint r s) :
    (A.prepareWord m u).price = 18*a + 36*A.e u.2 := by
  change 18*a + (reserveWord (m:=m) Fin.val _).price = _
  rw [reserveWord_price]

@[simp] theorem localWord_price (A : RectangleAtlas r a) {s : Bool} (j : Fin m) (u : Endpoint r s) :
    (A.localWord j u).price = 0 := rfl

@[simp] theorem commonWord_price (A : RectangleAtlas r a) (j : Fin m) (t : B) :
    (A.commonWord j t).price = 18*(a+2) + 36*A.e t := by
  change 18*(A.c t + (2+A.e t)) + (reserveWord (m:=m) Fin.val _).price = _
  rw [reserveWord_price]
  have := A.size t
  omega

/-- The script uses each address word in its forward or inverse direction. -/
noncomputable def routeWord (A : RectangleAtlas r a) {I J : H → L} :
    Move r (Fin m) I J → Support.Word (Fin (a+m+a)) Fin.val
  | .idle => .idle
  | .prepare u => A.prepareWord m u
  | .restore u => .symm (A.prepareWord m u)
  | .align j u => A.localWord j u
  | .unalign j u => .symm (A.localWord j u)
  | .gather j ⟨i,none⟩ => A.labelWord false j (I i)
  | .gather j ⟨_,some t⟩ => A.commonWord j t
  | .distribute j ⟨i,none⟩ => .symm (A.labelWord true j (J i))
  | .distribute j ⟨_,some t⟩ => .symm (A.commonWord j t)

@[simp] theorem routeWord_address (A : RectangleAtlas r a) {I J : H → L}
    (u : Move r (Fin m) I J) :
    (A.routeWord u).address.toEquiv = (A.physicalLayout m).perm u := by
  cases u with
  | idle => rfl
  | prepare u => exact A.prepareWord_address m u
  | restore u => exact congrArg Equiv.symm (A.prepareWord_address m u)
  | align j u => rfl
  | unalign j u => rfl
  | gather j t => rcases t with ⟨i,_ | b⟩ <;> first | rfl | exact A.commonWord_address j b
  | distribute j t => rcases t with ⟨i,_ | b⟩ <;> first | rfl | exact congrArg Equiv.symm (A.commonWord_address j b)

/-- Only the four conversion families counted by the ledger have positive
price. The bound is uniform in the number of main queries. -/
theorem routeWord_price_le (A : RectangleAtlas r a) {I J : H → L}
    (u : Move r (Fin m) I J) : (A.routeWord u).price ≤ 54*(a+2) := by
  have prep {s : Bool} (x : Endpoint r s) : (A.prepareWord m x).price ≤ 54*(a+2) := by
    rw [prepareWord_price]
    have := A.size x.2
    omega
  have comm (j : Fin m) (t : B) : (A.commonWord j t).price ≤ 54*(a+2) := by
    rw [commonWord_price]
    have := A.size t
    omega
  cases u with
  | idle => exact Nat.zero_le _
  | prepare x => exact prep x
  | restore x => exact prep x
  | align j x => exact Nat.zero_le _
  | unalign j x => exact Nat.zero_le _
  | gather j t =>
    rcases t with ⟨i,_ | b⟩
    · change 18*(a+2) ≤ 54*(a+2)
      omega
    · exact comm j b
  | distribute j t =>
    rcases t with ⟨i,_ | b⟩
    · change 18*(a+2) ≤ 54*(a+2)
      omega
    · exact comm j b

@[simp] theorem routeWord_price_idle (A : RectangleAtlas r a) (I J : H → L) :
    (A.routeWord (.idle (Q:=Fin m) (I:=I) (J:=J))).price = 0 := rfl

@[simp] theorem routeWord_price_align (A : RectangleAtlas r a) (I J : H → L) (j : Fin m)
    (u : Endpoint r false) : (A.routeWord (.align (I:=I) (J:=J) j u)).price = 0 := rfl

@[simp] theorem routeWord_price_unalign (A : RectangleAtlas r a) (I J : H → L) (j : Fin m)
    (u : Endpoint r true) : (A.routeWord (.unalign (I:=I) (J:=J) j u)).price = 0 := rfl

end Interchange.RectangleAtlas

end NearSquareRoot
end Computability
end OAI
