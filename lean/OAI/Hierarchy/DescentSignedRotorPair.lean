import OAI.Hierarchy.DescentPackedReservationColumn
import OAI.Hierarchy.DescentResetSignedStencilRun
import OAI.Hierarchy.DescentInstalledFallbackHeader

namespace OAI
/-! # Reading source and destination packet digits from the real old signed stencil -/
namespace Hierarchy.DescentPackedRotorMatrix
open DescentSIMDLookup DescentChosenRouter DescentResetTrunks DescentRelativeContacts
open DescentSixParty DescentRouterSlots DescentColonies DescentResetAttachments
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput W price ε h C Ht) (T : ResetInput.Terminals Z)
local notation "R" => Z.placement
local notation "rangeDepth" => (Z.k-T.commonDepth)

theorem root_location (s : Bool) (g : (R).Good) (e : Cells R s g) :
    (shortName T.commonDepth (T.code (T.home (ends W.graph s e.val)))).2=
      ((Z.goodLabel T g).val,some (source R s g e)) := by
  let p : {i // useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old i}:=⟨e.val,paid R s g e⟩
  have same : (R).ends s ((R).ticket p).1=g:=by
    simpa [Placement.owner,owner,Placement.contact,contact,p,paid R s g e] using e.property
  have head : base (R).b (R).depth (R).L (R).keys (R).hub (R).old p s=g:=((R).owned p s).symm.trans same
  rw [T.attach,T.source s e.val p.property,root_row]
  change (((R).b (base (R).b (R).depth (R).L (R).keys (R).hub (R).old p s).val.1-T.commonDepth,
    (base (R).b (R).depth (R).L (R).keys (R).hub (R).old p s).val.2.val%2^((R).b (base (R).b (R).depth (R).L (R).keys (R).hub (R).old p s).val.1-T.commonDepth)),_)=_
  rw [head];rfl

/-- The target ticket and sign are separate current columns. Two parity tests consume both actual
signed endpoints, while the relative root code selects this base within the coarse group. -/
def signedPair (r n : ℕ) (root : ℕ×ℕ) (own peer column : ℕ) : Cell (DescentPackedRotorMatrix.bits n) :=
  let shape:=own/2
  let z:=shape%(2^n+1)
  if own%2=0 ∧ peer%2=0 ∧ 0<z ∧ shape/(2^n+1)=root.1*2^r+root.2 then
    pair (⟨(z-1)%2^n,Nat.mod_lt _ (Nat.two_pow_pos _)⟩:Fin (2^n))
      (⟨column%2^n,Nat.mod_lt _ (Nat.two_pow_pos _)⟩:Fin (2^n))
  else 0

theorem extract {n : ℕ} (r : ℕ) (root : ℕ×ℕ) (i j : Fin (2^n)) (peer : ℕ) :
    signedPair r n root (2*DescentFallbackShapeTable.cell r (root,some i)) (2*peer) j.val=pair i j := by
  have digit : i.val+1<2^n+1:=Nat.succ_lt_succ i.isLt
  let value := DescentFallbackShapeTable.cell r (root,some i)
  have lo : value%(2^n+1)=i.val+1 := by
    change ((root.1*2^r+root.2)*(2^n+1)+(i.val+1))%(2^n+1)=_
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt digit]
  have hi : value/(2^n+1)=root.1*2^r+root.2 := by
    change ((root.1*2^r+root.2)*(2^n+1)+(i.val+1))/(2^n+1)=_
    rw [Nat.mul_comm (root.1*2^r+root.2),Nat.mul_add_div (Nat.zero_lt_succ _),Nat.div_eq_of_lt digit,Nat.add_zero]
  change signedPair r n root (2*value) (2*peer) j.val=_
  simp [signedPair,lo,hi,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt]

theorem extract_peer_bad (r n : ℕ) (root : ℕ×ℕ) (own peer target : ℕ) :
    signedPair r n root own (2*peer+1) target=0 := by simp [signedPair,Nat.add_mod]

theorem extract_own_bad (r n : ℕ) (root : ℕ×ℕ) (own peer target : ℕ) :
    signedPair r n root (2*own+1) peer target=0 := by simp [signedPair,Nat.add_mod]

theorem signed_paid (s : Bool) (g : (R).Good) (e : Cells R s g) (peer : ℕ) (col : ℕ)
    (measured : col=(R).reservedColumn T.commonDepth T.columns.host T.columns.near T.columns.size s
      ((R).ticket ⟨e.val,paid R s g e⟩)) :
    signedPair rangeDepth Z.n (Z.goodLabel T g).val
      (2*DescentFallbackShapeTable.cell rangeDepth (shortName T.commonDepth (T.code (T.home (ends W.graph s e.val)))).2)
      (2*peer) col=pair (source R s g e) (target R s g e) := by
  rw [root_location,measured,←link_column R s g T.columns e]
  exact extract ..

end
end Hierarchy.DescentPackedRotorMatrix

end OAI
