import OAI.Hierarchy.DescentFallbackOperandBranch
import OAI.Hierarchy.DescentResetContactShapePayload

namespace OAI
/-! # The receiver's installed palette tag determines the fallback operand and contact side -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentSIMDLookup DescentTreePrefixIntervals DescentDenseHostOrder DescentHostDirectory DescentResetLocalRoster
open scoped Classical
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : DescentFallbackOperandBranch.Config)

theorem mixed_fallback (node arg : ℕ) (x : C.Data n) (s : Bool)
    (root : code C.residual×Option (Fin (2^n))) (ds : List Bool) (shape : ↥(roster board C.residual C.maxDepth))
    (active : (C.header x 0).val≠0)
    (located : (C.header x 2).val=(localRank board C.residual C.maxDepth shape).val)
    (tag : shape.val=.fall s ((),(root.1.val,root.2)) ds)
    (room : DescentFallbackPeriod.rootCell C.residual n root<DescentFallbackShapeTable.rows C.residual (2^n)) :
    let id:= (⟨_,room⟩ : Fin (DescentFallbackShapeTable.rows C.residual (2^n)))
    let amount:=DescentFallbackPeriod.score (C.packet x) (id,0,id)
    C.mixed board node arg x=C.make s (C.header x 1).val (min C.maxDepth (Nat.clog 2 amount)) ds root (C.rowsAt x s root id amount) node arg := by
  have bound:=(localRank board C.residual C.maxDepth shape).isLt
  have fit : (C.header x 2).val<(roster board C.residual C.maxDepth).card :=located ▸ bound
  have cast : (⟨_,fit⟩ : Fin (roster board C.residual C.maxDepth).card)=
      DescentResetTrunkPalette.order board C.residual C.maxDepth shape:=Fin.ext located
  simp only [mixed,ite_eq_right active,dite_eq_left fit,cast,Equiv.symm_apply_apply,tag,dite_eq_left root.1.property]
  simp only [dite_eq_left room]

end
end Hierarchy.DescentFallbackOperandBranch.Config
namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentCommonHost DescentDenseHostOrder
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)


theorem installed_tree_shape (s : Bool) (t : Z.Fallback)
    (v : (DescentCommonPalette.tree (Z.placement.fallbackBook s t).height).Site) :
    (Z.localShape T (Z.placed T (Z.privateSiteAt T s (.inr t) v))).val =
      .fall s ((),((Z.fallLabel T t).val,(T.code t).2.2)) (List.ofFn v.2) := by
  change shape Z.graph (commonName Z T (privateSiteAt Z T s (.inr t) v))=_
  have siteName : Z.commonName T (Z.privateSiteAt T s (.inr t) v) =
      bankNode Z.placement Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d ⟨(s,.inr t),v⟩ :=
    congrArg (rawName Z.placement Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d)
      ((Z.resetNames T).apply_symm_apply (.inr ⟨(s,.inr t),v⟩))
  rw [siteName]
  rfl
end
end Hierarchy.DescentSixParty.ResetInput
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetPublicParentWord DescentDenseHostOrder DescentCommonHost
open DescentChosenRouter DescentRelativeContacts
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

theorem actual_contact_side (u : Host) (s : Bool) (c : (R).Contact)
    (atFace : (if s then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c))=u)
    (inc : DescentResetLocalRoster.active (blocks B) u (contactParent B c)) :
    contactSide B ⟨c,inc.2⟩=s := by
  have distinct := contact_no_loop B c
  change decide ((blocks B).src (contactParent B c) ≠ u) = s
  cases s
  · change (blocks B).src (contactParent B c) = u at atFace
    simp [atFace]
  · change (blocks B).dst (contactParent B c) = u at atFace
    exact decide_eq_true (fun eqn => distinct (eqn.trans atFace.symm))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
