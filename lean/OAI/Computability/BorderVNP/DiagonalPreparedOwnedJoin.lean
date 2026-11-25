import OAI.Computability.BorderVNP.DiagonalExteriorPrefixBanks
import OAI.Computability.BorderVNP.DiagonalNativeJoinedRows
import OAI.Computability.BorderVNP.DiagonalPositiveOwnedReports

/-! # The actual shared dispatch on a decoded pre-call prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PreparedOwned

open TeamContraction TeamContraction.ProcessorSlots CellDispatch CellMacro.Generator BorderVNP.Cube
open scoped Classical

variable {R n w axes b h K s : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X Raw Hist Claim : Type} {Route : Hist → Type}
    {Report : (i : Raw) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (prep : JointBeforeCells S ≃ PreparedFields Raw Hist Claim Route Report)
    (cells : Hist → ℕ) (owner : (q : Hist) → Route q → Fin (cells q) → Fin (R+1))
    (base : PreparedFields Raw Hist Claim Route Report → Fin (R+1) → ℕ)
    (table : ∀ (f : PreparedFields Raw Hist Claim Route Report) u,
      let z := prep.symm f
      OwnerTable (S z.1 u).pub ((S z.1 u).postMemory (z.2 u)) ⟨u.val,base f u,cells f.2.1⟩
        (PositiveTeam.ownerWord (owner f.2.1 f.2.2.1)))

local notation "Fields" => PreparedFields Raw Hist Claim Route Report

/-- The dispatch indexed by its actual public prefix. Its row order and
private call memory are obtained from the teams' true returns. -/
abbrev At (z : JointBeforeCells S) :=
  JoinedCells (fun u => (S z.1 u).pub) (fun u => (S z.1 u).postMemory) (fun u => (S z.1 u).generated) z.2

/-- The same dispatch, first built on the real native prefix recovered by
the inverse decoder. Its cells and owners already have their bounds and
identities from the decoded public history and route. -/
noncomputable def observed (f : Fields) : At S (prep.symm f) :=
  PositiveTeam.joinOwnedRows (S (prep.symm f).1) (prep.symm f).2 (owner f.2.1 f.2.2.1) (base f) (table f)

/-- Join an arbitrary returning exterior and complete preparation tuple
before extending it with any private bank. The attained history supplies
the number of cells, and the route supplies the owner column. -/
noncomputable def join (x : X) (p : (u : Fin (R+1)) → (S x u).Prefix) : At S ⟨x,p⟩ :=
  (Equiv.piCongrLeft' (At S) prep).symm (observed S prep cells owner base table) ⟨x,p⟩

/-- Restoring any full set of prepared fields gives the very dispatch
originally built on that state's physical owner table. -/
theorem join_symm (f : Fields) :
    join S prep cells owner base table (prep.symm f).1 (prep.symm f).2 = observed S prep cells owner base table f :=
  congrFun ((Equiv.piCongrLeft' (At S) prep).apply_symm_apply (observed S prep cells owner base table)) f

local notation3 (prettyPrint := false) "restored(" f ")" =>
  join S prep cells owner base table (prep.symm f).1 (prep.symm f).2

/-- Restore the global ordinal of a cell on this particular decoded history. -/
noncomputable def cellIndex (f : Fields) : Fin (cells f.2.1) ≃ (restored(f)).Cell :=
  Equiv.cast (congrArg JoinedCells.Cell (join_symm S prep cells owner base table f)).symm

/-- Both the route owner and its true native generated cell are in the
original ordinal of this history. Different prefixes may have different
cell counts, owners and private wire widths. -/
theorem cellIndex_read (f : Fields) (c : Fin (cells f.2.1)) :
    let z := prep.symm f
    let j := cellIndex S prep cells owner base table f c
    let u := owner f.2.1 f.2.2.1 c
    (restored(f)).owner j = u ∧ (restored(f)).cells j = ((S z.1 u).generated (z.2 u)).cell c.val := by
  let keep (A B : At S (prep.symm f)) (eqn : A=B) (v : B.Cell) :
      let j := Equiv.cast (congrArg JoinedCells.Cell eqn).symm v
      A.owner j=B.owner v ∧ A.cells j=B.cells v := by
    subst B
    exact ⟨rfl,rfl⟩
  exact keep _ _ (join_symm S prep cells owner base table f) c

variable (size : ∀ q, Fin (cells q) → ℕ)
    (width : ∀ (f : PreparedFields Raw Hist Claim Route Report) (c : Fin (cells f.2.1)), let z := prep.symm f
      let u := owner f.2.1 f.2.2.1 c
      (((S z.1 u).generated (z.2 u)).cell c.val).privateWires=size f.2.1 c)

/-- The bank of the real dispatched owner vectors, at the independent private
size of each cell of the public history. The prefix has already been joined
when the later private bits are chosen. -/
noncomputable def bank (f : Fields) : (restored(f)).Private ≃ ((c : Fin (cells f.2.1)) → Fin (size f.2.1 c) → Bool) :=
  let eqn := join_symm S prep cells owner base table f
  (Equiv.cast (congrArg JoinedCells.Private eqn)).trans
    ((observed S prep cells owner base table f).bankEquiv (Equiv.refl _) (size f.2.1) (width f))

private theorem castPrivate_read {z : JointBeforeCells S} {A B : At S z}
    (same : A=B) (p : B.Private) (c : B.Cell) :
    List.ofFn (((Equiv.cast (congrArg JoinedCells.Private same)).symm p)
      (Equiv.cast (congrArg JoinedCells.Cell same).symm c)) = List.ofFn (p c) := by
  subst B
  rfl

/-- The inverse bank map places every digit of its source cell verbatim in
the actual private-call vector at the restored cell ordinal. -/
theorem bank_symm_bits (f : Fields) (raw : (c : Fin (cells f.2.1)) → Fin (size f.2.1 c) → Bool) (c : Fin (cells f.2.1)) :
    List.ofFn ((bank S prep cells owner base table size width f).symm raw
      (cellIndex S prep cells owner base table f c)) = List.ofFn (raw c) := by
  let J := observed S prep cells owner base table f
  let e := J.bankEquiv (Equiv.refl _) (size f.2.1) (width f)
  refine (castPrivate_read S (join_symm S prep cells owner base table f) (e.symm raw) c).trans ?_
  have digits : e.symm raw c = raw c ∘ Fin.cast (width f c) := by
    funext j
    have seen := J.bankEquiv_read (Equiv.refl _) (size f.2.1) (width f) (e.symm raw) c j
    change e (e.symm raw) c (Fin.cast (width f c) j)=e.symm raw c j at seen
    exact seen.symm.trans (congrFun (congrFun (e.apply_symm_apply raw) c) _)
  rw [digits]
  have ofCast {m n : ℕ} (h : m=n) (v : Fin n → Bool) : List.ofFn (v ∘ Fin.cast h)=List.ofFn v := by
    subst n
    rfl
  exact ofCast (width f c) (raw c)

/-- The signed product of the private checks is the product over the
decoded history's actual dispatch. This holds on every proposed bank,
even when a check rejects it. -/
theorem bank_symm_weight (f : Fields) (raw : (c : Fin (cells f.2.1)) → Fin (size f.2.1 c) → Bool) :
    let J := observed S prep cells owner base table f
    (restored(f)).privateWeight ((bank S prep cells owner base table size width f).symm raw) =
      J.privateWeight ((J.bankEquiv (Equiv.refl _) (size f.2.1) (width f)).symm raw) := by
  let keep (A B : At S (prep.symm f)) (eqn : A=B) (v : B.Private) :
      A.privateWeight ((Equiv.cast (congrArg JoinedCells.Private eqn)).symm v) = B.privateWeight v := by
    subst B
    rfl
  exact keep _ _ (join_symm S prep cells owner base table f) _

open DiagonalTallyCellReports

/-- Any actual comparison of the received owner reports on the source-indexed
dispatch supplies the report image on the unmodified native pre-call prefix.
Its private vector is the inverse image of the very same bank. -/
noncomputable def reportImage (f : Fields) (raw : (c : Fin (cells f.2.1)) → Fin (size f.2.1 c) → Bool)
    {layout : Fin (R+1) → ReportLayout} (ss : ∀ u, List (AssignedCell (layout u)))
    (rr : ∀ u, ReportAssignments ((ss u).map AssignedCell.report)) :
    let J := observed S prep cells owner base table f
    J.ReportImage ((J.bankEquiv (Equiv.refl _) (size f.2.1) (width f)).symm raw) ss rr →
    (restored(f)).ReportImage ((bank S prep cells owner base table size width f).symm raw) ss rr := by
  intro J image
  let keep (A B : At S (prep.symm f)) (eqn : A=B) (v : B.Private) (view : B.ReportImage v ss rr) :
      A.ReportImage ((Equiv.cast (congrArg JoinedCells.Private eqn)).symm v) ss rr := by
    subst B
    exact view
  exact keep _ J (join_symm S prep cells owner base table f) _ image

end RoutingISA.Evaluator.PreparedOwned

end BorderVNP
end Computability
end OAI
