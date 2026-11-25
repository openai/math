import OAI.ThreeFlat.Diagonal.TraceCursorState
import OAI.ThreeFlat.Diagonal.LaneBucketAddresses
import OAI.ThreeFlat.Diagonal.LaneCursorPorts

namespace OAI
/-! # The physical compression boundary is the original cursor field array -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage.Block

open Computability.VPVNP.Compression CompressorPacking LaneCursor LaneCursor.RowLayout HistoryContraction LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
variable {F : Type} [Field F] (B : Block F) {q : ℕ} (hk : 2 ≤ q+1) (low offsets slots : ℕ)

set_option quotPrecheck false
local notation "A" => B.cursorState hk low offsets slots
local notation "D" => PayloadAddress low slots
local notation "O" => Fin offsets
local notation "W" => 2^low*(offsets*slots*3)

/-- The word bits are numbered in the same offset/low/slot/leg order as the native ROM. -/
def cursorWord : Fin (2^W) ≃ (O × D → Bool) :=
  (MotifBinaryPacking.word W).symm.trans (((finCongr (by ac_rfl :
    W=offsets*(2^low*(slots*3)))).trans (tagOrder offsets low slots)).arrowCongr (Equiv.refl Bool))

theorem cursorWord_apply (label : Fin (2^W)) (tag : O×D) :
    cursorWord low offsets slots label tag =
      (MotifBinaryPacking.word W).symm label (((tagOrder offsets low slots).symm tag).cast (by ac_rfl)) := rfl

private def arcCast {V L : Type} {m n : ℕ} (h : m=n) :
    (V×Fin m)×L ≃ (V×Fin n)×L :=
  ((Equiv.refl V).prodCongr (finCongr h)).prodCongr (Equiv.refl L)

private theorem targetCast {V L : Type} [AddCommGroup L] {m n : ℕ} (e : m=n) (G : LiftedSlots V m L)
    (j : (V×Fin m)×L) :
    (e ▸ G : LiftedSlots V n L).actualTarget.symm (arcCast e j) = arcCast e (G.actualTarget.symm j) := by
  subst n
  rfl

/-- All global port assignments, including every replica and both route choices,
are represented once by the rectangular array quantified by the trace cursor. -/
def cursorBoundary : (A).shape.Boundary ≃ Fields (q+1) B.cursorCopies O D where
  toFun label i s L := cursorWord low offsets slots (label (arcCast B.cursor_degree ((i,s),L)))
  invFun f z := let v := (arcCast B.cursor_degree).symm z
                (cursorWord low offsets slots).symm (f v.1.1 v.1.2 v.2)
  left_inv z := by
    funext v
    let e := arcCast (V := Fin (q+1)) (L := Lane (q+1)) B.cursor_degree
    let read : (Fin (q+1) × Fin (2^(B.exponent 0))) × Lane (q+1) → Fin (2^W) := z
    change (cursorWord low offsets slots).symm ((cursorWord low offsets slots) (read (e (e.symm v)))) = read v
    exact ((cursorWord low offsets slots).symm_apply_apply _).trans
      (congrArg read (e.apply_symm_apply v))
  right_inv f := by
    funext i s L
    simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply]

def cursorOutPort (i : Fin (q+1)) (L : Lane (q+1)) (s : Fin ((B.cursorCopies+1)*2)) :
    (A).shape.graph.Port (i,L) := ⟨(arcCast B.cursor_degree ((i,s),L),false),rfl⟩

def cursorInPort (i : Fin (q+1)) (L : Lane (q+1)) (s : Fin ((B.cursorCopies+1)*2)) :
    (A).shape.graph.Port (i,L) :=
  ⟨((A).graph.actualTarget.symm (arcCast B.cursor_degree ((i,s),L)),true),by
    change StageAddress.site ((A).graph.actualTarget ((A).graph.actualTarget.symm _))=(i,L)
    rw [Equiv.apply_symm_apply]
    rfl⟩

def cursorOut (i : Fin (q+1)) (L : Lane (q+1)) (x : (A).shape.Half (i,L)) :
    PortFields B.cursorCopies O D :=
  fun s => cursorWord low offsets slots (x (B.cursorOutPort hk low offsets slots i L s))

def cursorIn (i : Fin (q+1)) (L : Lane (q+1)) (x : (A).shape.Half (i,L)) :
    PortFields B.cursorCopies O D :=
  fun s => cursorWord low offsets slots (x (B.cursorInPort hk low offsets slots i L s))

theorem cursorOut_at (z : (A).shape.Boundary) (i : Fin (q+1)) (L : Lane (q+1)) :
    B.cursorOut hk low offsets slots i L ((A).shape.graph.atVertex z (i,L)) =
      outgoingPorts (B.cursorBoundary hk low offsets slots z) i L := rfl

theorem cursorIn_at (z : (A).shape.Boundary) (i : Fin (q+1)) (L : Lane (q+1)) :
    B.cursorIn hk low offsets slots i L ((A).shape.graph.atVertex z (i,L)) =
      incomingPorts hk (B.cursorBoundary hk low offsets slots z) i L := by
  funext s
  let u := ((i,s),L)
  let G := LaneCursor.graph hk (B.cursorCopies+1)
  change cursorWord low offsets slots (z ((A).graph.actualTarget.symm (arcCast B.cursor_degree u))) =
    cursorWord low offsets slots (z (arcCast B.cursor_degree (G.actualTarget.symm u)))
  exact congrArg (fun j => cursorWord low offsets slots (z j)) (targetCast B.cursor_degree G u)

/-- A factor uses both incident halves in the original trivalent port order. -/
def cursorFactor (K : Fin (q+1) → Lane (q+1) → PortFields B.cursorCopies O D → PortFields B.cursorCopies O D → F) :
    (A).shape.Factors F := fun v x => K v.1 v.2 (B.cursorOut hk low offsets slots v.1 v.2 x)
      (B.cursorIn hk low offsets slots v.1 v.2 x)

theorem cursor_contract (K : Fin (q+1) → Lane (q+1) → PortFields B.cursorCopies O D → PortFields B.cursorCopies O D → F) :
    (A).shape.contract (B.cursorFactor hk low offsets slots K) =
      ∑ f : Fields (q+1) B.cursorCopies O D, ∏ i, ∏ L, K i L (outgoingPorts f i L) (incomingPorts hk f i L) := by
  unfold Shape.contract PortGraph.contraction
  rw [← (B.cursorBoundary hk low offsets slots).sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  change (∏ v : Fin (q+1)×Lane (q+1), _) = _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro a _
  exact congrArg₂ (K i a) (B.cursorOut_at hk low offsets slots z i a)
    (B.cursorIn_at hk low offsets slots z i a)


end ThreeFlat.Diagonal.PhysicalStage.Block

end
end OAI
