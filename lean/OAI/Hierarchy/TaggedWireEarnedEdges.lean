import OAI.Hierarchy.TaggedWireStripPacketReads
import OAI.Hierarchy.ProbePaidBirthRow

namespace OAI
/-! The original row numbers used by the earned strip's physical installation. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip
open scoped Classical Fin.CommRing

variable {S : PurchaseSampler} {h d k n w : ℕ} {A B : Type}
local notation "C" => TreeColumn n
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "Ports" => StripPorts S h d k C (Fin n) B
local notation "E" => Edges S h d k
variable (b : Board) (order : Fin b.coreRows ≃ Edges S h d k)

/-- The old commodity role uses the separate stock row during installation.
All other cases point into the catalogue, retaining both physical radii. -/
def earnedIndex (col : C → Columns h d) (horizontal : Fin n → ColumnLayer k→E)
    (birth : B→Fin b.boughtRows) (unused : Fin b.rows) : R→Fin b.rows
  | .catalyst c j=>b.coreIndex (order.symm (.inl (.inl (col c,j,false))))
  | .radius c j side=>b.coreIndex (order.symm (.inl (.inl (col c,j,side))))
  | .cross c a s t=>b.coreIndex (order.symm (.inl (.inr (.inl (col c,crossDatum a s t)))))
  | .horizontal i l=>b.coreIndex (order.symm (horizontal i l))
  | .extra (.inr j)=>b.boughtIndex (birth j)
  | .extra (.inl _)=>unused

def earnedMate (col : C → Columns h d) (c : C) (j : Fin k) : Fin b.rows :=
  b.coreIndex (order.symm (.inl (.inl (col c,j,true))))

theorem StripPorts.earned_indices (p : Ports) (m : Memory w) (reg : Word w)
    (loaded : CoreLookup.Loaded p.directory order m) (room : b.rows<2^w)
    (col : C → Columns h d) (column : ∀c,((p.column c).eval m reg).val=((Fintype.equivFin _) (col c)).val)
    (horizontal : Fin n → ColumnLayer k→E)
    (roads : ∀e l,(p.horizontal e l).eval m reg=((order.symm (horizontal e l)).val:Word w))
    (birth : B→Fin b.boughtRows)
    (born : ∀j,(p.probe j).eval m reg=((b.boughtIndex (birth j)).val:Word w))
    (unused : Fin b.rows) :
    (∀r : R,paidRole r→((p.primary b r).eval m reg).val=(earnedIndex b order col horizontal birth unused r).val) ∧
    (∀c j,((p.mate b (.catalyst c j : R)).eval m reg).val=(earnedMate b order col c j).val) := by
  have word (e : Fin b.rows) (x : Word w) (eq : x=(e.val:Word w)) : x.val=e.val := by
    rw [eq,Fin.val_cast_of_lt (e.isLt.trans room)]
  let key (c : C) : Fin (CoreLookup.positions h d) :=
    ⟨_,((Fintype.equivFin _) (col c)).isLt.trans_le (Nat.le_max_left _ _)⟩
  have radius (c : C) (j : Fin k) (side : Bool) :
      (b.coreOnly (p.radiusAt c j side)).eval m reg =
        ((order.symm (.inl (.inl (col c,j,side)))).val : Word w) :=
    b.coreOnly_read _ m reg _ room
      (loaded.read _ (p.column c) reg (key c) (column c) _
        (CoreLookup.resolve_radius (col c) j side))
  constructor
  · intro r good
    apply word
    cases r with
    | catalyst c j => exact radius c j false
    | radius c j side => exact radius c j side
    | cross c a s t =>
      let x := crossDatum a s t
      exact b.coreOnly_read _ m reg _ room
        (loaded.read _ (p.column c) reg (key c) (column c) _
          (CoreLookup.resolve_cross (col c) x.1 x.2.1 x.2.2))
    | horizontal e l => exact b.coreOnly_read _ m reg _ room (roads e l)
    | extra e =>
      cases e with
      | inl a => exact good.elim
      | inr j => exact born j
  · intro c j
    exact word (earnedMate b order col c j) _ (radius c j true)


/-- Resolve both ends and both indices in one pass over the original typed
role. Horizontal and birth facts name the genuine physical row of the same
term. The pad is used only by an unused index in the old-stock case. -/
theorem StripPorts.earned_geometry (p : Ports) (m : Memory w) (reg : Word w)
    (loaded : CoreLookup.Loaded p.directory order m) (room : b.rows<2^w)
    (π : Equiv.Perm (Fin (2^h))) (col : C → Columns h d)
    (extra : A⊕B→DistinctPair (TreeSite n k))
    (column : ∀c,((p.column c).eval m reg).val=((Fintype.equivFin _) (col c)).val)
    (row : Fin b.rows→Site h d k×Site h d k)
    (core : ∀f,row (b.coreIndex (order.symm f))=CoreBoard.ends π f)
    (roads : ∀e l, ∃f:E,(p.horizontal e l).eval m reg=((order.symm f).val:Word w) ∧
      HorizontalFaces col (AdaptiveProbe.Strip.horizontal n e) l (CoreBoard.ends π f))
    (born : ∀j, ∃a:Fin b.boughtRows,(p.probe j).eval m reg=((b.boughtIndex a).val:Word w) ∧
      Faces (Prod.map col id) (extra (.inr j)) (row (b.boughtIndex a)))
    (unused : Fin b.rows) :
    ∃idx : R→Fin b.rows, ∃mate : C→Fin k→Fin b.rows,
      (∀r : R,paidRole r→((p.primary b r).eval m reg).val=(idx r).val) ∧
      (∀c j,((p.mate b (.catalyst c j : R)).eval m reg).val=(mate c j).val) ∧
      (∀e l (v : Fin b.rows),((b.coreOnly (p.horizontal e l)).eval m reg).val=v.val →
        Faces (Prod.map col id) (ColumnWires.ends (AdaptiveProbe.Strip.horizontal n) extra (.horizontal e l)) (row v)) ∧
      (∀j (v : Fin b.rows),((p.probe j).eval m reg).val=v.val →
        Faces (Prod.map col id) (extra (.inr j)) (row v)) := by
  choose f hread faces using roads
  choose birth hborn incident using born
  obtain ⟨first,second⟩:=p.earned_indices (A:=A) b order m reg loaded room col column f hread birth hborn unused
  refine ⟨_,_,first,second,?_,?_⟩
  · intro e l v observed
    have same:=b.coreOnly_read _ m reg _ room (hread e l)
    have fit : (order.symm (f e l)).val<2^w:=(b.coreIndex (order.symm (f e l))).isLt.trans room
    have V : v=b.coreIndex (order.symm (f e l)):=Fin.ext <|
      observed.symm.trans ((congrArg Fin.val same).trans (Fin.val_cast_of_lt fit))
    rw [V,core]
    exact faces e l
  · intro j v observed
    have fit:=(b.boughtIndex (birth j)).isLt.trans room
    have V : v=b.boughtIndex (birth j):=Fin.ext <|
      observed.symm.trans ((congrArg Fin.val (hborn j)).trans (Fin.val_cast_of_lt fit))
    rw [V]
    exact incident j

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
