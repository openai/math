import OAI.Hierarchy.DescentContactPreROM

namespace OAI
/-! # Reading post-trunk contact quantities through the retained original sparse pitch table -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentPackedZip DescentContactProbePitch
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Layout) {k b w : ℕ} (board : NonlinearExpanders.Graph A.n k)
    (reads : Fin A.oldFields→Expr) (prior : Bool→Fin A.half→Fin 5→Expr)
    (budget : A.Space reads prior w)
local notation "H" => A.hosts
local notation "P" => A.shapes
local notation "G" => A.groups
local notation "M" => A.batch
local notation "B" => A.fieldBits

/-- The address table inside the original marker date survives every later write outside
its exact range. Its original-host source argument can have been issued after the table. -/
theorem post_view (initial later : Memory w)
    (kept : ∀addr,addr<A.markerBase→later addr=A.memory board reads prior budget initial addr)
    (x : Expr) (values : Fin H→Fin G→Cell b) (source : Source x values M later) :
    Source (A.priorView x) (DescentContactProbePitch.lift (S:=P) values) M later:=by
  let short:=A.fields_fit reads prior budget
  have upper:=A.ordered.2.2.2.1.trans A.ordered.2.2.2.2
  have fits:A.markerBase<2^w:=upper.trans_lt budget.extent
  have marker:=(A.marker_any board (A.fields prior) short budget.extent budget.marker
      (A.frontImage reads initial)).2.2
  have stored (addr : ℕ) (h : addr<A.markerBase) : later addr=A.frontImage reads initial addr:=
    (kept addr h).trans (marker addr (.inl h))
  intro p
  change (x.atRow (value H P G M B A.pitchBase 0)).eval later _=_
  rw [eval_atRow,eval_below (value H P G M B A.pitchBase 0) _ (A.frontImage reads initial) later
    ⟨table_fits _ _ _ _ _ _ fits 0,trivial⟩ stored]
  rw [show (value H P G M B A.pitchBase 0).eval (A.frontImage reads initial) _=_ from
    map_read _ _ _ fits p]
  exact source (oldRow p)

theorem late_view_fits (upper : ℕ) (past : A.markerBase≤upper) (space : A.markerBase<2^w)
    (x : Expr) (valid : x.Fits w upper) : (A.priorView x).Fits w upper:=
  ProtocolRAM.Calendar.CatalogueRows.fits_atRow x _ valid
    (ProtocolRAMGeneratedWrite.fits_mono _ past
      (show (value H P G M B A.pitchBase 0).Fits w A.markerBase from
        ⟨table_fits _ _ _ _ _ _ space 0,trivial⟩))

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
