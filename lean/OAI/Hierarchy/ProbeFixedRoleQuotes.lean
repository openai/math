import OAI.Hierarchy.ProbeNativePacketRows
import OAI.Hierarchy.ProtocolRAMCommonCopies

namespace OAI
/-! # Portwise price quantization and the gain of the actual admitted row -/

noncomputable section
namespace Hierarchy.AdaptiveProbe.ColumnWires

variable {A B C H I E : Type*} {k : ℕ}

theorem grid_at_ports (M : ℝ) (len : H → ℝ) (idx : A → I)
    (port : Role C H (A⊕B) k → E) (kind : E → Option I) (fee : E → ℝ)
    (price : I → ℝ) (grid : A → ℝ) (error : ℝ) (positive : 0 ≤ error)
    (ordinary : ∀ r,kind (port r)=account idx r)
    (external : ∀ r,account idx r=none → fee (port r)=printed M len r)
    (digits : ∀ a,grid a ≤ price (idx a) ∧ price (idx a) ≤ grid a+error) (r) :
    let q := quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid) r
    q ≤ activePrice kind fee price (port r) ∧ activePrice kind fee price (port r) ≤ q+error := by
  have physical : activePrice kind fee price (port r) = activePrice (account idx) (printed M len) price r := by
    unfold activePrice
    rw [ordinary]
    cases h : account idx r with
    | none => exact external r h
    | some i => rfl
  rw [physical,← quote_active]
  cases r with
  | extra v =>
    cases v with
    | inl a => exact digits a
    | inr b => exact ⟨le_rfl,le_add_of_nonneg_right positive⟩
  | catalyst | radius | cross | horizontal => exact ⟨le_rfl,le_add_of_nonneg_right positive⟩

end Hierarchy.AdaptiveProbe.ColumnWires

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram AdaptiveProbe ColumnWires
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators Fin.CommRing

variable {F A B C H I : Type*} [Field F] [Fintype A] [Fintype B] [Fintype C] [Fintype H]
    {k sites N w D rows : ℕ} [Nonempty (Fin sites)]
local notation "Roles" => Role C H (A⊕B) k
variable [Nonempty (Role C H (A⊕B) k)] {edge : Role C H (A⊕B) k → Chord sites}
    {req : ((C×Fin k)⊕A) → Role C H (A⊕B) k} {box : Set (Role C H (A⊕B) k → ℝ)}
    {ε tree M γ : ℝ} {s : StockCommit} {mem : Memory w}

/-- The exact two word streams admit the nominal-width rate after the printed
payment fields and ordinary stock digits have been decoded. -/
theorem selected_role_quote (menu : Probe.FixedMenu F edge req box ε tree N)
    (len : H → ℝ) (grid : A → ℝ)
    (legal : quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid) ∈ box)
    (failed : ε ≤ Probe.discrepancy F edge req (quote M len (LocalCommodity.extraPrice (B:=B) grid))) :
    let key := quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid)
    let i := menu.select ⟨key,legal,failed⟩
    let P := menu.packet i
    ∀ (extra : ℕ) (b : Batch (P.terms+extra) D) (layout : PortPlan s b mem rows) (j : Fin rows)
      (R : NativePacketRow P extra b layout j) (idx : A → I) (kind : Fin D → Option I)
      (fee : Fin D → ℝ) (price : I → ℝ) (br err : ℝ) (K width : ℕ),
      0 ≤ γ → γ ≤ menu.margin → 0 ≤ err →
      (∀ r,kind (R.ports r)=account idx r) →
      (∀ r,account idx r=none → fee (R.ports r)=printed M len r) →
      (∀ a,grid a ≤ price (idx a) ∧ price (idx a) ≤ grid a+err) →
      br ≤ b.copies*(tree*P.selectorBits) → (Fintype.card Roles:ℝ)*b.maxWidth*err ≤ P.width*γ/2 →
      copied K P.width width ≤ b.copies →
      (∑ v,(installedBits s.columns mem (layout.enum ⟨j,v⟩):ℝ)*activePrice kind fee price v)+br+
        (copied K P.width width:ℝ)*(P.width*γ/2) ≤
        ∑ v,(consumedBits s.columns mem (layout.enum ⟨j,v⟩):ℝ)*activePrice kind fee price v := by
  intro key i P extra b layout j R idx kind fee price br err K width γpos margin pos ordinary external digits broadcast precision scale
  have record := selected_menu_quote menu (fun _ : Unit => key) (fun _ => legal) () failed extra b layout j R
    (activePrice kind fee price) (b.copies*(tree*P.selectorBits)) err γ pos margin
    (grid_at_ports M len idx R.ports kind fee price grid err pos ordinary external digits) rfl precision
  have smaller : (copied K P.width width:ℝ)*(P.width*γ/2) ≤ (b.copies:ℝ)*(P.width*γ/2) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr scale) (by positivity)
  exact (add_le_add (add_le_add le_rfl broadcast) smaller).trans record.2

end Hierarchy.ProtocolRAM.Calendar.StockCommit
end

end OAI
