import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Execute one native operand lookup on all packed sites and groups -/
namespace Hierarchy.DescentPackedZip
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

theorem lookup_run {H G M w a b c : ℕ} (rule : Cell a→Cell b→Cell c) (zero : rule 0 0=0)
    (tables : Tables) (left right : Expr) (out : ℕ) (m : Memory w)
    (x : Fin H→Fin G→Cell a) (y : Fin H→Fin G→Cell b)
    (fit : Fits tables left right a b M out w) (safe : out+H*chunks G M<2^w)
    (rom : Static tables rule M m) (oldX : Source left x M m) (oldY : Source right y M m) :
    let term:=tables.read left right
    let last:=image out (H*chunks G M) term m
    (scan w out (H*chunks G M) term).Exec m last (4+(H*chunks G M)*(2*term.work+4)) ∧
      (∀p : Row H G M,last (out+(row H G M p).val)=
        ((data (fun h g=>rule (x h g) (y h g)) p).val:Word w)) ∧
      (∀i,i<out ∨ out+H*chunks G M≤ i → last i=m i) ∧ CheapCode (scan w out (H*chunks G M) term) := by
  intro term last
  have valid : term.Fits w out := ⟨fit.apply,fit.right,fit.shift,fit.left⟩
  have values:=read_data tables left right out fit rule zero m rom x y oldX oldY
  exact ⟨scan_exec out _ term m valid safe,
    fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ m (row H G M p)).trans (values p),
    fun i away=>ProtocolRAMGeneratedWrite.frame_image _ _ _ m i away,
    by intro P R K pc reg pub exit j;exact scan_cheap w out _ term pc reg pub exit j⟩

end
end Hierarchy.DescentPackedZip

end OAI
