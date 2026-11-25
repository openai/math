import OAI.Hierarchy.DescentHaloRebaseMount
import OAI.Hierarchy.DescentHaloChartHeader
import OAI.Hierarchy.DescentHaloPackedReverseRank

namespace OAI
/-! # Reading a variable forward path for each live group in one packed native batch -/
namespace Hierarchy.DescentHaloPackedRebase
open DescentSIMDLookup DescentSharedCableNames DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H G M w P : ℕ}
local notation "b" => Packed.bits P

/-- Each selected occurrence supplies only its own short forward path in
`paths`. The variable per-rack lookup consumes the genuine shared table and
writes all purchased group digits, including inactive zero padding. -/
theorem run (T : Headers P) (Z : DescentPackedZip.Tables) (paths : Expr) (out : ℕ)
    (room : Fits T H G M w out) (zip : DescentPackedZip.Fits Z (context T) paths (b*P) b M out w)
    (space : out+H*chunks G M<2^w) (value : Fin H→Fin P→Fin (P+1)) (queries : Fin H→Fin G→Option (Fin P))
    (m : Memory w) (tables : Reads T value M G m) (fixed : DescentPackedZip.Static Z (fetch P) M m)
    (queryRead : DescentPackedZip.Source paths (fun h i=>Packed.token (queries h i)) M m) :
    let e:=Z.read (context T) paths
    let result:=image out (H*chunks G M) e m
    (scan w out (H*chunks G M) e).Exec m result (4+H*chunks G M*(2*e.work+4)) ∧
      (∀p : Row H G M,result (out+(row H G M p).val)=((data (fun h g=>fetch P (digest (value h)) (Packed.token (queries h g))) p).val:Word w)) ∧
      CheapCode (scan w out (H*chunks G M) e) :=by
  intro e result
  have ft : e.Fits w out:=⟨zip.apply,zip.right,zip.shift,zip.left⟩
  have mounted:=DescentPackedZip.read_data Z (context T) paths out zip (fetch P) ghost m fixed _ _ (source T out room value m tables) queryRead
  exact ⟨scan_exec _ _ _ _ ft space,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M p)).trans (mounted p),by apply scan_cheap⟩

end
end Hierarchy.DescentHaloPackedRebase

end OAI
