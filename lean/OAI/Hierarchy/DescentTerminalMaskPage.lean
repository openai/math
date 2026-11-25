import OAI.Hierarchy.DescentTerminalCellCoordinates
import OAI.Hierarchy.DescentTerminalClippedFields
import OAI.Hierarchy.DescentPackedLocalAtoms

namespace OAI
/-! # Packing the measured live cells into a single terminal page -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentSIMDLookup DescentPackedLocalAtoms
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {q t H N A w V C groups blocks B : ℕ}
local notation "width" => span q t H N A w
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
local notation "Venue" => (f : Fin 8)→Word (sized f)
local notation "Inputs" => BlockFields q t H N A w groups blocks

def densified (mask : Fin C→Word 1) (cells : Fin C→Venue) : Rows := fun f=>
  (wordBits _).symm fun j=>
    let z:Fin V×Fin (sized f):=finProdFinEquiv.symm j
    wordBits _ (field V mask (fun c=>cells c f) z.1) z.2

def homePage (fit : V*width≤B) (data : Inputs) :=
  clippedPage (densified (blankAt data) (cellAt data)) fit

end
end Hierarchy.DescentTerminalVertexFields

end OAI
