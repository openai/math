import OAI.Hierarchy.DescentFallbackItemGeometry
import OAI.Hierarchy.DescentResetStemCompactOrder

namespace OAI
/-! # The old signed local order is the actual item order of each installed tree cell -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking
open DescentPackedFallbackTree
open DescentFallbackItemSelect DescentContactTree
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃Fin groups×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht)
    (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site => (A.pos u).2)
    (filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le ..)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "theSite" => DescentIssuedFallbackPanel.endSite A


local notation "slots" => 2^(m-c)*(2*A.cap)
local notation "treeBook" => fun s t=>(R).fallbackBook s t
local notation "dest" => fun s t=>(treeBook s t).codes


local notation "item" s:arg t:arg => DescentRouterSlots.Item (R).contact (R).owner s (.inr t)
local notation "spatial" s:arg t:arg => DescentFixedNamedContact.code (dest s t) (DescentRouterSlots.link (R).contact (R).owner s (.inr t))
local notation "row" s:arg e:arg => finProdFinEquiv (localAddress («c»:=c) A native S ready digits frame.basis s e)


variable (vertex : V↪Fin (Fintype.card V)) (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (sorted : SourceSorted W order)
local notation "chron" => DescentOrderedReset.grains W A.grainCount order
local notation "whereHost" t => frame.host.symm (T.code t).1
local notation "coarseBin" t => selectedRoot A S ready Z T t
local notation "oldOrdinal" t:arg e:arg => sourceDigit A digits frame.basis fits vertex (whereHost t) (coarseBin t) e

include indexed sorted in
theorem fallback_cell_order (s : Bool) (t : Z.Fallback) (depth : ℕ)
    (a : DescentTreePrefixIntervals.Bits depth) (it : Fin slots→DescentFallbackItemSelect.Item)
    (actual : ∀e : item s t,(it (row s e.val)).key=
      ⟨oldOrdinal t e.val,(outgoingSlot A S ready order e.val).val,e.val.2.val⟩)
    (u v : Cell (spatial s t) depth a) :
    DescentFallbackItemSelect.before it (row s u.val.val) (row s v.val.val) ↔
      chron u.val.val<chron v.val.val := by
  let ky : (Cell (spatial s t) depth a)↪Fin _ :=
    (Function.Embedding.subtype _).trans ((Function.Embedding.subtype _).trans chron)
  apply chronological ky (fun e=>row s e.val.val) it _ u v
  intro x y
  rw [actual x.val,actual y.val]
  exact (scope_before A S ready digits frame.basis fits vertex (whereHost t) (coarseBin t)
    ready.coordinates indexed order sorted s x.val.val y.val.val
    (falls_parameters A S ready digits Z T frame x.val.property)
    (falls_parameters A S ready digits Z T frame y.val.property)).symm

include indexed sorted in
theorem issued_fallback_item (s : Bool) (t : Z.Fallback) (depth : ℕ)
    (ok : depth≤(treeBook s t).height) (a : DescentTreePrefixIntervals.Bits depth) (it : Fin slots→DescentFallbackItemSelect.Item)
    (actual : ∀e : item s t,(it (row s e.val)).key=
      ⟨oldOrdinal t e.val,(outgoingSlot A S ready order e.val).val,e.val.2.val⟩)
    (measured : ∀j,(it j).leaf=(leafPanel A S ready digits native Z T frame s t j).map Fin.val)
    (e : Cell (spatial s t) depth a) (m₀ : ℕ) (batch : Fin m₀) :
    let printed:=(Finset.univ.filter (fun j : Cell (spatial s t) depth a=>chron j.val.val<chron e.val.val)).card*m₀+batch.val
    select it (rows Ht (List.ofFn a) it) (printed/m₀)=some (row s e.val.val) :=
  flattened_item A S ready digits native Z T frame chron s t depth ok a it measured
    (fallback_cell_order A S ready digits native Z T frame vertex indexed order sorted s t depth a it actual) e m₀ batch

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
