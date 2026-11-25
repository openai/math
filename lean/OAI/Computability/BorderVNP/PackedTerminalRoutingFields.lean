import OAI.Computability.BorderVNP.PackedTerminalCellOrdinals
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldFrame
import OAI.Computability.BorderVNP.ParseBatchRawWord

/-! # Final site, edge, and port fields read from the retained history

The current edge pointers and widths are the actual sparse wires of the
returned route table. The owner is obtained by the product-deck ordinal
lookup. Grouped external ports refer to retained original site IDs. The
additional site-width wires can be produced by the retained computation
alongside the site route.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Crossing Cover Cover.AddressCircuit Shortening Shortening.PublicCapacity
open Shortening.PublicEndpoints Packing.CellAddressCircuit Packing.CellAddressPhysical
open Diagonal.ExternalSew.FieldExport ParseBatchSort VPVNP.VerifierNetwork
open private storedSite_occupied from OAI.Computability.BorderVNP.ShortenPublicEndpointSemantics
open scoped Classical

/-- One original site number per bottom bundle and tile, in row-major order. -/
def groupRow {groups tiles : ℕ} (offset : Fin groups → ℕ) (j : Fin (groups*tiles)) : ℕ :=
  let z : Fin groups × Fin tiles := finProdFinEquiv.symm j
  offset z.1+z.2.val

theorem groupRow_pair {groups tiles : ℕ} (offset : Fin groups → ℕ) (z : Fin groups × Fin tiles) :
    groupRow offset (finProdFinEquiv z) = offset z.1+z.2.val := by simp [groupRow]

/-- The static selector for an original private description. The clipping
case makes the table total on arbitrary schedules. True bundle/tile pairs
are always within the terminal rectangle by retained-row ancestry. -/
def originalPins {groups tiles V : ℕ} (pos : 0<V) (offset : Fin groups → ℕ) (i : Fin (groups*tiles)) : Fin V :=
  if h : groupRow offset i < V then ⟨groupRow offset i,h⟩ else ⟨0,pos⟩

/-- A genuine original description selects the physical row of its surviving
site on every branch, independently of the intermediate motions. -/
theorem originalPin_value {groups tiles V : ℕ} (pos : 0<V) (offset : Fin groups → ℕ)
    (z : Fin groups × Fin tiles) (row : Fin V) (name : offset z.1+z.2.val = row.val) :
    originalPins pos offset (finProdFinEquiv z) = row := by
  have within : groupRow offset (finProdFinEquiv z) < V := (groupRow_pair offset z).trans name ▸ row.isLt
  exact Fin.ext (by rw [originalPins,dite_eq_left within]; exact (groupRow_pair offset z).trans name)

variable {D q d V E n C w b : ℕ} {I : Type} {Move σ : Type*} [Fintype I] [Fintype Move] [Fintype σ]
    (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C)

/-- Routed input, retained site widths, decoded cell ordinals, and the two constant references. -/
abbrev Wires (Move : Type*) (q d V E w b : ℕ) :=
  ((RouteRows.Pins Move q (d+1) V E w ⊕ (Fin V × Fin w)) ⊕ (Fin V × Fin b)) ⊕ Bool

/-- One pass through the history output and the cell catalog, retaining every sparse row. -/
noncomputable def boundFrame (cf : C ≤ 2^b) (route : Frame σ (RouteRows.Pins Move q (d+1) V E w))
    (aux : Frame σ (Fin V × Fin w)) : Frame σ (Wires Move q d V E w b) :=
  let raw := parallelFrame route aux
  let pick := Frame.initial (Sum.inl : RouteRows.Pins Move q (d+1) V E w → _ ⊕ (Fin V × Fin w))
  let compute := ((frame enum number cf Move).subst pick).withInput.subst raw
  (constants _).subst compute

private def routed (i : RouteRows.Pins Move q (d+1) V E w) : Wires Move q d V E w b := .inl (.inl (.inl i))

/-- Fixed port pointers and lengths read through the two constant wires. All cable
and site values read the shared history computation. -/
def fields (vf : V ≤ 2^w) (cf : C ≤ 2^b) (portHost : Fin n → ℕ) (portBits : Fin n → ℕ) :
    Fields V E n C w b w (Wires Move q d V E w b) where
  sites := Fin.castLEEmb vf
  cells := Fin.castLEEmb cf
  owner i j := .inl (.inr (i,j))
  ptr
    | .inl (.inl i),j => routed (.inr (.inr (.inr (i,.inr (true,j)))))
    | .inl (.inr i),j => routed (.inr (.inr (.inr (i,.inr (false,j)))))
    | .inr i,j => .inr ((portHost i).testBit (w-1-j.val))
  edgeWidth i j := routed (.inr (.inr (.inr (i,.inl j))))
  auxWidth i j := .inl (.inl (.inr (i,j)))
  portWidth i j := .inr ((portBits i).testBit (w-1-j.val))

/-- The named old cable pointers, widths, holes, and dynamic final cell are obtained
from the returned route table; the auxiliary frame runs on the same assignment. -/
theorem route_represents {P K : Type*} {bits : P → ℕ} (N : Pack D P bits K) {L : ℝ} (r : SiteRoutes N I d L)
    {S : Shape} (rows : Rows S N.layout) (dummy : Fin S.edges → N.layout.Site) (portID : P ↪ Fin n)
    (vf : S.sites ≤ 2^w) (cf : C ≤ 2^b) (portHost : Fin n → ℕ) (portBits : Fin n → ℕ)
    (portAddr : ∀ p, portHost (portID p) = (rows.site (N.layout.attach p)).val)
    (portWidth : ∀ p, portBits (portID p) = bits p) (portRoom : ∀ p, portBits p < 2^w)
    (portHole : ∀ i ∉ Set.range portID, portBits i = 0)
    (route : Frame σ (RouteRows.Pins (allowedMoves I L) q (d+1) S.sites S.edges w))
    (aux : Frame σ (Fin S.sites × Fin w)) (x : σ → Bool)
    (ready : RouteRows.Ready enum N r rows dummy (route.eval x)) (size : N.layout.Site → ℕ)
    (atSite : ∀ v, value (fun j => aux.eval x (rows.site v,j)) = size v)
    (empty : ∀ i ∉ Set.range rows.site, value (fun j => aux.eval x (i,j)) = 0) :
    Packing.CellAddressPhysical.Represents N.layout (fun v => number (reduceMove d (r.origin v))) size
      rows.site rows.edge portID (fields vf cf portHost portBits)
      ((boundFrame enum number cf route aux).eval x) := by
  let Y := (boundFrame enum number cf route aux).eval x
  have raw (a : RouteRows.Pins (allowedMoves I L) q (d+1) S.sites S.edges w) :
      Y (routed a) = route.eval x a := by simp [Y,boundFrame,routed,constants_eval]
  have stage (i : Fin S.sites) (j : Fin w) : Y (.inl (.inl (.inr (i,j)))) = aux.eval x (i,j) := by
    simp [Y,boundFrame,constants_eval]
  have con (a : Bool) : Y (.inr a) = a := by simp [Y,boundFrame,constants_eval]
  have owners (i : Fin S.sites) (j : Fin b) :
      Y (.inl (.inr (i,j))) = (frame enum number cf (allowedMoves I L)).eval (route.eval x) (i,j) := by
    have selected : (Frame.initial (Sum.inl : RouteRows.Pins (allowedMoves I L) q (d+1) S.sites S.edges w →
        _ ⊕ (Fin S.sites × Fin w))).eval ((parallelFrame route aux).eval x) = route.eval x := by
      funext a; simp
    simp [Y,boundFrame,constants_eval,selected]
  change Packing.CellAddressPhysical.Represents N.layout _ size rows.site rows.edge portID _ Y
  have loc (e : N.layout.Edge) (side : Bool) :
      value (fun j => route.eval x (.inr (.inr (.inr (rows.edge e,.inr (side,j)))))) =
        (rows.site (if side then N.layout.src e else N.layout.dst e)).val :=
    (ready.names.addresses _ _).trans (congrArg Fin.val (storedSite_occupied ..))
  have edge (e : N.layout.Edge) :
      value (fun j => route.eval x (.inr (.inr (.inr (rows.edge e,.inl j))))) = N.layout.width e :=
    (ready.names.widths _).trans (Packing.Names.width_slot ..)
  constructor
  · intro v
    simpa only [fields,Function.comp_def,owners,Fin.castLEEmb_apply,Fin.val_castLE] using owner_value enum number cf N r rows dummy (route.eval x) ready v
  · intro e; simpa [fields,Function.comp_def,raw] using loc e true
  · intro e; simpa [fields,Function.comp_def,raw] using loc e false
  · intro p
    simp only [fields,Function.comp_def,con,ParseRecords.bigValue_testBit,Fin.castLEEmb_apply,Fin.val_castLE]
    rw [portAddr,Nat.mod_eq_of_lt ((rows.site (N.layout.attach p)).isLt.trans_le vf)]
  · intro e; simpa only [fields,Function.comp_def,raw] using edge e
  · intro v; simpa only [fields,Function.comp_def,stage] using atSite v
  · intro p
    simp only [fields,Function.comp_def,con,ParseRecords.bigValue_testBit]
    rw [Nat.mod_eq_of_lt (portRoom (portID p)),portWidth]
  · intro i hi
    have val := (ready.names.widths i).trans (Packing.Names.unused_row N.layout rows.edge dummy i hi).2.2
    simpa only [fields,Function.comp_def,raw] using val
  · intro i hi; simpa only [fields,Function.comp_def,stage] using empty i hi
  · intro i hi
    simp only [fields,Function.comp_def,con,ParseRecords.bigValue_testBit]
    rw [Nat.mod_eq_of_lt (portRoom i),portHole i hi]

omit [Fintype I] in
/-- The sparse cell lookup is shared across all current endpoints. -/
theorem boundFrame_size (cf : C ≤ 2^b) (route : Frame σ (RouteRows.Pins Move q (d+1) V E w))
    (aux : Frame σ (Fin V × Fin w)) :
    (boundFrame enum number cf route aux).size ≤ route.size+aux.size+(frame (V:=V) (E:=E) (w:=w) enum number cf Move).size+2 := by
  simp only [boundFrame,Frame.subst_size,Frame.withInput_size,parallelFrame_size,Frame.initial_size,Nat.zero_add]
  exact Nat.add_le_add_left (constants_size _) _

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
