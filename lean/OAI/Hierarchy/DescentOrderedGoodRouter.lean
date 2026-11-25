import OAI.Hierarchy.DescentGoodRouter
import OAI.Hierarchy.DescentOrderedRotorPins
import OAI.Hierarchy.DescentOrderedResetRows

namespace OAI
/-! # Boundary tables of a real paid rotor using chronological physical digits -/

namespace Hierarchy.DescentGoodRouter.Ordered
open Computability.BorderVNP.Crossing DescentRouterSlots DescentNamedContact DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open DescentOrderedReset
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
variable (s : Bool) (w : W) {n h bits C₀ N : ℕ} (G : NonlinearExpanders.Graph n h) {hw : 0<bits} {pay : ℝ}
variable (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "wt" => fun _ : I=>u
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
local notation "src" => (fun e : Item contact owner s w => first (root contact input site owner s w align e))
local notation "dst" => (fun e : Item contact owner s w => last (link contact owner s w e))
variable (P : BaseCircuit K G C₀ bits u hw
  (fun e : Item contact owner s w => first (root contact input site owner s w align e))
  (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin N)
local notation "idAt" => itemKey key contact owner s w
local notation "pos" => position D u contact input site owner s w first last
local notation "M" => Physical.rotor G P D

abbrev source := slotSource key contact wt input site owner align s w D
abbrev target := slotTarget key contact wt input site owner s w D

local notation "X" => source D u contact input site owner align s w key
local notation "Y" => target D u contact input site owner s w key

def pins (p : Ports lens) := DescentRotor.Ordered.actualPins P idAt (X p) (Y p)
local notation "pinsAt" => pins D u contact input site owner align s w G first last P key

omit [Fintype R] in
theorem local_pins : DescentLocalAdapters.Local M pos lens pinsAt := by
  intro v x y same q built
  rcases q with ⟨col,(_|_)⟩
  · apply congrArg (Physical.bundle _ _ _).symm
    funext r
    apply Physical.layer_local P.choose (fun p=>p.1) (DescentRotor.Ordered.orderedAddress idAt src dst hw) src
      (fun e=>rfl) (X x) (X y) r col
    intro e row
    let q := rootSlot D contact input site owner wt s w (root contact input site owner s w align e)
    have placed : pos q = (col,false) := by
      simpa only [q,position,names_root,Sum.elim_inl] using
        congrArg (fun t : Fin (2^n) => (t,false)) row
    have kept := same q ((congrArg (Physical.rotor G P D).attach placed).trans built)
    funext j
    exact congrFun kept _
  · apply congrArg (Physical.bundle _ _ _).symm
    funext r
    apply Physical.layer_local P.choose (fun p=>p.2.1) (DescentRotor.Ordered.orderedAddress idAt src dst hw) dst
      (fun e=>rfl) (Y x) (Y y) r col
    intro e row
    let q := linkSlot D contact input site owner wt s w (link contact owner s w e)
    have placed : pos q = (col,true) := by
      simpa only [q,position,names_link,Sum.elim_inr] using
        congrArg (fun t : Fin (2^n) => (t,true)) row
    have kept := same q ((congrArg (Physical.rotor G P D).attach placed).trans built)
    funext j
    exact congrFun kept _

/-- Same paid device, sites, widths and fixed interior scalar tables.
Its boundary adapter reads explicit prefix addresses directly. -/
def tables : (device D u contact input site owner align s w G first last P).Tables K :=
  DescentLocalAdapters.tables M pos lens (Physical.rotorTables G P D) pinsAt

omit [Fintype R] in
theorem value (p : Ports lens) :
    (device D u contact input site owner align s w G first last P).value
      (tables D u contact input site owner align s w G first last P key) p =
      if ∀e,X p e=Y p e then 1 else 0 :=
  (DescentLocalAdapters.value M pos lens _ pinsAt
    (local_pins D u contact input site owner align s w G first last P key) p).trans
    (DescentRotor.Ordered.actual_value G P idAt _ _)

omit [Fintype R] in
/-- Reading the packed coarse public cable and the joining cable both use the
original bundle ID followed by its true bit ordinal. -/
theorem visible_read (p : Ports (DescentRouterBank.publicWidth input wt)) (links : (B).Assignment)
    (i : Item contact owner s w) (j : Fin u) :
    let z := DescentNetworkSubstitution.visible B links p (s,w)
    X z i j=p (s,input s i.val) (sourceAt key contact wt input owner s w i j) ∧
      Y z i j=links (contact i.val) (linkAt key contact wt owner s w i j) :=
  DescentOrderedReset.visible_read key contact wt input site owner align s w D p links i j

end
end Hierarchy.DescentGoodRouter.Ordered

end OAI
