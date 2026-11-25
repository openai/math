import OAI.Hierarchy.DescentOrderedGoodRouter
import OAI.Hierarchy.DescentOrderedRotorDigits
import OAI.Hierarchy.DescentCanonicalScalars
import OAI.Hierarchy.DescentRotorRootRefs

namespace OAI
/-! # The real boundary source of every bit compared by an ordered rotor tap -/

namespace Hierarchy.DescentResetGates
open LinearAlgebra.SpectralBooks ThreeFlat
open Computability.BorderVNP.Crossing DescentRotor DescentPhysicalSplit DescentKernelHistory DescentRouterSlots DescentOrderedReset
open scoped Classical BigOperators
noncomputable section
section SplitHost
variable {d : ℕ} {T Q : Type} [Fintype T] {bitsAt : T → ℕ} (host : Network d T bitsAt)
    (place : Q → T) (widths : Q → ℕ)

/-- The two port adapters of the ordered rotor retain the split host's sites, cables,
and cable widths. Their composite attaches an external slot at `place q`. -/
private abbrev rotorPortWidth (v : DescentPhysicalSplit.Vertex host) :=
  boundaryWidth (DescentLocalAdapters.graph (DescentPhysicalSplit.graph host) place widths) v

private abbrev rotorAssignmentBit (a : (DescentPhysicalSplit.graph host).Assignment) (pins : Ports widths)
    (v : DescentPhysicalSplit.Vertex host) : BitRef (rotorPortWidth host place widths v) → Bool :=
  assignmentBit (DescentLocalAdapters.graph (DescentPhysicalSplit.graph host) place widths) a pins v

end SplitHost

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
local notation "ord" => Ordered.orderedAddress idAt src dst hw
local notation "H" => Physical.host G.arcs D P.layers C₀ bits u
local notation "positionAt" => DescentGoodRouter.position D u contact input site owner s w first last
local notation "widthAt" => rotorPortWidth H positionAt lens
local notation "readAt" => rotorAssignmentBit H positionAt lens
local notation "pinsAt" => DescentGoodRouter.Ordered.pins D u contact input site owner align s w G first last P key
local notation "X" => slotSource key contact wt input site owner align s w D
local notation "Y" => slotTarget key contact wt input site owner s w D

private theorem bundle_extract {L q b : ℕ} (x : Fin L→Fin q→Fin (2^b)) (r : Fin L) (k : Fin q) (j : Fin b) :
    (Physical.bundle L q b).symm x (digitBit r k j)=(bitWord b).symm (x r k) j := by
  have packs:=bundle_digit ((Physical.bundle L q b).symm x) r k
  rw [Equiv.apply_symm_apply] at packs
  rw [packs,Equiv.symm_apply_apply]

def portRefFalse (v : Fin (2^n)) (k : Fin u) (e : {e // src e=v}) :
    BitRef (widthAt (tap H (.inl (v,false)))) :=
  let q := rootSlot D contact input site owner wt s w (root contact input site owner s w align e.val)
  ⟨.inr ⟨q,by
    have atRow : DescentGoodRouter.position D u contact input site owner s w first last q=(v,false) := by
      simpa only [q,DescentGoodRouter.position,names_root,Sum.elim_inl] using
        congrArg (fun r : Fin (2^n) => (r,false)) e.property
    exact congrArg (fun k : Fin (2^n) × Bool => tap H (.inl k)) atRow⟩,
    sourceAt key contact wt input owner s w e.val k⟩

def portRefTrue (v : Fin (2^n)) (k : Fin u) (e : {e // dst e=v}) :
    BitRef (widthAt (tap H (.inl (v,true)))) :=
  let q := linkSlot D contact input site owner wt s w (link contact owner s w e.val)
  ⟨.inr ⟨q,by
    have atRow : DescentGoodRouter.position D u contact input site owner s w first last q=(v,true) := by
      simpa only [q,DescentGoodRouter.position,names_link,Sum.elim_inr] using
        congrArg (fun r : Fin (2^n) => (r,true)) e.property
    exact congrArg (fun k : Fin (2^n) × Bool => tap H (.inl k)) atRow⟩,
    Fin.cast (linkWidth D contact input site owner wt s w _).symm (linkAt key contact wt owner s w e.val k)⟩

def selectSource {U V : Type} {width : U→ℕ} (f : V→BitRef width) : Bool⊕V →Source width :=
  Sum.elim Source.fixed (fun x=>.bit (f x))

private theorem select_read {U V : Type} {width : U→ℕ} (f : V→BitRef width)
    (x : BitRef width→Bool) (z : Bool⊕V) :
    (selectSource f z).read x=z.elim id (fun v=>x (f v)) := by cases z <;> rfl

def publicTapSource (b : Bool) (v : Fin (2^n)) (r : Fin P.layers) (k : Fin u) (j : Fin bits) :
    Source (widthAt (tap H (.inl (v,b)))) := by
  cases b
  · exact selectSource (portRefFalse D u contact input site owner align s w G first last P key v k)
      (Ordered.focus ord (fun p=>(P.choose p,p.1)) src (fun _=>rfl) r v j)
  · exact selectSource (portRefTrue D u contact input site owner align s w G first last P key v k)
      (Ordered.focus ord (fun p=>(P.choose p,p.2.1)) dst (fun _=>rfl) r v j)

omit [Fintype R] in
theorem publicTap_read (a : (DescentPhysicalSplit.graph H).Assignment) (pins : Ports lens) (b : Bool) (v : Fin (2^n)) (r : Fin P.layers)
    (k : Fin u) (j : Fin bits) :
    (publicTapSource D u contact input site owner align s w G first last P key b v r k j).read (readAt a pins (tap H (.inl (v,b)))) =
      pinsAt pins (v,b) (digitBit r k j) := by
  cases b
  · change (selectSource _ _).read _ = (Physical.bundle _ _ _).symm _ _
    rw [select_read,bundle_extract]
    exact Ordered.focus_read ord (fun p=>(P.choose p,p.1)) src (fun _=>rfl) r v j (X pins) k
  · change (selectSource _ _).read _ = (Physical.bundle _ _ _).symm _ _
    rw [select_read,bundle_extract]
    exact Ordered.focus_read ord (fun p=>(P.choose p,p.2.1)) dst (fun _=>rfl) r v j (Y pins) k

/-- The old leg is an actual public packet or the corresponding carried arc.
The stride decomposition implements the three packed coordinates. -/
def legSource : (e : Leg H)→Fin (DescentPhysicalSplit.width H e) → Source (widthAt (tap H e))
  | .inl (v,b),t =>
    let z := (finProdFinEquiv : Fin P.layers × Fin (u*bits) ≃ Fin (P.layers*(u*bits))).symm t
    let q := (finProdFinEquiv : Fin u × Fin bits ≃ Fin (u*bits)).symm z.2
    publicTapSource D u contact input site owner align s w G first last P key b v z.1 q.1 q.2
  | .inr (e,false),j => .bit ⟨.inl ⟨.inl e,Or.inl rfl⟩,j⟩
  | .inr (e,true),j => .bit ⟨.inl ⟨.inl e,Or.inr rfl⟩,j⟩

omit [Fintype R] in
theorem leg_read (a : (DescentPhysicalSplit.graph H).Assignment) (pins : Ports lens) (e : Leg H) (j : Fin (DescentPhysicalSplit.width H e)) :
    (legSource D u contact input site owner align s w G first last P key e j).read (readAt a pins (tap H e))=visible H (decode H a).1 (pinsAt pins) e j := by
  rcases e with ⟨v,b⟩|⟨e,(_|_)⟩
  · obtain ⟨⟨r,rest⟩,rfl⟩ := (finProdFinEquiv : Fin P.layers × Fin (u*bits) ≃ Fin (P.layers*(u*bits))).surjective j
    obtain ⟨⟨k,j⟩,rfl⟩ := (finProdFinEquiv : Fin u × Fin bits ≃ Fin (u*bits)).surjective rest
    simpa only [legSource, Equiv.symm_apply_apply, DescentPhysicalSplit.visible, digitBit] using
      publicTap_read D u contact input site owner align s w G first last P key a pins b v r k j
  · rfl
  · rfl

def tapLegSource (v : Fin (2^n)) (i : Fin (count H v)) (j : Fin (localWidth H v i)) :
    Source (widthAt ⟨v,.inr i⟩) :=
  Eq.ndrec (motive := fun t => Source (widthAt t)) (legSource D u contact input site owner align s w G first last P key (name H v i) j) (tap_named H v i)

omit [Fintype R] in
theorem tapLegSource_read (a : (DescentPhysicalSplit.graph H).Assignment) (pins : Ports lens) (v : Fin (2^n))
    (i : Fin (count H v)) (j : Fin (localWidth H v i)) :
    (tapLegSource D u contact input site owner align s w G first last P key v i j).read
      (readAt a pins ⟨v,.inr i⟩)=args H (decode H a).1 (pinsAt pins) v i j := by
  let e:=name H v i
  have transfer (v₀ v₁ : DescentPhysicalSplit.Vertex H) (eqn : v₀=v₁) (z : Source (widthAt v₀)) :
      (Eq.ndrec (motive := fun t => Source (widthAt t)) z eqn).read (readAt a pins v₁)=
        z.read (readAt a pins v₀) := by cases eqn;rfl
  exact (transfer _ _ (tap_named H v i) (legSource D u contact input site owner align s w G first last P key e j)).trans
    (leg_read D u contact input site owner align s w G first last P key a pins e j)

end
end Hierarchy.DescentResetGates

end OAI
