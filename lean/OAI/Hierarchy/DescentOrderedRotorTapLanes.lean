import OAI.Hierarchy.DescentLaneGates
import OAI.Hierarchy.DescentOrderedRotorTapRefs
import OAI.Hierarchy.DescentOrderedGoodRouter
import OAI.Hierarchy.DescentOrderedRotorDigits
import OAI.Hierarchy.DescentCanonicalScalars
import OAI.Hierarchy.DescentRotorRootRefs

namespace OAI
/-! # Uniform, affine source lanes at every installed ordered rotor tap -/

namespace Hierarchy.DescentResetGates
open LinearAlgebra.SpectralBooks ThreeFlat
open Computability.BorderVNP.Crossing DescentRotor DescentPhysicalSplit DescentKernelHistory DescentRouterSlots DescentOrderedReset
open DescentLaneGates
open private rotorPortWidth rotorAssignmentBit from OAI.Hierarchy.DescentOrderedRotorTapRefs
open scoped Classical BigOperators
noncomputable section
section Shape
variable {E K : Type} [Fintype E] [Field K] (D u : ℕ) {n h bits C₀ : ℕ}
variable (G : NonlinearExpanders.Graph n h) {hw : 0<bits} {pay : ℝ} {src dst : E→Fin (2^n)}
variable (P : BaseCircuit K G C₀ bits u hw src dst pay)
local notation "H" => Physical.host G.arcs D P.layers C₀ bits u

def legBits : Leg H→ℕ
  | .inl _=>bits
  | .inr _=>C₀*bits

local notation "Bq" => legBits D u G P

def legDigitAt : (e : Leg H)→Fin P.layers→Fin u→Fin (Bq e)→Fin (DescentPhysicalSplit.width H e)
  | .inl _,r,k,j => digitBit r k j
  | .inr _,r,k,j => digitBit r k j

local notation "digit" => legDigitAt D u G P

def tapBits (v : Fin (2^n)) (i : Fin (count H v)) := Bq (name H v i)

def legDigit (v : Fin (2^n)) (i : Fin (count H v)) (r : Fin P.layers) (k : Fin u)
    (j : Fin (tapBits D u G P v i)) : Fin (localWidth H v i) := digit (name H v i) r k j

private theorem legBits_le (e : Leg H) : Bq e≤ max bits (C₀*bits) := by
  rcases e with q|q
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem tapBits_le (v : Fin (2^n)) (i : Fin (count H v)) :
    tapBits D u G P v i≤ max bits (C₀*bits) := legBits_le D u G P (name H v i)

private theorem leg_width_eq (e : Leg H) : DescentPhysicalSplit.width H e=P.layers*(u*Bq e) := by
  rcases e with q|q <;> rfl

theorem tapWidth_eq (v : Fin (2^n)) (i : Fin (count H v)) :
    localWidth H v i=P.layers*(u*tapBits D u G P v i) :=
  leg_width_eq D u G P (name H v i)

private theorem digit_val (e : Leg H) (r : Fin P.layers) (k : Fin u) (j : Fin (Bq e)) :
    (digit e r k j).val=j.val+Bq e*(k.val+u*r.val) := by
  rcases e with q|q
  · change j.val+bits*k.val+(u*bits)*r.val=j.val+bits*(k.val+u*r.val)
    ring
  · change j.val+(C₀*bits)*k.val+(u*(C₀*bits))*r.val=j.val+(C₀*bits)*(k.val+u*r.val)
    ring

theorem legDigit_val (v : Fin (2^n)) (i : Fin (count H v)) (r : Fin P.layers) (k : Fin u)
    (j : Fin (tapBits D u G P v i)) :
    (legDigit D u G P v i r k j).val=j.val+tapBits D u G P v i*(k.val+u*r.val) :=
  digit_val D u G P (name H v i) r k j

end Shape

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

variable {m p : ℕ}

def batchDigit (hu : u=m*p) (k : Fin m) (d : Fin p) : Fin u :=
  Fin.cast hu.symm (finProdFinEquiv (k,d))

private theorem stepVal (hu : u=m*p) (k : Fin m) (d : Fin p) :
    (batchDigit u hu k d).val=d.val+p*k.val := rfl

private def affine {Q : Type} {size : Q→ℕ} (port : Q) (start stride : ℕ)
    (proj : Fin p→Fin (size port)) (hits : ∀d,(proj d).val=start+stride*d.val) : Lane p size where
  port:=port
  start:=start
  stride:=stride
  fits d:=hits d ▸ (proj d).isLt

private theorem affine_read {Q : Type} {size : Q→ℕ} (port : Q) (start stride : ℕ)
    (proj : Fin p→Fin (size port)) (hits : ∀d,(proj d).val=start+stride*d.val)
    (d : Fin p) : (affine port start stride proj hits).atBit d=⟨port,proj d⟩ :=
  congrArg (Sigma.mk port) (Fin.ext (hits d).symm)

local notation "pFalse" => portRefFalse D u contact input site owner align s w G first last P key
local notation "pTrue" => portRefTrue D u contact input site owner align s w G first last P key
local notation "batch" => batchDigit u

def falseLane (hu : u=m*p) (v : Fin (2^n)) (k : Fin m)
    (e : {e // src e=v}) (hp : 0<p) :
    Lane p (widthAt (tap H (.inl (v,false)))) := by
  let proj := fun d : Fin p=>pFalse v (batch hu k d) e
  let off := DescentOrderedWords.offset (fibreKey key (input s) (input s e.val.val))
    (fun z=>wt z.val) ⟨e.val.val,rfl⟩
  exact affine (proj ⟨0,hp⟩).1 (off+p*k.val) 1 (fun d=>(proj d).2) (fun d=>by
    change off+(d.val+p*k.val)=_
    omega)

def trueLane (hu : u=m*p) (v : Fin (2^n)) (k : Fin m)
    (e : {e // dst e=v}) (hp : 0<p) :
    Lane p (widthAt (tap H (.inl (v,true)))) := by
  let proj := fun d : Fin p=>pTrue v (batch hu k d) e
  let off := DescentOrderedWords.offset (fibreKey key contact (contact e.val.val))
    (fun z=>wt z.val) ⟨e.val.val,rfl⟩
  exact affine (proj ⟨0,hp⟩).1 (off+p*k.val) 1 (fun d=>(proj d).2) (fun d=>by
    change off+(d.val+p*k.val)=_
    omega)

def focusLane {Q E : Type} {size : Q→ℕ} (f : E→Lane p size) : Bool⊕E→LaneSource p size :=
  Sum.elim LaneSource.fixed (fun e=>.wire (f e))

def publicTapLane (hu : u=m*p) (hp : 0<p) (b : Bool) (v : Fin (2^n)) (r : Fin P.layers)
    (k : Fin m) (j : Fin bits) : LaneSource p (widthAt (tap H (.inl (v,b)))) := by
  cases b
  · exact focusLane (fun e=>falseLane D u contact input site owner align s w G first last P key hu v k e hp)
      (Ordered.focus ord (fun z=>(P.choose z,z.1)) src (fun _=>rfl) r v j)
  · exact focusLane (fun e=>trueLane D u contact input site owner align s w G first last P key hu v k e hp)
      (Ordered.focus ord (fun z=>(P.choose z,z.2.1)) dst (fun _=>rfl) r v j)

local notation "publicLane" => publicTapLane D u contact input site owner align s w G first last P key
local notation "publicBit" => publicTapSource D u contact input site owner align s w G first last P key

private theorem sameBitRef {Q : Type} {size : Q→ℕ} {a b : BitRef size}
    (port : a.1=b.1) (index : a.2.val=b.2.val) : a=b := by
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  change a=b at port
  subst b
  exact congrArg (Sigma.mk a) (Fin.ext index)

omit [Fintype R] in
theorem publicTapLane_read (hu : u=m*p) (hp : 0<p) (b : Bool) (v : Fin (2^n))
    (r : Fin P.layers) (k : Fin m) (j : Fin bits) (d : Fin p)
    (x : BitRef (widthAt (tap H (.inl (v,b))))→Bool) :
    (publicLane hu hp b v r k j).read x d=(publicBit b v r (batch hu k d) j).read x := by
  cases b
  · unfold publicTapLane publicTapSource
    cases Ordered.focus ord (fun z=>(P.choose z,z.1)) src (fun _=>rfl) r v j with
    | inl val => rfl
    | inr e =>
      apply congrArg x
      change (falseLane D u contact input site owner align s w G first last P key hu v k e hp).atBit d =
        pFalse v (batch hu k d) e
      apply sameBitRef
      · rfl
      · let off := DescentOrderedWords.offset (fibreKey key (input s) (input s e.val.val))
          (fun z=>wt z.val) ⟨e.val.val,rfl⟩
        change (off+p*k.val)+1*d.val=off+(d.val+p*k.val)
        omega
  · unfold publicTapLane publicTapSource
    cases Ordered.focus ord (fun z=>(P.choose z,z.2.1)) dst (fun _=>rfl) r v j with
    | inl val => rfl
    | inr e =>
      apply congrArg x
      change (trueLane D u contact input site owner align s w G first last P key hu v k e hp).atBit d =
        pTrue v (batch hu k d) e
      apply sameBitRef
      · rfl
      · let off := DescentOrderedWords.offset (fibreKey key contact (contact e.val.val))
          (fun z=>wt z.val) ⟨e.val.val,rfl⟩
        change (off+p*k.val)+1*d.val=off+(d.val+p*k.val)
        omega

local notation "Bq" => legBits D u G P
local notation "digit" => legDigitAt D u G P

def supplyLane {Q : Type} {size : Q→ℕ} (port : Q) (R b : ℕ) (sz : size port=R*(u*b))
    (hu : u=m*p) (r : Fin R) (k : Fin m) (j : Fin b) : Lane p size :=
  affine port (j.val+b*(p*k.val)+(u*b)*r.val) b
    (fun d=>Fin.cast sz.symm (digitBit r (batch hu k d) j)) (fun d=>by
      change j.val+b*(d.val+p*k.val)+(u*b)*r.val=_
      ring)

def legLane (hu : u=m*p) (hp : 0<p) :
    (e : Leg H)→Fin P.layers→Fin m→Fin (Bq e)→LaneSource p (widthAt (tap H e))
  | .inl (v,b),r,k,j=>publicLane hu hp b v r k j
  | .inr (e,false),r,k,j =>.wire (supplyLane u (.inl ⟨.inl e,Or.inl rfl⟩) P.layers (C₀*bits) rfl hu r k j)
  | .inr (e,true),r,k,j =>.wire (supplyLane u (.inl ⟨.inl e,Or.inr rfl⟩) P.layers (C₀*bits) rfl hu r k j)

local notation "fetchLane" => legLane D u contact input site owner align s w G first last P key
local notation "fetchBit" => legSource D u contact input site owner align s w G first last P key

omit [Fintype R] in
theorem legLane_read (hu : u=m*p) (hp : 0<p) (e : Leg H) (r : Fin P.layers)
    (k : Fin m) (j : Fin (Bq e)) (d : Fin p) (x : BitRef (widthAt (tap H e))→Bool) :
    (fetchLane hu hp e r k j).read x d=(fetchBit e (digit e r (batch hu k d) j)).read x := by
  rcases e with ⟨v,b⟩|⟨z,(_|_)⟩
  · have read := publicTapLane_read D u contact input site owner align s w G first last P key hu hp b v r k j d x
    cases b <;> simpa only [legLane,legDigitAt,legSource,digitBit,Equiv.symm_apply_apply] using read
  · exact congrArg x (affine_read _ _ _ _ _ d)
  · exact congrArg x (affine_read _ _ _ _ _ d)

def tapLegLane (hu : u=m*p) (hp : 0<p) (v : Fin (2^n)) (i : Fin (count H v))
    (r : Fin P.layers) (k : Fin m) (j : Fin (tapBits D u G P v i)) :
    LaneSource p (widthAt ⟨v,.inr i⟩) :=
  Eq.ndrec (motive := fun t => LaneSource p (widthAt t))
    (fetchLane hu hp (name H v i) r k j) (tap_named H v i)

omit [Fintype R] in
theorem tapLegLane_read (hu : u=m*p) (hp : 0<p) (a : (DescentPhysicalSplit.graph H).Assignment) (pins : Ports lens)
    (v : Fin (2^n)) (i : Fin (count H v)) (r : Fin P.layers) (k : Fin m)
    (j : Fin (tapBits D u G P v i)) (d : Fin p) :
    (tapLegLane D u contact input site owner align s w G first last P key hu hp v i r k j).read
      (readAt a pins ⟨v,.inr i⟩) d=
        args H (decode H a).1 (pinsAt pins) v i (legDigit D u G P v i r (batch hu k d) j) := by
  let e:=name H v i
  have move (v₀ v₁ : DescentPhysicalSplit.Vertex H) (eqn : v₀=v₁) (z : LaneSource p (widthAt v₀)) :
      (Eq.ndrec (motive := fun t => LaneSource p (widthAt t)) z eqn).read (readAt a pins v₁) d =
        z.read (readAt a pins v₀) d := by cases eqn;rfl
  exact (move _ _ (tap_named H v i) (fetchLane hu hp e r k j)).trans <|
    (legLane_read D u contact input site owner align s w G first last P key hu hp e r k j d _).trans
      (leg_read D u contact input site owner align s w G first last P key a pins e (digit e r (batch hu k d) j))

private def strideOf {Q : Type} {size : Q→ℕ} : LaneSource p size→ℕ
  | .fixed _=>0
  | .wire l=>l.stride

omit [Fintype R] in
private theorem publicStride (hu : u=m*p) (hp : 0<p) (b : Bool) (v : Fin (2^n))
    (r : Fin P.layers) (k : Fin m) (j : Fin bits) : strideOf (publicLane hu hp b v r k j)≤1 := by
  cases b
  · unfold publicTapLane
    cases Ordered.focus ord (fun z=>(P.choose z,z.1)) src (fun _=>rfl) r v j with
    | inl _=>exact Nat.zero_le 1
    | inr _=>exact Nat.le_refl _
  · unfold publicTapLane
    cases Ordered.focus ord (fun z=>(P.choose z,z.2.1)) dst (fun _=>rfl) r v j with
    | inl _=>exact Nat.zero_le 1
    | inr _=>exact Nat.le_refl _

omit [Fintype R] in
private theorem legStride (hu : u=m*p) (hp : 0<p) (e : Leg H) (r : Fin P.layers)
    (k : Fin m) (j : Fin (Bq e)) :
    strideOf (fetchLane hu hp e r k j)≤ max 1 (max bits (C₀*bits)) := by
  rcases e with ⟨v,b⟩|⟨arc,(_|_)⟩
  · exact (publicStride D u contact input site owner align s w G first last P key hu hp b v r k j).trans (le_max_left _ _)
  · exact (le_max_right bits (C₀*bits)).trans (le_max_right _ _)
  · exact (le_max_right bits (C₀*bits)).trans (le_max_right _ _)

omit [Fintype R] in
theorem tapLegLane_stride (hu : u=m*p) (hp : 0<p) (v : Fin (2^n)) (i : Fin (count H v))
    (r : Fin P.layers) (k : Fin m) (j : Fin (tapBits D u G P v i))
    (l : Lane p (widthAt ⟨v,.inr i⟩))
    (yes : tapLegLane D u contact input site owner align s w G first last P key hu hp v i r k j=.wire l) :
    l.stride≤ max 1 (max bits (C₀*bits)) := by
  have move (v₀ v₁ : DescentPhysicalSplit.Vertex H) (eqn : v₀=v₁) (z : LaneSource p (widthAt v₀)) :
      strideOf (Eq.ndrec (motive := fun t => LaneSource p (widthAt t)) z eqn)=strideOf z := by cases eqn;rfl
  calc
    l.stride = strideOf (tapLegLane D u contact input site owner align s w G first last P key hu hp v i r k j) := by
      simp only [yes,strideOf]
    _ = strideOf (fetchLane hu hp (name H v i) r k j) := move _ _ (tap_named H v i) _
    _ ≤ _ := legStride D u contact input site owner align s w G first last P key hu hp (name H v i) r k j

end
end Hierarchy.DescentResetGates

end OAI
