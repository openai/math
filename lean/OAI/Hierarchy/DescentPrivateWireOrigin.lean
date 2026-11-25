import OAI.Hierarchy.DescentBundlePrivateRelabel
import OAI.Hierarchy.DescentBundleQuotient

namespace OAI
/-! # Actual source wires and donor slots of the two ordinary captures -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentNetworkPartition Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {P C Tag : Type} [Fintype C] {n d p : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (loc : N.Site→C) (pos : C→EuclideanSpace ℝ (Fin d)) (ball : ∀c,‖pos c‖≤1)
variable (r : SiteBits (U:=Tag) N) (s : ∀v,Shape p (r v)) (edge : ∀e,p∣N.width e) (hp : 0<p)
local notation "Q" => quotient N loc pos ball
local notation "qr" => quotientBits N loc pos ball r
local notation "qs" => quotientShape N loc pos ball r s edge
abbrev WireWord (p : ℕ) := Σe : N.Edge, Fin (N.width e/p)
abbrev OccupiedWord := Σu : N.Site,((s u).recipe hp).UsedWord
local notation "born" c => (fun e : PrivateEdge N loc c=>N.width e.val)

def quotientWordAt (c : C) : ((qs c).recipe hp).UsedWord↪(WireWord N p ⊕ OccupiedWord N r s hp) :=
  let key:=liveSource hp (fun i : {u //loc u=c}=>r i.val) (born c)
    (quotientBit N loc pos ball c) (fun i=>s i.val) (fun e=>edge e.val) (quotientMap N loc pos ball c)
  let fromCable : BornWord (p:=p) (born c) ↪ WireWord N p :=
    ⟨fun x=>⟨x.1.val,x.2⟩,by rintro ⟨⟨e,h⟩,x⟩ ⟨⟨e',h'⟩,y⟩ eqn;cases eqn;rfl⟩
  let fromDonor : (Σi : {u //loc u=c},((s i.val).recipe hp).UsedWord)↪OccupiedWord N r s hp :=
    ⟨fun x=>⟨x.1.val,x.2⟩,by rintro ⟨⟨u,h⟩,x⟩ ⟨⟨u',h'⟩,y⟩ eqn;cases eqn;rfl⟩
  have key_inj : Function.Injective key :=
    liveSource_injective hp (fun i : {u // loc u=c} => r i.val) (born c)
      (quotientBit N loc pos ball c) (fun i => s i.val) (fun e => edge e.val) (quotientMap N loc pos ball c)
  (⟨key,key_inj⟩ : _ ↪ _).trans (fromCable.sumMap fromDonor)

def ownership : WireWord N p⊕OccupiedWord N r s hp→C :=
  Sum.elim (fun t=>loc (N.src t.1)) (fun t=>loc t.1)

theorem quotient_owner (c : C) (h : ((qs c).recipe hp).UsedWord) :
    ownership N loc r s hp (quotientWordAt N loc pos ball r s edge hp c h)=c := by
  rcases h with ⟨⟨e|⟨u,h⟩,j⟩,used⟩
  · exact e.property.1
  · exact u.property

/-- These are the actual old source-wire and old operand identities. The site
of the quotient is recoverable from either kind of identity. -/
def quotientOrigin : OccupiedWord (Q) (qr) (qs) hp↪(WireWord N p⊕OccupiedWord N r s hp) where
  toFun x:=quotientWordAt N loc pos ball r s edge hp x.1 x.2
  inj' := by
    rintro ⟨c,x⟩ ⟨e,y⟩ eqn
    have owner:=congrArg (ownership N loc r s hp) eqn
    change ownership _ _ _ _ _ (quotientWordAt _ _ _ _ _ _ _ _ c x)=
      ownership _ _ _ _ _ (quotientWordAt _ _ _ _ _ _ _ _ e y) at owner
    rw [quotient_owner,quotient_owner] at owner
    subst e
    exact congrArg (Sigma.mk c) ((quotientWordAt N loc pos ball r s edge hp c).injective eqn)

variable {D : Type} [Fintype D] {d' : ℕ} (place : C→D) (pt : D→EuclideanSpace ℝ (Fin d'))
    (hb : ∀u,‖pt u‖≤1)
local notation "newQ" => quotient (Q) place pt hb
local notation "newR" => quotientBits (Q) place pt hb (qr)
local notation "newS" => quotientShape (Q) place pt hb (qr) (qs) (fun e=>edge e.val)

def survivingWire : WireWord (Q) p↪WireWord N p where
  toFun x:=⟨x.1.val,x.2⟩
  inj' := by rintro ⟨⟨e,h⟩,x⟩ ⟨⟨e',h'⟩,y⟩ eqn;cases eqn;rfl

/-- The outer left summand is a second-stage capture. The inner left summand
is a first-stage capture. Both refer to the same original raw wire namespace.
Every other used word is an actual previously used word at its own old site. -/
def doubleOrigin : OccupiedWord (newQ) (newR) (newS) hp↪
    (WireWord N p⊕(WireWord N p⊕OccupiedWord N r s hp)) :=
  (quotientOrigin (Q) place pt hb (qr) (qs) (fun e=>edge e.val) hp).trans
    ((survivingWire N loc pos ball).sumMap (quotientOrigin N loc pos ball r s edge hp))

def originHome : WireWord N p⊕(WireWord N p⊕OccupiedWord N r s hp)→D :=
  Sum.elim (fun e=>place (loc (N.src e.1))) (fun t=>place (ownership N loc r s hp t))

theorem double_home (v : D) (x : ((newS v).recipe hp).UsedWord) :
    originHome N loc r s hp place (doubleOrigin N loc pos ball r s edge hp place pt hb ⟨v,x⟩)=v := by
  let firstMap:=quotientOrigin N loc pos ball r s edge hp
  let forward:=(survivingWire (p:=p) N loc pos ball).sumMap firstMap
  have atHome:=quotient_owner (Q) place pt hb (qr) (qs) (fun e=>edge e.val) hp v x
  let source:=quotientWordAt (Q) place pt hb (qr) (qs) (fun e=>edge e.val) hp v x
  change originHome N loc r s hp place (forward source)=v
  change ownership (Q) place (qr) (qs) hp source=v at atHome
  rw [←atHome]
  cases source with
  | inl cable=>rfl
  | inr h=>
    exact congrArg place (quotient_owner N loc pos ball r s edge hp h.1 h.2)

/-- Only the previous sites and raw cables belonging to this actual cell
participate in its private name book. -/
def doubleAt (v : D) : ((newS v).recipe hp).UsedWord ↪
    {z : WireWord N p ⊕ (WireWord N p ⊕ OccupiedWord N r s hp) //originHome N loc r s hp place z=v} where
  toFun x:=⟨doubleOrigin N loc pos ball r s edge hp place pt hb ⟨v,x⟩,
    double_home N loc pos ball r s edge hp place pt hb v x⟩
  inj' := by
    intro a b same
    have pair:=(doubleOrigin N loc pos ball r s edge hp place pt hb).injective (congrArg Subtype.val same)
    cases pair
    rfl

end
end Hierarchy.DescentBundleHistory

end OAI
