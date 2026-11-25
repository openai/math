import OAI.Hierarchy.DescentPrivateOldDonors
import OAI.Hierarchy.DescentBundlePrivateRelabel
import OAI.Hierarchy.DescentBundleReentry

namespace OAI
/-! # Every occupied private operand of a reset comes from one original site -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentLocalPrivateNames DescentOrderedWords DescentNamedContact DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {Tag A B : Type} {p : ℕ} (hp : 0<p) {w : A→ℕ} {v : B→ℕ} {r : BitRecipe Tag A w}
variable (s : Shape p r) {route : BitRef w→BitRef v} (f : BlockMap p w v route)
local notation "oldR" => s.recipe hp
local notation "newR" => (s.reroute f).recipe hp

theorem rerouteLen (u : r.Node) : (newR).arity u=(oldR).arity u :=
  (congrArg List.length (reroute_keys s f u)).trans
    (List.length_map («as» := s.keys u) (Sum.map f.map id))

theorem reroute_operand (u : r.Node) (j : Fin ((oldR).arity u)) :
    (newR).operand u (Fin.cast (rerouteLen hp s f u).symm j)=((oldR).operand u j).map f.map id := by
  have original : j.val < (s.keys u).length := j.isLt
  have moved : j.val < ((s.reroute f).keys u).length :=
    (Fin.cast (rerouteLen hp s f u).symm j).isLt
  have cell : ((s.reroute f).keys u)[j.val]'moved =
      ((s.keys u)[j.val]'original).map f.map id :=
    (getElem_congr (reroute_keys s f u) (rfl : j.val = j.val) moved).trans
      (List.getElem_map (Sum.map f.map id))
  refine (congrArg (Sum.map id (privateIndex hp)) cell).trans ?_
  change (((s.keys u)[j.val]'original).map f.map id).map id (privateIndex hp) =
    (((s.keys u)[j.val]'original).map id (privateIndex hp)).map f.map id
  cases (s.keys u)[j.val]'original <;> rfl

def rerouteLive : (newR).UsedWord ≃ (oldR).UsedWord where
  toFun a:=⟨a.val,(reroute_used hp s f a.val).1 a.property⟩
  invFun a:=⟨a.val,(reroute_used hp s f a.val).2 a.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

private theorem donorPair_injective {I : Type*} {T : I → Type*} {D K : ℕ}
    (donor : I ↪ Fin D) (slot : ∀ i, T i ↪ Fin K) :
    Function.Injective (fun t : Σ i, T i => finProdFinEquiv (donor t.1, slot t.1 t.2)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ eqn
  have pair := finProdFinEquiv.injective eqn
  have same : i = j := donor.injective (congrArg Prod.fst pair)
  subst j
  exact congrArg (Sigma.mk i) ((slot i).injective (congrArg Prod.snd pair))

section
variable {n d L : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bs : P→ℕ}
variable (N : Network n P bs) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e) (old : SiteBits (U:=X) N) (src : ∀v,Shape p (old v)) (h : H)
local notation "M" => DescentResetTrunks.network N home group R
local notation "rr" => oldGather N home group R key old h
local notation "sh" => oldGatherShape N home group R key whole old src h
local notation "result" => (inShape N home group R key whole old src h).recipe hp
local notation "bw" => boundaryWidth (M) (.inl (false,h))
local notation "noWidth" => (Empty.elim : Empty→ℕ)
local notation "rt" => (fun (_ : Fibre home h) (b : BitRef bw)=>(Sum.inl b : BitRef bw⊕BitRef noWidth))
local notation "maps" => (fun _ : Fibre home h=>({map:=id,read:=fun _ _=>rfl} : BlockMap p bw bw id).publicOnly)

def gatherDonor (i : Fibre home h) : ((sh i).recipe hp).UsedWord ≃ ((src i.val).recipe hp).UsedWord := by
  rcases i with ⟨u,rfl⟩
  exact rerouteLive hp (src u) (oldBlockMap N home group R key whole u)

/-- The empty captured-cable band of this particular product removes every fresh case of
the general contraction source. The surviving tag is an actual donor followed by its old word. -/
def insideDonor : (result).UsedWord ≃ (Σi : Fibre home h,((sh i).recipe hp).UsedWord) where
  toFun
    | ⟨⟨.inl z,_⟩,_⟩=>nomatch z
    | ⟨⟨.inr ⟨i,z⟩,j⟩,hit⟩=>⟨i,⟨⟨z,j⟩,(inherited_used hp rr noWidth rt sh (fun z => nomatch z) maps i ⟨z,j⟩).1 hit⟩⟩
  invFun t:=⟨oldWord rr noWidth rt t.1 t.2.val,
    (inherited_used hp rr noWidth rt sh (fun z => nomatch z) maps t.1 t.2.val).2 t.2.property⟩
  left_inv t:=by rcases t with ⟨⟨z|⟨i,z⟩,j⟩,yes⟩;exact z.elim;rfl
  right_inv t:=by rcases t with ⟨i,⟨⟨z,j⟩,yes⟩⟩;rfl

omit [Fintype Q] in
theorem actual_live_source (a : (result).UsedWord) :
    liveSource hp rr noWidth rt sh (fun z => nomatch z) maps a=Sum.inr (insideDonor hp N home group R key whole old src h a) := by
  rcases a with ⟨⟨z|⟨i,z⟩,j⟩,yes⟩
  · exact z.elim
  · rfl

def resetDonor : (result).UsedWord ≃ (Σi : Fibre home h,((src i.val).recipe hp).UsedWord) :=
  (insideDonor hp N home group R key whole old src h).trans
    (Equiv.sigmaCongrRight (gatherDonor hp N home group R key whole old src h))

/-- The new code has just two local fields. The second field is the donor's own first
old use, and refers to precisely its old scalar birth and operand position. -/
def donorAlias {D K : ℕ} (donor : Fibre home h↪Fin D)
    (prior : ∀i : Fibre home h,Slot ((src i.val).recipe hp)↪Fin K) : (result).UsedWord↪Fin (D*K) where
  toFun a:=let t:=resetDonor hp N home group R key whole old src h a
    finProdFinEquiv (donor t.1,firstAlias _ (prior t.1) t.2)
  inj' := (donorPair_injective donor (fun i => firstAlias _ (prior i))).comp
    (resetDonor hp N home group R key whole old src h).injective

omit [Fintype Q] in
theorem donorAlias_read {D K : ℕ} (donor : Fibre home h↪Fin D)
    (prior : ∀i : Fibre home h,Slot ((src i.val).recipe hp)↪Fin K) (a : (result).UsedWord) :
    let t:=resetDonor hp N home group R key whole old src h a
    ∃k : Slot ((src t.1.val).recipe hp),
      read _ k=some t.2 ∧ (donorAlias hp N home group R key whole old src h donor prior a).val=
        (prior t.1 k).val+K*(donor t.1).val := by
  let t:=resetDonor hp N home group R key whole old src h a
  obtain ⟨k,pos,uses⟩:=firstAlias_read _ (prior t.1) t.2
  exact ⟨k,uses,by change (firstAlias _ (prior t.1) t.2).val+K*(donor t.1).val=_;rw [←pos]⟩

omit [Fintype Q] in
/-- Read the same occupied operand at its old and new node, with the actual ordinal cast
from the two physical row lists. -/
theorem retained_operand (v : N.Site) (u : (old v).Node) (j : Fin (((src v).recipe hp).arity u))
    (t : ((src v).recipe hp).UsedWord) (was : ((src v).recipe hp).operand u j=.inr t.val) :
    let i : Fibre home (home v):=⟨v,rfl⟩
    let after:=(inShape N home group R key whole old src (home v)).recipe hp
    ∃(node : after.Node)(slot : Fin (after.arity node)),slot.val=j.val ∧
      after.operand node slot=.inr ((resetDonor hp N home group R key whole old src (home v)).symm ⟨i,t⟩).val := by
  let i : Fibre home (home v):=⟨v,rfl⟩
  let recs:=oldGather N home group R key old (home v)
  let shapes:=oldGatherShape N home group R key whole old src (home v)
  let localWidths:=boundaryWidth (M) (.inl (false,home v))
  let route:=fun (_ : Fibre home (home v)) (b : BitRef localWidths)=>(Sum.inl b : BitRef localWidths⊕BitRef noWidth)
  let functions:=fun _ : Fibre home (home v)=>({map:=id,read:=fun _ _=>rfl} : BlockMap p localWidths localWidths id).publicOnly
  let f:=oldBlockMap N home group R key whole v
  let rj:=Fin.cast (rerouteLen hp (src v) f u).symm j
  have prev:=reroute_operand hp (src v) f u j
  rw [was] at prev
  have held : ((shapes i).recipe hp).operand u rj=.inr t.val:=prev
  have carried:=wordTransfer_read hp recs noWidth route shapes (fun z => nomatch z) functions i u rj
  dsimp only at carried
  rw [held] at carried
  have len : ((inShape N home group R key whole old src (home v)).recipe hp).arity ⟨i,u⟩ =
      ((shapes i).recipe hp).arity u :=
    (congrArg List.length (combined_keys recs noWidth route shapes (fun z => nomatch z) functions i u)).trans
      (List.length_map («as» := (shapes i).keys u) (destination recs noWidth route functions i))
  exact ⟨⟨i,u⟩,Fin.cast len.symm rj,rfl,carried⟩

omit [Fintype Q] in
/-- A physically installed relay or batched bank has no private ports. -/
theorem relay_no_private (q : (relayShape N home group R key whole hp h).recipe hp |>.UsedWord) : False :=
  q.val.1.elim

omit [Fintype Q] in
theorem bank_no_private {bank : SiteBits (U:=Y) R} (device : ∀v,Shape p (bank v)) (u : R.Site)
    (empty : IsEmpty (bank u).Hidden) (q : ((bankPullbackShape N home group R key whole bank hp device u).recipe hp).UsedWord) :
    False := empty.false q.val.1

end
end
end Hierarchy.DescentBundleHistory

end OAI
