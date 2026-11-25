import OAI.Hierarchy.DescentPrivateAbsorption
import OAI.Hierarchy.DescentPrivateStageWidths
import OAI.Hierarchy.DescentPrivateVolume
import OAI.Hierarchy.DescentBundleReentry
import OAI.Hierarchy.DescentBundleSeed
import OAI.Hierarchy.DescentScheduledBitHistory

namespace OAI
/-! # Counting the private bits of the actual local recipes throughout a descent -/
namespace Hierarchy.DescentHistoryOrder
open Computability.BorderVNP.Crossing DescentKernelHistory DescentNetworkPartition DescentSixParty DescentHostDirectory GadgetNetwork
open scoped BigOperators Classical
noncomputable section
variable {F P V U : Type} [Field F] {d D : ℕ} {bits : P→ℕ}
variable (N : Network D P bits) [Fintype V] (loc : N.Site→V)

theorem absorbed_le : absorbed N loc≤∑e,N.width e := by
  rw [absorbed_eq_test]
  apply Finset.sum_le_sum
  intro e he
  split <;> omega

variable (pos : V→EuclideanSpace ℝ (Fin d)) (ball : ∀v,‖pos v‖≤1) (r : SiteBits (U:=U) N)

theorem quotient_mass :
    (∑v,privateWidth (quotient N loc pos ball) (quotientBits N loc pos ball r) v)=
      (∑v,privateWidth N r v)+absorbed N loc := by
  simp only [quotient_private_width,Finset.sum_add_distrib]
  rw [←Fintype.sum_sigma' (fun v (t : {i // loc i=v})=>privateWidth N r t.val)]
  have fibreSum : (∑ t : (Σ v, {i // loc i = v}), privateWidth N r t.2.val) =
      ∑ i, privateWidth N r i :=
    (Equiv.sigmaFiberEquiv loc).sum_comp (privateWidth N r)
  calc
    _ = absorbed N loc + (∑ i, privateWidth N r i) :=
      congrArg (absorbed N loc + ·) fibreSum
    _ = _ := Nat.add_comm _ _

variable {W : MarkedWorld F D P bits}

def sitePrivate (B : BitDescription W) (v : W.graph.Site) := privateWidth W.graph B.recipe v
def privateMass (B : BitDescription W) := ∑v,sitePrivate B v

theorem sitePrivate_le (B : BitDescription W) (v : W.graph.Site) : sitePrivate B v≤privateMass B :=
  Finset.single_le_sum (fun i _=>Nat.zero_le (sitePrivate B i)) (Finset.mem_univ v)

variable (B : BitDescription W)

theorem coalesced_site {H : Type} [DecidableEq H] (key : W.graph.Site→Key H) (hub : H→Bool) (k g : ℕ)
    (v : MarkedWorld.reclaimed W key hub k g) :
    let loc := MarkedWorld.address W key hub k g
    sitePrivate (B.coalesced key hub k g) v=(∑e : PrivateEdge W.graph loc v,W.graph.width e.val)+
      ∑u : {u //loc u=v},sitePrivate B u.val := by
  have hq := quotient_private_width W.graph B.recipe (MarkedWorld.address W key hub k g)
    (fun _ => (0 : EuclideanSpace ℝ (Fin D))) (fun _ => by simp) v
  refine Eq.trans ?_ (Eq.trans hq ?_)
  · first
    | rfl
  · apply congrArg₂ Nat.add <;>
      exact Finset.sum_congr (by ext x; simp only [Finset.mem_univ]) (fun _ _ => rfl)

theorem coalesced_mass {H : Type} [DecidableEq H] (key : W.graph.Site→Key H) (hub : H→Bool) (k g : ℕ) :
    privateMass (B.coalesced key hub k g)=privateMass B+absorbed W.graph (MarkedWorld.address W key hub k g) :=
  quotient_mass _ _ _ _ _

theorem pieces_site (m : W.graph.Edge→ℕ) (q : ℕ) (fit : ∀e∈W.core,W.graph.width e=m e*q) (v) :
    sitePrivate (B.pieces m q fit) v=sitePrivate B v := rfl

theorem granular_site (m : W.graph.Edge→ℕ) (q : ℕ) (fit : ∀e,W.graph.width e=m e*q) (v) :
    sitePrivate (BitDescription.granular W m q fit B) v=sitePrivate B v := rfl

theorem granular_mass (W : MarkedWorld F D P bits) (m : W.graph.Edge→ℕ) (q : ℕ)
    (fit : ∀e,W.graph.width e=m e*q) (B : BitDescription W) :
    privateMass (BitDescription.granular W m q fit B)=privateMass B := rfl

theorem named_site (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) (v) :
    sitePrivate (B.renamed s e) v=sitePrivate B (s.symm v) := rfl

theorem named_mass (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) :
    privateMass (B.renamed s e)=privateMass B := s.symm.sum_comp (sitePrivate B)

def mergeFee {W : MarkedWorld F D P bits} (n : Normalize W) : ℕ := by
  induction n with
  | done _ => exact 0
  | split _ _ _ _ _ fee => exact fee
  | named _ _ _ _ fee => exact fee
  | merge W H key hub k g _ fee =>
    exact absorbed W.graph (MarkedWorld.address (V := H) W key hub k g) + fee

def mergeWidths {W : MarkedWorld F D P bits} (n : Normalize W) : ℕ := by
  induction n with
  | done _ => exact 0
  | split _ _ _ _ _ total => exact total
  | named _ _ _ _ total => exact total
  | merge W _ _ _ _ _ _ total => exact (∑ e, W.graph.width e) + total

theorem mergeFee_le (n : Normalize W) : mergeFee n≤ mergeWidths n := by
  induction n with
  | done => exact le_refl _
  | named W s e rest ih => exact ih
  | split W q m fit rest ih => exact ih
  | merge W H key hub k g rest ih =>
    exact Nat.add_le_add (absorbed_le W.graph (MarkedWorld.address (V := H) W key hub k g)) ih

theorem follow_mass (n : Normalize W) (B : BitDescription W) :
    privateMass (BitDescription.follow n B)=privateMass B+mergeFee n := by
  induction n with
  | done => exact (Nat.add_zero _).symm
  | split W q m fit rest ih => exact ih (B.pieces m q fit)
  | named W s e rest ih =>
    exact (ih (B.renamed s e)).trans (congrArg (· + mergeFee rest) (named_mass B s e))
  | merge W H key hub k g rest ih =>
    calc
      _ = privateMass (B.coalesced key hub k g) + mergeFee rest := ih (B.coalesced key hub k g)
      _ = (privateMass B + absorbed W.graph (MarkedWorld.address W key hub k g)) + mergeFee rest :=
        congrArg (· + mergeFee rest) (coalesced_mass B key hub k g)
      _ = _ := Nat.add_assoc _ _ _

variable {I C : Type} [Fintype I] (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→C) (profile : I→Profile G.C)
local notation "phys" => physical W.graph pick (branchWidth G z profile)
local notation "whereAt" => newSite W.graph pick (bestLayout (branchWidth G z profile)) pack

def selectedFee := absorbed phys whereAt

private theorem physical_private (a : (phys).Site) :
    privateWidth phys (physicalBits G W.toWorld pick z room profile B.recipe) a =
      (Sum.elim (sitePrivate B) (fun _ : I × Fin 6 => 0)) a := by
  rcases a with u | ⟨i,j⟩
  · rfl
  · apply Finset.sum_eq_zero
    intro e _
    exact (show Empty from e).elim

theorem selected_site (v : Merged W.graph pick (bestLayout (branchWidth G z profile)) pack) :
    sitePrivate (B.selected G pick z hz fit room pack profile) v=
      (∑e : PrivateEdge phys whereAt v,(phys).width e.val)+
        ∑a : {a //whereAt a=v},(Sum.elim (sitePrivate B) (fun _=>0)) a.val := by
  let pos := fun _ : Merged W.graph pick (bestLayout (branchWidth G z profile)) pack =>
    (0 : EuclideanSpace ℝ (Fin D))
  have ball (u) : ‖pos u‖ ≤ 1 := by simp [pos]
  refine (quotient_private_width phys (physicalBits G W.toWorld pick z room profile B.recipe)
    whereAt pos ball v).trans ?_
  apply congrArg (fun n => (∑e : PrivateEdge phys whereAt v,(phys).width e.val) + n)
  exact Finset.sum_congr rfl fun a _ => physical_private B G pick z room profile a.val

theorem selected_mass : privateMass (B.selected G pick z hz fit room pack profile)=
    privateMass B+selectedFee (W:=W) G pick z pack profile := by
  let pos := fun _ : Merged W.graph pick (bestLayout (branchWidth G z profile)) pack =>
    (0 : EuclideanSpace ℝ (Fin D))
  have ball (u) : ‖pos u‖ ≤ 1 := by simp [pos]
  let old : (phys).Site → ℕ := Sum.elim (sitePrivate B) (fun _ => 0)
  have hs : (∑ a : (phys).Site, old a) = privateMass B := by
    change (∑ a : W.graph.Site ⊕ (I × Fin 6), (Sum.elim (sitePrivate B) (fun _ : I × Fin 6 => 0)) a) = _
    rw [Fintype.sum_sum_type (Sum.elim (sitePrivate B) (fun _ : I × Fin 6 => 0))];
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, Nat.add_zero, privateMass]
  refine (quotient_mass phys whereAt pos ball (physicalBits G W.toWorld pick z room profile B.recipe)).trans ?_
  apply congrArg (fun n => n + absorbed phys whereAt)
  exact (Finset.sum_congr rfl (fun a _ => physical_private B G pick z room profile a)).trans hs

private theorem selectedFee_le_widths :
    selectedFee (W:=W) G pick z pack profile ≤ ∑e, (phys).width e :=
  absorbed_le phys whereAt

variable {u ε : ℝ} {G : PoweredGadget F} (he : 0≤ε) (T : StageInput W G u ε)

def scanFee (v : (T.result he).Choice) :=
  let r:=BitDescription.scannedRows he T
  selectedFee (W:=W) G r.pick (fun _=>T.z) r.pack (r.profile v)

def scanWidths (v : (T.result he).Choice) :=
  let r:=BitDescription.scannedRows he T
  let N:=physical W.graph r.pick (branchWidth G (fun _=>T.z) (r.profile v))
  ∑e,N.width e

theorem scanFee_le (v : (T.result he).Choice) : scanFee he T v≤ scanWidths he T v := by
  let r := BitDescription.scannedRows he T
  exact selectedFee_le_widths (W := W) G r.pick (fun _=>T.z) r.pack (r.profile v)

theorem scanWidths_le (v : (T.result he).Choice) : scanWidths he T v≤W.tetherWidth+4*W.liveWidth :=
  let r:=BitDescription.scannedRows he T
  physical_width_le G W r.pick (fun _=>T.z) (r.profile v) r.picked r.fit

theorem scanned_mass (he : 0≤ε) (T : StageInput W G u ε) (B : BitDescription W) (v : (T.result he).Choice) :
    privateMass (BitDescription.scanned he T B v)=privateMass B+scanFee he T v := by
  have hm {X Y : MarkedWorld F D P bits} (h : X=Y) (A : BitDescription X) :
      privateMass (cast (congrArg BitDescription h) A)=privateMass A := by subst Y;rfl
  let r := BitDescription.scannedRows he T
  let A := B.selected G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit
    (fun _=>le_refl T.z) r.pack (r.profile v)
  exact (hm (r.state v).symm A).trans (selected_mass B G r.pick (fun _=>T.z) (fun _=>T.unitPos)
    r.fit (fun _=>le_refl T.z) r.pack (r.profile v))

section Trunk
open DescentResetAttachments DescentResetTrunks DescentNamedContact DescentRouterBank DescentChosenRouter
variable {H Q X Y : Type} [Fintype H] [Fintype Q] {L : ℕ}
variable (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)

/-- At a primary trunk site exactly the old labels in that home's fibre are present.
The relay has no private word. A bank site retains its own local labels. -/
def trunkPrivate : ((Bool×H)⊕R.Site)→ℕ
  | .inl (false,h)=>∑v : Fibre home h,privateWidth N old v.val
  | .inl (true,_)=>0
  | .inr v=>privateWidth R bank v

omit [Fintype Q] in
theorem trunk_site (v : (DescentResetTrunks.network N home group R).Site) :
    privateWidth _ (trunkBits N home group R key old bank) v=trunkPrivate N home group R old bank v := by
  rcases v with ⟨_|_,h⟩|v
  · let gathered := oldGather N home group R key old h
    let carried (p : Σ i : Fibre home h, (gathered i).Hidden) := (gathered p.1).hiddenWidth p.2
    change (∑ z, Sum.elim (Empty.elim : Empty → ℕ) carried z) =
      ∑ i : Fibre home h, privateWidth N old i.val
    rw [Fintype.sum_sum_type (Sum.elim (Empty.elim : Empty → ℕ) carried)]
    have noExtra : (∑ e : Empty, Sum.elim (Empty.elim : Empty → ℕ) carried (.inl e)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      exact e.elim
    rw [noExtra, Nat.zero_add]
    change (∑ p, carried p) = _
    rw [Fintype.sum_sigma carried]
    apply Finset.sum_congr rfl
    rintro ⟨v,rfl⟩ _
    rfl
  · change (∑ e : Empty, (Empty.elim e : ℕ)) = 0
    apply Finset.sum_eq_zero
    intro e _
    exact e.elim
  · rfl

omit [Fintype Q] in
theorem trunk_mass :
    (∑v,privateWidth _ (trunkBits N home group R key old bank) v)=
      (∑v,privateWidth N old v)+(∑v,privateWidth R bank v) := by
  simp_rw [trunk_site]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  change ((∑_ : H,(0:ℕ))+(∑h,∑u : Fibre home h,privateWidth N old u.val))+(∑v,privateWidth R bank v)=_
  simp only [Finset.sum_const_zero,Nat.zero_add]
  rw [←Fintype.sum_sigma' (fun h (u : Fibre home h)=>privateWidth N old u.val)]
  exact congrArg (fun x => x + ∑ v, privateWidth R bank v)
    ((Equiv.sigmaFiberEquiv home).sum_comp (privateWidth N old))

variable (place : W.graph.Site→H) (groupAt : Bool→W.graph.Edge→Q) (hub : H→Bool)
variable {w : W.graph.Edge→ℕ} (same : w=W.graph.width)
variable (board : Network d (Bool×Q) (publicWidth groupAt w)) (legacy sorted : board.Tables F)
variable (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board)
variable (valid : ReadsBits board scalar prog sorted)

/-- Real primary/relay/bank addresses, across the one transport of exterior cable widths. -/
def installedAddress (place : W.graph.Site → H) (groupAt : Bool → W.graph.Edge → Q)
    (hub : H → Bool) {w : W.graph.Edge → ℕ} (same : w = W.graph.width)
    (board : Network d (Bool × Q) (publicWidth groupAt w)) (legacy : board.Tables F) :
    ((install W place groupAt hub same board legacy).graph.Site)≃((Bool×H)⊕board.Site) := by
  subst w
  exact Equiv.refl _

omit [Fintype Q] in
theorem installed_site (v : (install W place groupAt hub same board legacy).graph.Site) :
    sitePrivate (B.installed place groupAt hub same board legacy sorted ids scalar prog valid) v=
      match (installedAddress (W := W) place groupAt hub same board legacy).toFun v with
      | .inl (false,h)=>∑u : Fibre place h,sitePrivate B u.val
      | .inl (true,_)=>0
      | .inr v=>privateWidth board prog v := by
  subst w
  have h := trunk_site W.graph place groupAt board ids B.recipe prog v
  rcases v with ⟨_|_,x⟩|x <;> exact h

omit [Fintype Q] in
theorem installed_mass :
    privateMass (B.installed place groupAt hub same board legacy sorted ids scalar prog valid)=
      privateMass B+∑v,privateWidth board prog v := by
  subst w
  exact trunk_mass W.graph place groupAt board ids B.recipe prog
end Trunk

open DescentRotor DescentChosenRouter DescentResetTrunks
variable {price fee : ℝ} {h C₀ Ht L : ℕ} (Zr : ResetInput W price fee h C₀ Ht) (Tt : Zr.Terminals)
variable (key : W.graph.Edge↪Fin L) (m p : ℕ) (hp : 0<p) (fit : Zr.unit=m*p)
variable (cfg : ∀π,Configures F Zr.graph.arcs C₀ Zr.width π)
local notation "dev" => Zr.laneRecipe key m p hp fit
local notation "flat" => funext fun e => Eq.symm (Zr.allWidths e)
local notation "scalar" => DescentLaneGates.scalar Zr.graph.arcs C₀ Zr.width p (rom Zr.graph.arcs C₀ Zr.width (fixedTable cfg))

theorem bank_site_zero (v : Zr.bank.Site) : privateWidth Zr.bank dev v=0 := by
  apply Finset.sum_eq_zero
  intro e _
  exact (show Empty from e).elim

theorem reset_mass : privateMass (B.batchedReset Zr Tt key m p hp fit cfg)=privateMass B := by
  have volume : (∑ v, privateWidth Zr.bank dev v) = 0 :=
    Finset.sum_eq_zero fun v _ => bank_site_zero Zr key m p hp fit v
  exact (installed_mass (W := W) (B := B) (place := Tt.home) (groupAt := Zr.placement.input)
    (hub := Tt.hub) (same := flat) (board := Zr.bank) (legacy := Zr.tables) (sorted := Zr.orderedBank key)
    (ids := key) («scalar» := scalar) (prog := dev) (valid := Zr.lane_valid key m p hp fit cfg)).trans
    ((congrArg (privateMass B + ·) volume).trans (Nat.add_zero _))

theorem reset_site (v : (Zr.orderedReentry Tt key).graph.Site) :
    sitePrivate (B.batchedReset Zr Tt key m p hp fit cfg) v=
      match (installedAddress (W := W) Tt.home Zr.placement.input Tt.hub flat Zr.bank Zr.tables).toFun v with
      | .inl (false,h)=>∑u : DescentNamedContact.Fibre Tt.home h,sitePrivate B u.val
      | _=>0 := by
  refine (installed_site (W := W) (B := B) (place := Tt.home) (groupAt := Zr.placement.input)
    (hub := Tt.hub) (same := flat) (board := Zr.bank) (legacy := Zr.tables) (sorted := Zr.orderedBank key)
    (ids := key) («scalar» := scalar) (prog := dev) (valid := Zr.lane_valid key m p hp fit cfg) v).trans ?_
  cases (installedAddress (W := W) Tt.home Zr.placement.input Tt.hub flat Zr.bank Zr.tables).toFun v with
  | inl t=>rcases t with ⟨_|_,x⟩ <;> rfl
  | inr x=>exact bank_site_zero Zr key m p hp fit x

open DescentInitialHost Catalyst
variable {k nP : ℕ} (X : Approximation F k nP) (count width : ℕ) (c : (initialGroup X count width).Choice)

theorem initial_site (v) : sitePrivate (BitDescription.initial X count width c) v=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact (DescentBundleHistory.initial_hidden X count width c v i).elim

theorem initial_mass : privateMass (BitDescription.initial X count width c)=0 := by
  simp [privateMass,initial_site]

end
end Hierarchy.DescentHistoryOrder

end OAI
