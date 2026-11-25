import OAI.Hierarchy.DescentInstalledPrivateDonors
import OAI.Hierarchy.DescentBatchedNodeOrder
import OAI.Hierarchy.DescentRosterOrder

namespace OAI
/-! # Bounded node order and role fields at each physically installed reset site -/
namespace Hierarchy.DescentResetLocalNodes
open DescentKernelHistory DescentNamedContact DescentResetTrunks DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {I : Type} [Fintype I] (J : I→Type) [∀i,Fintype (J i)] (donor : I↪ℕ) (prior : ∀i,J i↪ℕ)

/-- Bounded actual rank by counting earlier keys, including a sparse predecessor order. -/
def ordinal {E : Type} [Fintype E] (key : E↪ℕ) : E ≃ Fin (Fintype.card E) :=
  Equiv.ofBijective (DescentRosterOrder.compact key)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨(DescentRosterOrder.compact key).injective,by simp⟩)

def oldOrder : (Σi,J i) ≃ Fin (Fintype.card (Σi,J i)) :=
  (Equiv.sigmaCongrRight (fun i=>ordinal (prior i))).trans
    ((ProtocolRAMPortRanks.enumerate (fun i=>Fintype.card (J i)) donor donor.injective).trans
      (finCongr (by simp [Fintype.card_sigma])))

theorem oldOrder_val (i : I) (u : J i) :
    (oldOrder J donor prior ⟨i,u⟩).val =
      (∑j ∈ Finset.univ.filter (fun j=>donor j<donor i),Fintype.card (J j))+
        (Finset.univ.filter (fun x=>prior i x<prior i u)).card := by
  change _+(DescentRosterOrder.compact (prior i) u).val=_
  rw [DescentRosterOrder.compact_read]
  rfl

variable {n d L : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (board : Network d (Bool×Q) (publicWidth group N.width)) (ids : N.Edge↪Fin L)
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) board)
variable (donors : ∀h,Fibre home h↪ℕ) (oldIds : ∀v,(old v).Node↪ℕ)
variable (bankIds : ∀v,(bank v).Node ≃ Fin (Fintype.card (bank v).Node))
local notation "post" => trunkBits N home group board ids old bank

def gathered (h : H) (i : Fibre home h) : (oldGather N home group board ids old h i).Node ≃ (old i.val).Node := by
  rcases i with ⟨v,rfl⟩
  exact Equiv.refl _

def donorNodes (h : H) : (post (.inl (false,h))).Node ≃ (Σi : Fibre home h,(old i.val).Node) :=
  Equiv.sigmaCongrRight (gathered N home group board ids old h)

def relayKey (h : H) : Fibre (moved N home) h↪ℕ :=
  ((Function.Embedding.subtype _).trans ids).trans Fin.valEmbedding

/-- All three constructors have a dense order inside the single output site. -/
def localOrder : ∀v,(post v).Node ≃ Fin (Fintype.card (post v).Node)
  | .inl (false,h)=>
    let e:=donorNodes N home group board ids old bank h
    e.trans ((oldOrder (fun i : Fibre home h=>(old i.val).Node) (donors h) (fun i=>oldIds i.val)).trans
      (finCongr (Fintype.card_congr e).symm))
  | .inl (true,h)=>ordinal (relayKey N home ids h)
  | .inr v=>bankIds v

omit [Fintype Q] in
theorem old_number (h : H) (i : Fibre home h) (z : (old i.val).Node) :
    (localOrder N home group board ids old bank donors oldIds bankIds (.inl (false,h))
      ((donorNodes N home group board ids old bank h).symm ⟨i,z⟩)).val =
      (∑j ∈ Finset.univ.filter (fun j=>donors h j<donors h i),Fintype.card (old j.val).Node)+
        (Finset.univ.filter (fun x=>oldIds i.val x<oldIds i.val z)).card :=
  by
    let eqv:=donorNodes N home group board ids old bank h
    change (oldOrder (fun j : Fibre home h=>(old j.val).Node) (donors h) (fun j=>oldIds j.val)
      (eqv (eqv.symm ⟨i,z⟩))).val=_
    rw [Equiv.apply_symm_apply]
    exact oldOrder_val (fun j : Fibre home h=>(old j.val).Node) (donors h) (fun j=>oldIds j.val) i z

omit [Fintype Q] in
theorem relay_number (h : H) (e : Fibre (moved N home) h) :
    (localOrder N home group board ids old bank donors oldIds bankIds (.inl (true,h)) e).val =
      (Finset.univ.filter (fun j : Fibre (moved N home) h=>ids j.val < ids e.val)).card :=
  DescentRosterOrder.compact_read _ _

omit [Fintype Q] in
theorem bank_number (v : board.Site) (i : (bank v).Node) :
    localOrder N home group board ids old bank donors oldIds bankIds (.inr v) i=bankIds v i := rfl

structure Header (Tag : Type) where
  tag : Tag
  arity : ℕ
  width : Fin arity→ℕ

def header {Tag A : Type} {w : A→ℕ} (q : BitRecipe Tag A w) (n : q.Node) : Header Tag :=
  ⟨q.tag n,q.arity n,q.size n⟩

def Header.map {S T : Type} (f : S→T) (h : Header S) : Header T :=
  ⟨f h.tag,h.arity,h.width⟩

/-- The common role, arity and operand lengths in actual tape order. -/
def shelf (v : (DescentResetTrunks.network N home group board).Site) :=
  List.ofFn (fun j=>header (post v) ((localOrder N home group board ids old bank donors oldIds bankIds v).symm j))

omit [Fintype Q] in
theorem shelf_read (v : (DescentResetTrunks.network N home group board).Site) (i : (post v).Node) :
    (shelf N home group board ids old bank donors oldIds bankIds v)[
      (localOrder N home group board ids old bank donors oldIds bankIds v i).val]?=some (header (post v) i) := by
  have h := (localOrder N home group board ids old bank donors oldIds bankIds v i).isLt
  rw [List.getElem?_eq_getElem (by simp [shelf])]
  simp [shelf]

omit [Fintype Q] in
theorem retained_header (h : H) (i : Fibre home h) (z : (old i.val).Node) :
    header (post (.inl (false,h))) ((donorNodes N home group board ids old bank h).symm ⟨i,z⟩)=
      (header (old i.val) z).map Sum.inl := by rcases i with ⟨v,rfl⟩;rfl

omit [Fintype Q] in
theorem relay_header (h : H) (e : Fibre (moved N home) h) :
    header (post (.inl (true,h))) e=⟨.inr (.inl ()),2,fun _=>N.width e.val⟩ := rfl

omit [Fintype Q] in
theorem bank_header (v : board.Site) (i : (bank v).Node) :
    header (post (.inr v)) i=(header (bank v) i).map (Sum.inr ∘ Sum.inr) := rfl

open DescentSixParty
variable {F : Type} [Field F] {W : MarkedWorld F n P bits} (B : BitDescription W)
variable (atHome : W.graph.Site→H) (atPort : Bool→W.graph.Edge→Q) (hub : H→Bool)
variable {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (R : Network d (Bool×Q) (publicWidth atPort w))
variable (legacy sorted : R.Tables F) (key : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
variable (prog : SiteBits (U:=Y) R) (valid : ReadsBits R scalar prog sorted)
local notation "postBits" => B.installed atHome atPort hub same R legacy sorted key scalar prog valid

def installedOrder (who : ∀h,Fibre atHome h↪ℕ) (previous : ∀v,(B.recipe v).Node↪ℕ)
    (fresh : ∀v,(prog v).Node ≃ Fin (Fintype.card (prog v).Node)) :
    ∀v,((postBits).recipe v).Node ≃ Fin (Fintype.card ((postBits).recipe v).Node) := by
  subst w
  exact localOrder W.graph atHome atPort R key B.recipe prog who previous fresh

end
end Hierarchy.DescentResetLocalNodes

namespace Hierarchy.DescentSixParty.ResetInput
open DescentKernelHistory DescentResetLocalNodes DescentNamedContact DescentRotor
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {n : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} {price ε : ℝ} {h C Ht L : ℕ}
variable (B : BitDescription W) (Z : ResetInput W price ε h C Ht) (T : Terminals Z)
variable (key : W.graph.Edge↪Fin L) (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p) (menu : ∀π,Configures F Z.graph.arcs C Z.width π)
local notation "post" => B.batchedReset Z T key m p hp fit menu

def resetLocalOrder (who : ∀t,Fibre T.home t↪ℕ) (previous : ∀v,(B.recipe v).Node↪ℕ) :
    ∀v,((post).recipe v).Node ≃ Fin (Fintype.card ((post).recipe v).Node) :=
  installedOrder B T.home Z.placement.input T.hub (funext fun e=>(Z.allWidths e).symm) Z.bank Z.tables
    (Z.orderedBank key) key _ _ (Z.lane_valid key m p hp fit menu) who previous (Z.laneNodeOrder key m p hp fit)

/-- Compact the genuine previously issued physical site numbers inside this one old home fibre. -/
def homeTicket {V : ℕ} (vertex : W.graph.Site↪Fin V) (t : Z.Fallback) :
    Fibre T.home t↪Fin (Fintype.card (Fibre T.home t)) :=
  DescentRosterOrder.compact (((Function.Embedding.subtype _).trans vertex).trans Fin.valEmbedding)

theorem homeTicket_read {V : ℕ} (vertex : W.graph.Site↪Fin V) (t : Z.Fallback) (i : Fibre T.home t) :
    (Z.homeTicket T vertex t i).val=(Finset.univ.filter (fun j : Fibre T.home t=>vertex j.val<vertex i.val)).card :=
  DescentRosterOrder.compact_read _ _

def physicalLocalOrder {V : ℕ} (vertex : W.graph.Site↪Fin V) (previous : ∀v,(B.recipe v).Node↪ℕ) :
    ∀v,((post).recipe v).Node ≃ Fin (Fintype.card ((post).recipe v).Node) :=
  Z.resetLocalOrder B T key m p hp fit menu (fun t=>(Z.homeTicket T vertex t).trans Fin.valEmbedding) previous

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
