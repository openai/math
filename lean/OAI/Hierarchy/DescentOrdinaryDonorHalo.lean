import OAI.Hierarchy.DescentDonorSiteOrder
import OAI.Hierarchy.DescentOldHostBall
import OAI.Hierarchy.DescentCableDonorNames
import OAI.Hierarchy.DescentColoredHost
import OAI.Hierarchy.DescentStageEdgeReceipt
import OAI.Hierarchy.DescentHubDirectory

namespace OAI
/-! # Bounded real donors of ordinary normalized cable children -/
namespace Hierarchy.DescentOrdinaryDonorHalo
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.StarKeys DescentSixParty.MarkedWorld
open DescentHostDirectory DescentColonies DescentPacking DescentStageEdgeReceipt DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [DecidableEq V]

theorem projected {near : V→Finset V} {D slots : ℕ} (t : ℕ) {x y : Key V}
    (inside : y∈directory near D slots t x) : y.1∈around near t x.1 := by
  induction t generalizing y with
  | zero=>simpa [directory,around] using congrArg Prod.fst (Finset.mem_singleton.mp inside)
  | succ t ih=>
    obtain ⟨p,old,hop⟩:=Finset.mem_biUnion.mp inside
    exact Finset.mem_biUnion.mpr ⟨p.1,ih old,(Finset.mem_product.mp hop).1⟩

theorem around_room (near : V→Finset V) (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (t : ℕ) (v:V) :
    (around near t v).card≤(Δ+1)^t := by
  induction t with
  | zero=>simp [around]
  | succ t ih=>
    calc
      _ ≤ ∑p∈around near t v,(insert p (near p)).card:=Finset.card_biUnion_le
      _ ≤ ∑_p∈around near t v,(Δ+1):=Finset.sum_le_sum fun p _=>(Finset.card_insert_le p _).trans (Nat.add_le_add_right (degree p) 1)
      _ ≤ _:=by simpa [pow_succ] using Nat.mul_le_mul_right (Δ+1) ih

theorem siteSet_room {U : Type} [Fintype U] {k : ℕ} (near : V→Finset V) (pos : U→V) (block : U→Block k)
    (single : Function.Injective (fun u=>(pos u,block u))) (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (key : Key V) :
    (siteSet near pos key).card≤(Δ+1)^4*2^k := by
  let f : ↥(siteSet near pos key)→ ↥(around near 4 key.1)×Block k :=
    fun u=>(⟨pos u.val,(Finset.mem_filter.mp u.property).2⟩,block u.val)
  have inj : Function.Injective f := by
    intro a b h
    have positions : pos a.val = pos b.val :=
      congrArg (fun x : ↥(around near 4 key.1) × Block k => x.1.val) h
    have blocks : block a.val = block b.val :=
      congrArg (fun x : ↥(around near 4 key.1) × Block k => x.2) h
    exact Subtype.ext (single (Prod.ext positions blocks))
  have count:=Fintype.card_le_of_injective f inj
  have upper : (siteSet near pos key).card≤(around near 4 key.1).card*2^k := by simpa using count
  exact upper.trans (Nat.mul_le_mul_right _ (around_room near Δ degree 4 key.1))

def halo {U : Type} [Fintype U] {k : ℕ} (near : V→Finset V) (pos : U→V) (block : U→Block k)
    (single : Function.Injective (fun u=>(pos u,block u))) (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (rank : U↪ℕ) :
    Halo (Key V) U ((Δ+1)^4*2^k) := Halo.fromRank (siteSet near pos) rank (siteSet_room near pos block single Δ degree)

/-- An executable padded layout has no dependency on whether an old site was
occupied. Each full incoming raster is addressed by its old relative rack
and a block digit; missing sites retain their unused locations. -/
def raster {U : Type} [Fintype U] {k : ℕ} (near : V→Finset V) (pos : U→V) (block : U→Block k)
    (single : Function.Injective (fun u=>(pos u,block u))) (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (rank : V↪ℕ) :
    Halo (Key V) U ((Δ+1)^4*2^k) where
  member:=siteSet near pos
  slot s:=
    let hosts:=Halo.fromRank (around near 4) rank (around_room near Δ degree 4)
    { toFun:=fun u=>finProdFinEquiv (hosts.slot s.1 ⟨pos u.val,(Finset.mem_filter.mp u.property).2⟩,block u.val)
      inj':=by
        intro u v eqn
        have pair:=finProdFinEquiv.injective eqn
        have positions : pos u.val = pos v.val :=
          congrArg Subtype.val ((hosts.slot s.1).injective (congrArg Prod.fst pair))
        have blocks : block u.val = block v.val :=
          congrArg (fun x : Fin ((Δ+1)^4) × Block k => x.2) pair
        exact Subtype.ext (single (Prod.ext positions blocks)) }

theorem raster_val {U : Type} [Fintype U] {k : ℕ} (near : V→Finset V) (pos : U→V) (block : U→Block k)
    (single : Function.Injective (fun u=>(pos u,block u))) (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (rank : V↪ℕ)
    (s : Key V) (u : ↥(siteSet near pos s)) :
    let rack:=(Halo.fromRank (around near 4) rank (around_room near Δ degree 4)).slot s.1
      ⟨pos u.val,(Finset.mem_filter.mp u.property).2⟩
    ((raster near pos block single Δ degree rank).slot s u).val=rack.val*2^k+(block u.val).val := by
  let hosts:=Halo.fromRank (around near 4) rank (around_room near Δ degree 4)
  let rack:=hosts.slot s.1 ⟨pos u.val,(Finset.mem_filter.mp u.property).2⟩
  change (block u.val).val + 2^k*rack.val = rack.val*2^k+(block u.val).val
  rw [Nat.mul_comm (2^k) rack.val, Nat.add_comm]

theorem raster_lt {U : Type} [Fintype U] {k : ℕ} (near : V→Finset V) (pos : U→V) (block : U→Block k)
    (single : Function.Injective (fun u=>(pos u,block u))) (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (rank : V↪ℕ)
    (s : Key V) (u v : ↥(siteSet near pos s)) :
    (raster near pos block single Δ degree rank).slot s u<(raster near pos block single Δ degree rank).slot s v ↔
      rank (pos u.val)*2^k+(block u.val).val<rank (pos v.val)*2^k+(block v.val).val := by
  let hosts:=Halo.fromRank (around near 4) rank (around_room near Δ degree 4)
  let x : ↥(hosts.member s.1):=⟨pos u.val,(Finset.mem_filter.mp u.property).2⟩
  let y : ↥(hosts.member s.1):=⟨pos v.val,(Finset.mem_filter.mp v.property).2⟩
  simp only [Fin.lt_def,raster_val,lex (block u.val).isLt (block v.val).isLt]
  have comp : hosts.slot s.1 x<hosts.slot s.1 y ↔ rank (pos u.val)<rank (pos v.val):=Halo.slot_lt ..
  have eqn : (hosts.slot s.1 x).val=(hosts.slot s.1 y).val ↔ rank (pos u.val)=rank (pos v.val) := by
    constructor
    · intro same
      have points : x=y := (hosts.slot s.1).injective (Fin.ext same)
      exact congrArg (fun t : ↥(hosts.member s.1) => rank t.val) points
    · intro same
      have points : x=y := Subtype.ext (rank.injective same)
      exact congrArg (fun t : ↥(hosts.member s.1) => ((hosts.slot s.1) t).val) points
  exact or_congr comp (and_congr_left' eqn)

section Native
variable {n k markCap : ℕ} {P : Type*} {bits : P→ℕ} (N : Network n P bits) (core : Finset N.Edge)
variable {C : Type} [Fintype C] [DecidableEq C] (home : N.Site→C) (color : N.Site→Bool) (B : ℕ)
variable (col : C↪V×(ℕ×ℕ)) (near : V→Finset V) (D a : ℕ) (load : V→Block k→ℕ)
variable (markLimit : ∀v x,load v x≤ markCap) (position : N.Site→V) (block : N.Site→Block k)
variable (A : ℕ) (positive : 0<B) (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
variable (realized : ∀u,col (home u)=colonyCode N markCap near D a load markLimit position block u)
variable (same : ∀e,block (N.src e)=block (N.dst e))
variable (adj : ∀e,position (N.dst e)∈near (position (N.src e)) ∧ position (N.src e)∈near (position (N.dst e)))
variable (colors : ∀e∈core,color (N.src e)=color (N.dst e)) (layout : Bool)
local notation "pk" => colorPick N core home color B
local notation "pack" => coloredPack N core home color B
local notation "addr" => nativeKey N core home color B col colors layout

include D a load markLimit block A positive cap realized same adj

/-- Actual source before and after hub contraction has the original source
of the identifying old cable in its measured roster, for all eleven roles. -/
theorem native_member (hub : V→Bool) (g : ℕ) (e : GadgetNetwork.Edge (I:=NativePair N core home color B) N) :
    N.src (DescentCableDonorNames.anchor pk e)∈siteSet near position
      (mergeHub hub k g (addr (GadgetNetwork.newSite N pk layout pack (GadgetNetwork.source N e)))) := by
  let u:=N.src (donorEdge N pk e)
  have old:=native_donor N core home color B col near D a load markLimit position block A positive cap realized same adj colors layout e
  have reachable:=projected 4 old
  have rank := congrArg Prod.fst ((packed_home N core home color B col u).trans (realized u))
  change (packAddress N core home color B col (pack u)).1=position u at rank
  have sameDonor : DescentCableDonorNames.anchor pk e=donorEdge N pk e := by rcases e with t|t|t <;> rfl
  rw [sameDonor]
  apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,?_⟩
  let p:=addr (GadgetNetwork.newSite N pk layout pack (GadgetNetwork.source N e))
  have site : (mergeHub hub k g p).1=p.1 := by cases flag : hub p.1 <;> simp [mergeHub,flag]
  change position u∈around near 4 (mergeHub hub k g p).1
  rw [site, ← rank]
  exact reachable
theorem native_old_member (hub : V→Bool) (g : ℕ) (u : N.Site) :
    u∈siteSet near position
      (mergeHub hub k g (addr (GadgetNetwork.newSite N pk layout pack (.inl u)))) := by
  have old:=native_old_donor N core home color B col near D a load markLimit position block A positive cap realized same adj colors layout u
  have reachable:=projected 4 old
  have rank := congrArg Prod.fst ((packed_home N core home color B col u).trans (realized u))
  change (packAddress N core home color B col (pack u)).1=position u at rank
  apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,?_⟩
  let p:=addr (GadgetNetwork.newSite N pk layout pack (.inl u))
  have site : (mergeHub hub k g p).1=p.1 := by cases flag : hub p.1 <;> simp [mergeHub,flag]
  change position u∈around near 4 (mergeHub hub k g p).1
  rw [site, ← rank]
  exact reachable
theorem native_born_member (hub : V→Bool) (g : ℕ) (i : NativePair N core home color B) (j : Fin 6) :
    N.src (pk (i,0))∈siteSet near position
      (mergeHub hub k g (addr (GadgetNetwork.newSite N pk layout pack (.inr (i,j))))) := by
  let u:=N.src (pk (i,0))
  have old:=native_born_donor N core home color B col near D a load markLimit position block A positive cap realized same adj colors layout i j
  have reachable:=projected 4 old
  have rank := congrArg Prod.fst ((packed_home N core home color B col u).trans (realized u))
  change (packAddress N core home color B col (pack u)).1=position u at rank
  apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,?_⟩
  let p:=addr (GadgetNetwork.newSite N pk layout pack (.inr (i,j)))
  have site : (mergeHub hub k g p).1=p.1 := by cases flag : hub p.1 <;> simp [mergeHub,flag]
  change position u∈around near 4 (mergeHub hub k g p).1
  rw [site, ← rank]
  exact reachable
end Native

section Children
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
set_option quotPrecheck false
local notation "world" => (subroundNormalize W G pick z hz fit pack p key flag k g q old picked affected).result
local notation "tape" => ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected

/-- Concrete ordinary origin and child offset used by `parent_injective`.
The two subtype restrictions only remove cables. Neither changes the raw
constructor nor associates a different parent's numerical offset. -/
theorem actual_children (u v : (world).graph.Edge)
    (raw : ((tape).owner u).val.val=((tape).owner v).val.val) (child : (tape).offset u=(tape).offset v) : u=v := by
  have same : (tape).owner u=(tape).owner v:=Subtype.ext (Subtype.ext raw)
  apply (tape).order.injective
  apply Fin.ext
  rw [(tape).read, (tape).read, same, child]
end Children

end
end Hierarchy.DescentOrdinaryDonorHalo

end OAI
