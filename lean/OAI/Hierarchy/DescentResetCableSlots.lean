import OAI.Hierarchy.DescentDenseHostOrder
import OAI.Hierarchy.DescentContactDegree
import OAI.Hierarchy.DescentOrderedResetRows
import OAI.Hierarchy.DescentInstalledRotorLayers
import OAI.Hierarchy.DescentRotorPhysicalMaps

namespace OAI
/-! # Linear-size sparse slot allocation for every literal reset cable

A fallback contact uses the left terminal and its physically issued leaf
code. A paid contact uses its actual left reserved socket. The two old
endpoint stems retain their parent grain number.
-/

namespace Hierarchy.DescentResetCableSlots
open DescentRouterSlots DescentChosenRouter DescentContacts DescentCommonHost DescentHostDirectory
open DescentResetWireTags DescentMixedRouter
open scoped Classical BigOperators
noncomputable section

def prod {A B : Type*} {m n : ℕ} (a : A↪Fin m) (b : B↪Fin n) : A×B↪Fin (m*n) :=
  (a.prodMap b).trans finProdFinEquiv.toEmbedding

def sum {A B : Type*} {m n : ℕ} (a : A↪Fin m) (b : B↪Fin n) : (A⊕B)↪Fin (m+n) :=
  (a.sumMap b).trans finSumFinEquiv.toEmbedding

def dep {A : Type*} {B : A→Type*} {m n : ℕ} (a : A↪Fin m) (b : ∀i,B i↪Fin n) :
    (Σi,B i)↪Fin (m*n) :=
  (show (Σi,B i)↪Fin m×Fin n from {
    toFun:=fun x=>(a x.1,b x.1 x.2)
    inj':=by
      rintro ⟨i,x⟩ ⟨j,y⟩ same
      obtain rfl:=a.injective (congrArg Prod.fst same)
      exact congrArg (Sigma.mk i) ((b i).injective (congrArg Prod.snd same)) }).trans finProdFinEquiv.toEmbedding

def optional {Y : ℕ} : Option (Fin Y)↪Fin (Y+1) where
  toFun z:=⟨optionRow z,by cases z with
                           | none=>exact Nat.zero_lt_succ _
                           | some i=>exact Nat.succ_lt_succ i.isLt⟩
  inj':=fun _ _ h=>optionRow.injective (congrArg Fin.val h)

def interval (k : ℕ) : ↥(codes k)↪Fin (2^(k+1)) :=
  (DescentRosterOrder.compact ((Function.Embedding.subtype _).trans Nat.pairEquiv.toEmbedding)).trans
    (Fin.castLEEmb (by rw [Fintype.card_coe];have := codes_card k;omega))

variable {V F A I H : Type} [Fintype V] [DecidableEq V] [Fintype F] [Fintype A] [Fintype I] [Field H]
variable {k n h C₀ bits u U one : ℕ} (P : Placement V I F A k (2^n)) (vertex : V↪Fin U)
variable (code : F↪V×Endpoint (2^n))
variable (valid : ∀f,(code f).2.1.1≤k ∧ (code f).2.1.2<2^(code f).2.1.1)
local notation "Y" => (2^n:ℕ)
local notation "bs" => (U*2^k)
local notation "ts" => (U*(2^(k+1)*(Y+1)))

def base : P.Good↪Fin bs where
  toFun g := finProdFinEquiv (vertex g.val.1,Fin.castLE (Nat.pow_le_pow_right (by decide) (P.depth _)) g.val.2)
  inj' := by
    rintro ⟨⟨a,i⟩,ha⟩ ⟨⟨b,j⟩,hb⟩ eqn
    have pair:=finProdFinEquiv.injective eqn
    obtain rfl:=vertex.injective (congrArg Prod.fst pair)
    exact Subtype.ext (congrArg (Sigma.mk a) (Fin.ext (congrArg (fun z=>z.2.val) pair)))

def terminal : F↪Fin ts :=
  (show F↪V×(↥(codes k)×Option (Fin Y)) from {
    toFun:=fun f=>((code f).1,⟨(code f).2.1,mem_codes (valid f).1 (valid f).2⟩,(code f).2.2)
    inj':=fun _f _g eqn=>code.injective (congrArg (fun z=>(z.1,z.2.1.val,z.2.2)) eqn) }).trans
  (prod vertex (prod (interval k) optional))

variable (Ht : ℕ) (depth : ∀s t,(P.fallbackBook s t).height≤Ht)
local notation "term" => terminal vertex code valid

def leftSocket : P.Contact↪(Reserve P.span ⊕ Σ t:F,LinkId P.owner false (.inr t)) where
  toFun
    | .inl c=>.inl c
    | .inr c=>.inr ⟨c.val.1,⟨.inr c,rfl⟩⟩
  inj':=by
    let read : (Reserve P.span ⊕ Σ t:F,LinkId P.owner false (.inr t))→P.Contact :=
      Sum.elim Sum.inl (fun z=>z.2.val)
    intro a b eqn
    have back:=congrArg read eqn
    cases a <;> cases b <;> exact back

def leaf (s : Bool) (t : F) : LinkId P.owner s (.inr t)↪Fin (2^Ht) :=
  (P.fallbackBook s t).codes.trans
    ((DescentRotor.bitWord _).toEmbedding.trans (Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (depth s t))))

def contact : P.Contact↪Fin (bs*Y+ts*2^Ht) :=
  (leftSocket P).trans (sum ((paidSlot P).trans (prod (base P vertex) (Function.Embedding.refl _)))
    (dep term (leaf P Ht depth false)))

variable (G : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor G
local notation "tCap" => (2^(Ht+1))
local notation "cCap" => max (Fintype.card (Computability.BorderVNP.Crossing.Network.Edge Q)) tCap

def rotor : (Q).Edge↪Fin cCap :=
  (DescentRosterOrder.compact (rotorWire G)).trans (Fin.castLEEmb (le_max_left _ _))

def tree (s : Bool) (t : F) : (DescentCommonPalette.tree (P.fallbackBook s t).height).Edge↪Fin cCap :=
  (DescentRosterOrder.compact (treeWire _)).trans (Fin.castLEEmb (by
    have sz : Fintype.card (DescentCommonPalette.tree (P.fallbackBook s t).height).Edge + 2 =
        2^((P.fallbackBook s t).height+1) :=
      DescentContactTree.Physical.edges (h:=(P.fallbackBook s t).height) (D:=0)
        (fun (_ : Unit) (_ : ℕ)=>false) (fun _=>0)
    have inc:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.succ_le_succ (depth s t))
    exact ((Nat.le_add_right _ 2).trans (sz.le.trans inc)).trans (le_max_right _ _)))

variable (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=H) (C₀:=C₀) (u:=u) P G hw pay) (D : ℕ)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => network G hw u P.contact P.input P.site P.owner P.align sel D
local notation "kernelSlots" => ((2*(bs+ts))*cCap)
local notation "contactSlots" => (bs*Y+ts*2^Ht)

def privateWire : (v : Bool×P.Site)→(device G hw u P.contact P.input P.site P.owner P.align (D:=D) (sel v.1 v.2)).Edge↪Fin cCap
  | (s,.inl g) =>
    let layers := DescentChosenRouter.selectedRotorLayers P G hw pay hardware s g
    (DescentCommonPalette.rotorEdgeEquiv G D layers C₀ bits u).symm.toEmbedding.trans (rotor Ht G)
  | (s,.inr t) => tree P Ht depth G s t

def bankCable : (bank).Edge↪Fin (contactSlots+kernelSlots) :=
  sum (contact P vertex code valid Ht depth) (dep
    (prod finTwoEquiv.symm.toEmbedding (sum (base P vertex) term))
    (privateWire P Ht depth G hw pay hardware D))

def complete (old : I↪Fin one) : ((Bool×I) ⊕ (F ⊕ (bank).Edge))↪Fin (2*one+(ts+(contactSlots+kernelSlots))) :=
  sum (prod finTwoEquiv.symm.toEmbedding old)
    (sum term (bankCable P vertex code valid Ht depth G hw pay hardware D))

end
end Hierarchy.DescentResetCableSlots

end OAI
