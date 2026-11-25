import OAI.Hierarchy.DescentCommonHost
import OAI.Hierarchy.DescentInstalledRotorLayers
import OAI.Hierarchy.DescentRotorPhysicalMaps
import OAI.Hierarchy.DescentSparseWordOrder
import Mathlib.Data.Nat.Pairing

namespace OAI
/-! # Explicit sparse labels of the actual reset wires -/

namespace Hierarchy.DescentResetWireTags
open DescentChosenRouter DescentContacts DescentRouterSlots DescentMixedRouter
open scoped Classical
noncomputable section

def digit {n : ℕ} : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
def side : Bool ↪ ℕ := finTwoEquiv.symm.toEmbedding.trans digit

def spaced {A B : Type*} (a : A↪ℕ) (b : B↪ℕ) : A×B↪ℕ :=
  (a.prodMap b).trans Nat.pairEquiv.toEmbedding

def tagged {A B : Type*} (a : A↪ℕ) (b : B↪ℕ) : (A⊕B)↪ℕ where
  toFun := Sum.elim (fun x=>2*a x) (fun x=>2*b x+1)
  inj' := by
    rintro (x|x) (y|y) eqn
    · exact congrArg Sum.inl (a.injective (by change 2*a x=2*a y at eqn;omega))
    · change 2*a x=2*b y+1 at eqn
      omega
    · change 2*b x+1=2*a y at eqn
      omega
    · exact congrArg Sum.inr (b.injective (by change 2*b x+1=2*b y+1 at eqn;omega))

def dependent {A : Type*} {X : A→Type*} (a : A↪ℕ) (part : ∀x,X x↪ℕ) : (Σ x,X x)↪ℕ where
  toFun p := Nat.pair (a p.1) (part p.1 p.2)
  inj' := by
    rintro ⟨x,i⟩ ⟨y,j⟩ eqn
    obtain ⟨same,bit⟩ := Nat.pair_eq_pair.mp eqn
    have xy : x = y := a.injective same
    subst y
    have ij : i = j := (part x).injective bit
    exact congrArg (Sigma.mk x) ij

def optionRow {n : ℕ} : Option (Fin n)↪ℕ where
  toFun := Option.elim' 0 (fun i=>i.val+1)
  inj' := by
    rintro (_|i) (_|j) eqn
    · rfl
    · change 0=j.val+1 at eqn
      omega
    · change i.val+1=0 at eqn
      omega
    · exact congrArg some (Fin.ext (Nat.succ.inj eqn))

variable {V H A I K : Type} [Fintype V] [DecidableEq V] [Fintype H] [Fintype A] [Fintype I] [Field K]
variable {k n h C₀ bits u : ℕ} (P : Placement V I H A k (2^n)) (vertex : V↪ℕ) (code : H↪V×Endpoint (2^n))

def baseTag : P.Good↪ℕ := (Function.Embedding.subtype _).trans (dependent vertex (fun _=>digit))
def termTag : H↪ℕ :=
  code.trans (spaced vertex (spaced Nat.pairEquiv.toEmbedding optionRow))

/-- The published output column on the false end identifies each reserved
cable. The two absolute terminal names identify every fallback cable. -/
def paidSlot : Reserve P.span↪(P.Good×Fin (2^n)) where
  toFun c := let q := slot P.b P.keys P.hub P.ends P.span P.room false c
             (q.1,P.columns false q.1 q.2)
  inj' := by
    intro c d eqn
    apply slot_unique P.b P.keys P.hub P.ends P.span P.room false
    let q := slot P.b P.keys P.hub P.ends P.span P.room false c
    let r := slot P.b P.keys P.hub P.ends P.span P.room false d
    change (q.1,P.columns false q.1 q.2)=(r.1,P.columns false r.1 r.2) at eqn
    have first := congrArg Prod.fst eqn
    have cols := congrArg Prod.snd eqn
    change P.columns false q.1 q.2=P.columns false r.1 r.2 at cols
    rw [←first] at cols
    exact Prod.ext first ((P.columns false q.1).injective cols)

def contactTag : P.Contact↪ℕ := tagged ((paidSlot P).trans (spaced (baseTag P vertex) digit))
  ((Function.Embedding.subtype _).trans (spaced (termTag vertex code) (termTag vertex code)))

def siteTag : P.Site↪ℕ := tagged (baseTag P vertex) (termTag vertex code)

def treeWire (t : ℕ) : (DescentCommonPalette.tree t).Edge↪ℕ :=
  dependent digit (fun d=>(DescentRotor.bitWord (d.val+1)).toEmbedding.trans digit)

variable (G : NonlinearExpanders.Graph n h)

/-- The two directed arc vertices, its multiplicity number, and the
coordinate of every local adjacency-path wire are all literal fields. -/
def rotorWire : (DescentCommonPalette.rotor G).Edge↪ℕ :=
  tagged (dependent (spaced digit digit) (fun _=>digit)) (dependent digit (fun _=>digit))

variable (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay) (D : ℕ)
local notation "sel" => selected P G hw pay hardware
local notation "Q" => network G hw u P.contact P.input P.site P.owner P.align sel D

def insideWire : (v : Bool×P.Site) → (device G hw u P.contact P.input P.site P.owner P.align (D:=D) (sel v.1 v.2)).Edge↪ℕ
  | (s, .inl g) =>
    (DescentCommonPalette.rotorEdgeEquiv G D
      (DescentChosenRouter.selectedRotorLayers P G hw pay hardware s g) C₀ bits u).symm.toEmbedding.trans
        (rotorWire G)
  | (s, .inr t) => treeWire (P.fallbackBook s t).height

def bankWire : (Q).Edge↪ℕ :=
  tagged (contactTag P vertex code) (dependent (spaced side (siteTag P vertex code)) (insideWire P G hw pay hardware D))

def assembled (input : I↪ℕ) : ((Bool×I) ⊕ (H ⊕ (Q).Edge))↪ℕ :=
  tagged (spaced side input) (tagged (termTag vertex code) (bankWire P vertex code G hw pay hardware D))

end
end Hierarchy.DescentResetWireTags

namespace Hierarchy.DescentResetWireTags
open DescentChosenRouter DescentContacts DescentCommonHost
open scoped Classical
noncomputable section
variable {V H : Type} {n h : ℕ} (vertex : V↪ℕ) (G : NonlinearExpanders.Graph n h)

def listTag : List Bool↪ℕ := by
  let read : List Bool ↪ (Σn,Fin n→Bool) := {
    toFun := fun x=>⟨x.length,x.get⟩
    inj' := by
      intro x y same
      simpa only [List.ofFn_get] using congrArg (fun p : Σn,Fin n→Bool=>List.ofFn p.2) same }
  exact read.trans (dependent (Function.Embedding.refl ℕ) (fun n=>(DescentRotor.bitWord n).toEmbedding.trans digit))

def hostTag : Node V (V×Endpoint (2^n)) (DescentCommonPalette.rotor G).Site ↪ ℕ := by
  let term := spaced vertex (spaced Nat.pairEquiv.toEmbedding (optionRow (n:=2^n)))
  let base := spaced vertex (Function.Embedding.refl ℕ)
  let rot : (DescentCommonPalette.rotor G).Site ↪ ℕ := dependent digit (fun _=>tagged side digit)
  let shape : Node V (V×Endpoint (2^n)) (DescentCommonPalette.rotor G).Site ↪
      (Bool×(V×Endpoint (2^n)))⊕((Bool×((V×ℕ)×(DescentCommonPalette.rotor G).Site))⊕(Bool×((V×Endpoint (2^n))×List Bool))) := {
    toFun := fun | .trunk s z=>.inl (s,z) | .good s b y=>.inr (.inl (s,b,y)) | .fall s z p=>.inr (.inr (s,z,p))
    inj' := by intro x y eqn; cases x <;> cases y <;> cases eqn <;> rfl }
  exact shape.trans (tagged (spaced side term) (tagged (spaced side (spaced base rot)) (spaced side (spaced term listTag))))

end
end Hierarchy.DescentResetWireTags

end OAI
