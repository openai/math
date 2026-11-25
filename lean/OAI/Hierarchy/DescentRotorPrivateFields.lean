import OAI.Hierarchy.DescentResetCableSlots
import OAI.Hierarchy.DescentWordProduct

namespace OAI
/-! # Fixed rotor cable headers and native installed-width instructions -/

namespace Hierarchy.DescentRotorPrivateFields
open DescentPhysicalSplit DescentRotor.Physical DescentResetWireTags DescentChosenRouter DescentMixedRouter
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open private DescentRotor.Physical.local_legs from OAI.Hierarchy.DescentTrivalentRotor
open private DescentRotor.regular_ports from OAI.Hierarchy.DescentRotorHost
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor G
local notation "bare" => host G.arcs 0 0 0 0 0

/-- A private arc carries C payloads; a path step carries the whole tuple of its host. -/
def legPrice (C b : ℕ) : Leg (bare)→ℕ
  | .inl _=>b
  | .inr _=>C*b

def price (C b : ℕ) : (Q).Edge→ℕ
  | .inl _=>C*b
  | .inr ⟨v,_⟩=>∑j,legPrice G C b (name (bare) v j)

private theorem spine_price_slots (C b : ℕ) (v : Fin (2^n)) (i : Fin (count (bare) v+1)) :
    price G C b (.inr ⟨v,i⟩)=∑s,DescentRotor.SlotWidth G.arcs C b v s := by
  let slots:=((index (bare) v).symm.trans (rowFibre (D:=0) (R:=0) (C:=0) (w:=0) (u:=0) G v))
  calc
    price G C b (.inr ⟨v,i⟩)=∑j,DescentRotor.SlotWidth G.arcs C b v (slots j) := by
      apply Finset.sum_congr rfl
      intro j _
      change legPrice G C b (((index (bare) v).symm j).val)=DescentRotor.SlotWidth G.arcs C b v
        (rowFibre (D:=0) (R:=0) (C:=0) (w:=0) (u:=0) G v ((index (bare) v).symm j))
      generalize (index (bare) v).symm j=t
      rcases t with ⟨x|x,hit⟩ <;> rfl
    _ = ∑s,DescentRotor.SlotWidth G.arcs C b v s := slots.sum_comp _

private theorem sum_scaled_prices {S : Type*} [Fintype S] (f : S→ℕ) (layers u : ℕ) :
    (∑ s, layers * (u * f s)) = layers * (u * ∑ s, f s) := by
  simp only [Finset.mul_sum]

set_option maxHeartbeats 800000 in
theorem edge_width (D layers C b u : ℕ) (e : (Q).Edge) :
    (graph (host G.arcs D layers C b u)).width (DescentCommonPalette.rotorEdge G D layers C b u e)=
      layers*(u*price G C b e) := by
  rcases e with e | ⟨v,k⟩
  · rfl
  · let N := host G.arcs D layers C b u
    let slots := rowFibre (D:=D) (R:=layers) (C:=C) (w:=b) (u:=u) G v
    let fee := fun s => layers * (u * DescentRotor.SlotWidth G.arcs C b v s)
    change (∑ j, localWidth N v j) = layers * (u * price G C b (.inr ⟨v,k⟩))
    calc
      _ = ∑ p : Fibre N v, width N p.val :=
        (index N v).symm.sum_comp (fun p => width N p.val)
      _ = ∑ p : Fibre N v, fee (slots p) :=
        Finset.sum_congr rfl fun p _ =>
          DescentRotor.Physical.local_legs (D:=D) (R:=layers) (C:=C) (w:=b) (u:=u) G v p
      _ = ∑ s, fee s := slots.sum_comp fee
      _ = layers * (u * ∑ s, DescentRotor.SlotWidth G.arcs C b v s) :=
        sum_scaled_prices (DescentRotor.SlotWidth G.arcs C b v) layers u
      _ = _ := by
        apply congrArg (fun z : ℕ => layers * (u * z))
        refine Eq.trans ?_ (spine_price_slots G C b v k).symm
        apply Finset.sum_congr (congrArg (@Finset.univ (DescentRotor.Slot G.arcs v)) (Subsingleton.elim _ _))
        intro _ _
        rfl

theorem spine_price (C b : ℕ) (v : Fin (2^n)) (i : Fin (count (bare) v+1)) :
    price G C b (.inr ⟨v,i⟩)=(2+2*h*C)*b := by
  rw [spine_price_slots,Fintype.sum_sum_type]
  simp [DescentRotor.SlotWidth,DescentRotor.regular_ports]
 ; ring

/-- The inverse lives in the immutable finite rotor menu. For the changing stage this is
a single fixed table of geometry, including every zero-arity and parallel-arc case. -/
def order : (Q).Edge ≃ Fin (Fintype.card (Q).Edge) :=
  let code := DescentRosterOrder.compact (rotorWire G)
  Equiv.ofBijective code ((Fintype.bijective_iff_injective_and_card _).2 ⟨code.injective,by simp⟩)

def edgeAt (slot : ℕ) : Option (Q).Edge :=
  if live : slot<Fintype.card (Q).Edge then some ((order G).symm ⟨slot,live⟩) else none

theorem edgeAt_slot (Ht : ℕ) (e : (Q).Edge) :
    edgeAt G (DescentResetCableSlots.rotor Ht G e).val=some e := by
  change edgeAt G (order G e).val=some e
  simp [edgeAt]

theorem edgeAt_padding (slot : ℕ) (dead : Fintype.card (Q).Edge≤ slot) :
    edgeAt G slot=none := by simp [edgeAt,Nat.not_lt.mpr dead]

structure Header where
  active : ℕ
  source : ℕ
  target : ℕ
  width : ℕ
  core : ℕ
  deriving DecidableEq

def header (C b u layers : ℕ) (site : (Q).Site→ℕ) (slot : ℕ) : Header :=
  match edgeAt G slot with
  | none=>⟨0,0,0,0,0⟩
  | some e=>⟨1,site ((Q).src e),site ((Q).dst e),layers*(u*price G C b e),1⟩

theorem header_slot (Ht D C b u layers : ℕ) (site : (Q).Site→ℕ) (e : (Q).Edge) :
    header G C b u layers site (DescentResetCableSlots.rotor Ht G e).val=
      let actual := DescentCommonPalette.rotorEdge G D layers C b u e
      let readSite := (DescentCommonPalette.rotorSiteEquiv G D layers C b u).symm
      let installed := graph (host G.arcs D layers C b u)
      ⟨1,site (readSite (installed.src actual)),site (readSite (installed.dst actual)),
        installed.width actual,1⟩ := by
  dsimp only
  rw [header,edgeAt_slot,edge_width,DescentCommonPalette.rotor_left,DescentCommonPalette.rotor_right]
  change _ = Header.mk 1
    (site ((DescentCommonPalette.rotorSiteEquiv G D layers C b u).symm
      ((DescentCommonPalette.rotorSiteEquiv G D layers C b u) ((Q).src e))))
    (site ((DescentCommonPalette.rotorSiteEquiv G D layers C b u).symm
      ((DescentCommonPalette.rotorSiteEquiv G D layers C b u) ((Q).dst e))))
    (layers * (u * price G C b e)) 1
  simp only [Equiv.symm_apply_apply]

theorem header_padding (C b u layers : ℕ) (site : (Q).Site→ℕ) (slot : ℕ) (dead : Fintype.card (Q).Edge≤ slot) :
    header G C b u layers site slot=⟨0,0,0,0,0⟩ := by rw [header,edgeAt_padding G slot dead]

/-- Width is computed from the one measured layer field by repeated doubling and fixed
one-bit additions. Its coefficient is stage grain times the immutable physical slot price. -/
def coefficient (C b u slot : ℕ) := (edgeAt G slot).elim 0 (fun e=>u*price G C b e)

def widthTerm (w C b u slot : ℕ) : Term w 0 1 :=
  let k := coefficient G C b u slot
  ProtocolRAMPortScale.scale w (ProtocolRAMPortScale.bitWidth k) k

theorem widthTerm_read {w : ℕ} (C b u slot : ℕ) (site : (Q).Site→ℕ) (layers : ℕ) (m : Memory w) (vs : Fin 1→Word w)
    (measured : vs 0=(layers : Word w)) :
    (widthTerm G w C b u slot).eval Fin.elim0 m vs=((header G C b u layers site slot).width : Word w) := by
  rw [widthTerm,ProtocolRAMPortScale.eval_scale _ _ _ _ (ProtocolRAMPortScale.fits _),measured]
  cases hit : edgeAt G slot <;> simp [coefficient,header,hit]

theorem widthTerm_binds (w C b u slot : ℕ) :
    (widthTerm G w C b u slot).binds≤1+2*ProtocolRAMPortScale.bitWidth (coefficient G C b u slot) :=
  ProtocolRAMPortScale.binds ..

theorem widthTerm_cheap (w C b u slot : ℕ) :
    ProtocolRAM.admissible (widthTerm G w C b u slot) := DescentWordProduct.scale_ok ..

variable {V A I F K : Type} [Fintype V] [DecidableEq V] [Fintype A] [Fintype I] [Fintype F] [Field K]
variable {k C b u : ℕ} (P : Placement V I F A k (2^n)) (Ht : ℕ)
variable (depth : ∀s t,(P.fallbackBook s t).height≤Ht) (hw : 0<b) (pay : ℝ)
variable (hardware : Hardware (K:=K) (C₀:=C) (u:=u) P G hw pay) (D : ℕ)
local notation "sel" => selected P G hw pay hardware
local notation "dev" => device G hw u P.contact P.input P.site P.owner P.align (D:=D)

theorem selected_header (s : Bool) (g : P.Good) (site : (Q).Site→ℕ) (e : (dev (sel s (.inl g))).Edge) :
    header G C b u (hardware s g).layers site
      (DescentResetCableSlots.privateWire P Ht depth G hw pay hardware D (s,.inl g) e).val =
      let readSite := (DescentCommonPalette.rotorSiteEquiv G D (selectedRotorLayers P G hw pay hardware s g) C b u).symm
      ⟨1,site (readSite ((dev (sel s (.inl g))).src e)),site (readSite ((dev (sel s (.inl g))).dst e)),
        (dev (sel s (.inl g))).width e,1⟩ := by
  let actualLayers := selectedRotorLayers P G hw pay hardware s g
  let edges := DescentCommonPalette.rotorEdgeEquiv G D actualLayers C b u
  obtain ⟨e₀,rfl⟩ := edges.surjective e
  change header G C b u (hardware s g).layers site
    (DescentResetCableSlots.rotor Ht G (edges.symm (edges e₀))).val = _
  rw [edges.symm_apply_apply]
  conv_lhs => rw [←selectedRotorLayers_eq P G hw pay hardware s g]
  exact header_slot G Ht D C b u actualLayers site e₀

variable {slots oldCap : ℕ} (vertex : V↪Fin slots) (code : F↪V×DescentContacts.Endpoint (2^n))
variable (valid : ∀t,(code t).2.1.1≤k ∧ (code t).2.1.2<2^(code t).2.1.1) (old : I↪Fin oldCap)
local notation "bs" => slots*2^k
local notation "ts" => slots*(2^(k+1)*(2^n+1))
local notation "cc" => max (Fintype.card (Computability.BorderVNP.Crossing.Network.Edge Q)) (2^(Ht+1))
local notation "cap" => bs*2^n+ts*2^Ht

/-- The same fixed rotor cable has a concrete global ordinal inside the complete reset archive. -/
def completePort (s : Bool) (g : P.Good) (e : (Q).Edge) : ℕ :=
  2*oldCap+(ts+(cap+((DescentResetCableSlots.rotor Ht G e).val+
    cc*((DescentResetCableSlots.base P vertex g).val+(bs+ts)*(finTwoEquiv.symm s).val))))

theorem completePort_read (s : Bool) (g : P.Good) (e : (dev (sel s (.inl g))).Edge) :
    (DescentResetCableSlots.complete P vertex code valid Ht depth G hw pay hardware D old
      (.inr (.inr (.inr ⟨(s,.inl g),e⟩)))).val=completePort (oldCap:=oldCap) G P Ht vertex s g
        ((DescentCommonPalette.rotorEdgeEquiv G D (selectedRotorLayers P G hw pay hardware s g) C b u).symm e) := by
  rfl

theorem completeArm_read (s : Bool) (e : I) :
    (DescentResetCableSlots.complete P vertex code valid Ht depth G hw pay hardware D old (.inl (s,e))).val=
      (old e).val+oldCap*(finTwoEquiv.symm s).val := rfl

end
end Hierarchy.DescentRotorPrivateFields

end OAI
