import OAI.Hierarchy.DescentPackedPrivateMenu
import OAI.Hierarchy.DescentInstalledFallbackHeader
import OAI.Hierarchy.DescentPackedIssuedFallback

namespace OAI
/-! # Reconstructing real installed wires from relative tickets and integral sizes -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentChosenRouter DescentCommonHost DescentResetHostSize DescentRelativeContacts
open DescentResetCableSlots DescentResetPaletteCode DescentHostDirectory DescentRouterSlots DescentMixedRouter
open DescentPackedPrivateMenu DescentSIMDLookup DescentPackedFallbackTree
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "X" => Z.placement
local notation "Q" => DescentCommonPalette.rotor Z.graph
local notation "menu" => selected (X) Z.graph Z.positive Z.pay Z.circuit
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (X).contact (X).input (X).site (X).owner (X).align (D:=d)
local notation "Y" => (2^Z.n:ℕ)
local notation "r" => (Z.k-T.commonDepth)
local notation "levelsOf" => DescentChosenRouter.selectedRotorLayers (X) Z.graph Z.positive Z.pay Z.circuit
local notation "slot" => privateWire (X) Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d

def layerLimit := ⌊21*Z.pay/((2:ℝ)^Z.n*Z.width*Z.unit)⌋₊
def layerBits := ProtocolRAMPurchaseSampler.bits (layerLimit Z)

theorem layers_fit (unit : 0<Z.unit) (s : Bool) (g : (X).Good) :
    (Z.circuit s g).layers<2^(layerBits Z) := by
  have charge:=(Z.circuit s g).bitCost
  rw [DescentRotor.attached_bit_cost] at charge
  let factor : ℝ:=((2*h+4)*(2*h*C+2):ℕ)
  have pos : 0<factor:=by dsimp [factor];positivity
  have le : ((Z.circuit s g).layers:ℝ)*((2:ℝ)^Z.n*Z.width*Z.unit)≤21*Z.pay := by
    apply le_of_mul_le_mul_left _ pos
    convert charge using 1 <;> dsimp [factor] <;> push_cast <;> ring
  have low : (Z.circuit s g).layers≤layerLimit Z := Nat.le_floor ((le_div_iff₀ (by
    have:=Z.positive;positivity : 0<(2:ℝ)^Z.n*Z.width*Z.unit)).2 le)
  exact low.trans_lt (ProtocolRAMPurchaseSampler.lt_span _)

def rotorKey (unit : 0<Z.unit) (count : ℕ) (s : Bool) (g : (X).Good) :
    Key (n:=Z.n) r Ht count (layerBits Z) :=
  some (.inl (interval r (goodLabel Z T g),⟨(Z.circuit s g).layers,layers_fit Z unit s g⟩))

def fallbackKey {count : ℕ} (s : Bool) (t : Z.Fallback) (arrivals : Panel Ht count) :
    Key (n:=Z.n) r Ht count (layerBits Z) :=
  some (.inr (interval r (fallLabel Z T t),optional (T.code t).2.2,
    DescentPackedFallbackTree.pack Ht ((X).fallbackBook s t).height arrivals))

def localHost (s : Bool) (g : (X).Site) (v : (dev (menu s g)).Site) :=
  rom Z.graph r Ht (ordinal Z.graph r Ht (privateLocal Z T s g v)).val

def localCable (s : Bool) (g : (X).Site) (e : (dev (menu s g)).Edge) (units : ℕ) : Fin 5→ℕ :=
  ![1,localHost Z T s g ((dev (menu s g)).src e),localHost Z T s g ((dev (menu s g)).dst e),units,1]

theorem rotor_fields (unit : 0<Z.unit) (count : ℕ) (s : Bool) (g : (X).Good) (e : (dev (menu s (.inl g))).Edge) :
    values Z.graph r Ht count (layerBits Z) C Z.width s (slot (s,.inl g) e).val (rotorKey Z T unit count s g)=
      localCable Z T s (.inl g) e ((Z.circuit s g).layers*DescentRotorPrivateFields.price Z.graph C Z.width
        ((DescentCommonPalette.rotorEdgeEquiv Z.graph d (levelsOf s g) C Z.width Z.unit).symm e)) := by
  let E := DescentCommonPalette.rotorEdgeEquiv Z.graph d (levelsOf s g) C Z.width Z.unit
  let bare := E.symm e
  have ticket : (slot (s,.inl g) e).val=(DescentResetCableSlots.rotor Ht Z.graph bare).val := rfl
  let loc (v : (Q).Site) : DescentResetPaletteCode.Local Z.graph r Ht := (s,goodLabel Z T g,.inl v)
  have source : privateLocal Z T s (.inl g) ((dev (menu s (.inl g))).src e)=loc ((Q).src bare) :=
    congrArg loc (DescentCommonPalette.rotor_left_inv Z.graph d (levelsOf s g) C Z.width Z.unit e)
  have target : privateLocal Z T s (.inl g) ((dev (menu s (.inl g))).dst e)=loc ((Q).dst bare) :=
    congrArg loc (DescentCommonPalette.rotor_right_inv Z.graph d (levelsOf s g) C Z.width Z.unit e)
  unfold values rotorKey DescentPackedRotorPanel.fields
  rw [ticket,DescentRotorPrivateFields.edgeAt_slot]
  simp only [localCable,localHost,source,target,loc,rotor_address,encoder,bare,E]

theorem rotor_measured (s : Bool) (g : (X).Good) (e : (dev (menu s (.inl g))).Edge) :
    (dev (menu s (.inl g))).width e=Z.unit*((Z.circuit s g).layers*DescentRotorPrivateFields.price Z.graph C Z.width
      ((DescentCommonPalette.rotorEdgeEquiv Z.graph d (levelsOf s g) C Z.width Z.unit).symm e)) := by
  let E := DescentCommonPalette.rotorEdgeEquiv Z.graph d (levelsOf s g) C Z.width Z.unit
  obtain ⟨i,rfl⟩ := E.surjective e
  change (dev (menu s (.inl g))).width (E i)=Z.unit*((Z.circuit s g).layers*
    DescentRotorPrivateFields.price Z.graph C Z.width (E.symm (E i)))
  rw [E.symm_apply_apply]
  calc
    _ = (levelsOf s g)*(Z.unit*DescentRotorPrivateFields.price Z.graph C Z.width i) :=
      DescentRotorPrivateFields.edge_width Z.graph d (levelsOf s g) C Z.width Z.unit i
    _ = _ := by rw [DescentChosenRouter.selectedRotorLayers_eq]; ac_rfl

set_option maxHeartbeats 1000000 in
theorem fallback_fields {count : ℕ} (s : Bool) (t : Z.Fallback) (arrivals : Panel Ht count) (e : (dev (menu s (.inr t))).Edge) :
    let shape:=DescentPrivateTreeTemplate.lookup Ht ((X).fallbackBook s t).height (slot (s,.inr t) e).val (fun q=>heap q)
    values Z.graph r Ht count (layerBits Z) C Z.width s (slot (s,.inr t) e).val (fallbackKey Z T s t arrivals)=
      localCable Z T s (.inr t) e (DescentPackedFallbackTree.count arrivals shape) := by
  let depth:=((X).fallbackBook s t).height
  have hd : depth<2^(Ht+2) := (T.bookHeight s t).trans_lt ((Nat.lt_two_pow_self (n:=Ht)).trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega)))
  have hit : DescentPrivateTreeTemplate.edgeAt depth (slot (s,.inr t) e).val = some e :=
    DescentPrivateTreeTemplate.edgeAt_slot (X) Ht T.bookHeight Z.graph s t e
  let line:=DescentPrivateTreeTemplate.lookup Ht depth (slot (s,.inr t) e).val (fun q=>heap q)
  have shape : DescentPackedFallbackTree.localShape (H:=Ht) (n:=count) (fun _ q=>heap q) (slot (s,.inr t) e).val
      (DescentPackedFallbackTree.pack Ht depth arrivals)=line := by
    have read : ((encode (Ht+2) (count+1)).symm
        (DescentPackedFallbackTree.pack Ht depth arrivals) 0).val = depth := by
      rw [DescentPackedFallbackTree.pack,Equiv.symm_apply_apply,Fin.cons_zero,Fin.val_cast_of_lt hd]
    exact congrArg (fun z => DescentPrivateTreeTemplate.lookup Ht z (slot (s,.inr t) e).val (fun q => heap q)) read
  have isLive : line.active=1 := by simp only [line,DescentPrivateTreeTemplate.lookup,hit]
  have sourceRead : line.source=heap ((dev (menu s (.inr t))).src e) := by
    simp only [line,DescentPrivateTreeTemplate.lookup,hit]; rfl
  have targetRead : line.target=heap ((dev (menu s (.inr t))).dst e) := by
    simp only [line,DescentPrivateTreeTemplate.lookup,hit]; rfl
  let base := Fintype.card (Q).Site + 2^(Ht+1) * (DescentResetCableSlots.optional (T.code t).2.2).val +
    (Fintype.card (Q).Site + (Y+1)*2^(Ht+1)) *
    ((interval r (fallLabel Z T t)).val + 2^(r+1)*(finTwoEquiv.symm s).val)
  have address (v : (dev (menu s (.inr t))).Site) :
      rom Z.graph r Ht (base+heap v) = localHost Z T s (.inr t) v := by
    apply congrArg (rom Z.graph r Ht)
    change base+heap v = (ordinal Z.graph r Ht (s,fallLabel Z T t,.inr ((T.code t).2.2,raiseTree (T.bookHeight s t) v))).val
    refine Eq.trans ?_ (tree_address Z.graph r (T.bookHeight s t) s (fallLabel Z T t) (T.code t).2.2 v).symm
    dsimp only [base,encoder]
    ac_rfl
  unfold values fallbackKey fallbackFields
  dsimp only
  change (if (DescentPackedFallbackTree.localShape (H:=Ht) (n:=count) _ _ (DescentPackedFallbackTree.pack Ht depth arrivals)).active=0 then _ else _)=_
  rw [shape,ite_eq_right (by omega : ¬line.active=0),tally_pack,sourceRead,targetRead]
  change ![1,rom Z.graph r Ht (base+_),rom Z.graph r Ht (base+_),_,1]=_
  rw [address,address]
  rfl

def expand {H : ℕ} (vertex : Z.V↪Fin H) (g : (X).Site) (localFields : Fin 5→ℕ) : Fin 7→ℕ :=
  let common:=(DescentDenseHostOrder.roster Z.graph r Ht).card*(vertex (rootVertex Z T g)).val
  let group:=(X).siteGroup T.commonDepth T.code g
  if localFields 0=0 then fun _=>0 else
    ![localFields 0,localFields 1+common,localFields 2+common,group,group,Z.unit*localFields 3,localFields 4]

@[simp] theorem expand_zero {H : ℕ} (vertex : Z.V↪Fin H) (g : (X).Site) :
    expand Z T vertex g (fun _=>0)=fun _=>0 := by simp [expand]

theorem expand_measured {H : ℕ} (vertex : Z.V↪Fin H) (s : Bool) (g : (X).Site) (e : (dev (menu s g)).Edge)
    (units : ℕ) (paid : (dev (menu s g)).width e=Z.unit*units) :
    expand Z T vertex g (localCable Z T s g e units)=actualRecord Z T vertex (privateWireAt Z T s g e) := by
  rw [record_actual]
  funext j
  fin_cases j <;> simp [expand,localCable,localHost,privateRecord,privateHost,paid]

theorem rotor_row {H : ℕ} (vertex : Z.V↪Fin H) (unit : 0<Z.unit) (count : ℕ) (s : Bool) (g : (X).Good)
    (e : (dev (menu s (.inl g))).Edge) :
    expand Z T vertex (.inl g)
      (values Z.graph r Ht count (layerBits Z) C Z.width s (slot (s,.inl g) e).val (rotorKey Z T unit count s g))=
      actualRecord Z T vertex (privateWireAt Z T s (.inl g) e) := by
  rw [rotor_fields,expand_measured Z T vertex _ _ _ _ (rotor_measured Z s g e)]

end
end Hierarchy.DescentSixParty.ResetInput


namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots DescentMixedRouter
open DescentSIMDLookup DescentPackedPrivateMenu DescentResetCableSlots
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "X" => Z.placement
local notation "slots" => 2^(m-T.commonDepth)*(2*A.cap)
local notation "menu" => selected (X) Z.graph Z.positive Z.pay Z.circuit
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (X).contact (X).input (X).site (X).owner (X).align (D:=d)
local notation "slot" => privateWire (X) Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d
local notation "r" => (Z.k-T.commonDepth)

set_option maxHeartbeats 1000000 in
theorem tree_row {H : ℕ} (vertex : Z.V↪Fin H) (s : Bool) (t : Z.Fallback) (e : (dev (menu s (.inr t))).Edge) :
    let occurrences:=leafPanel A S ready digits native Z T frame s t
    Z.expand T vertex (.inr t)
      (values Z.graph r Ht slots (Z.layerBits) C Z.width s (slot (s,.inr t) e).val (Z.fallbackKey T s t occurrences))=
      Z.actualRecord T vertex (Z.privateWireAt T s (.inr t) e) := by
  dsimp only
  rw [ResetInput.fallback_fields]
  exact Z.expand_measured T vertex s (.inr t) e _
    (private_width A S ready digits native Z T frame s t e (fun _ v=>DescentResetPaletteCode.heap v))

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
