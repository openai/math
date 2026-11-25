import OAI.Hierarchy.DescentPackedRotorPanel
import OAI.Hierarchy.DescentPackedLocalLookup

namespace OAI
/-! # Shared finite private-cable menu for occupied rotor and exceptional roots -/

namespace Hierarchy.DescentPackedPrivateMenu
open DescentSIMDLookup DescentResetPaletteCode DescentPackedFallbackTree ProtocolRAM
open DescentPackedFallbackTree.Image Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor G
local notation "Y" => (2^n:ℕ)
local notation "labels" => (fun r=>2^(r+1))
local notation "trees" => (fun H=>2^(H+1))
local notation "kinds" => (fun H => Fintype.card (Computability.BorderVNP.Crossing.Network.Site (DescentCommonPalette.rotor G)) + (Y+1)*trees H)

abbrev Tree (r H count : ℕ) := Cell (r+1) × Fin (Y+1) × Cell (width H count)
abbrev Key (r H count layerBits : ℕ) := Option (DescentPackedRotorPanel.Live r layerBits ⊕ Tree (n:=n) r H count)

def rotorSlots (r layerBits : ℕ) := labels r*2^layerBits
def treeSlots (n r H count : ℕ) := labels r*((2^n+1)*2^(width H count))
def size (n r H count layerBits : ℕ) := (rotorSlots r layerBits+treeSlots n r H count)+1
def bits (n r H count layerBits : ℕ) := ProtocolRAMPurchaseSampler.bits (size n r H count layerBits)

def tag (r H count l : ℕ) : Key (n:=n) r H count l ≃ Fin (size n r H count l) :=
  (Equiv.optionCongr ((Equiv.sumCongr finProdFinEquiv
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv)).trans
      (finSuccEquiv _).symm

def pack (r H count l : ℕ) (key : Key (n:=n) r H count l) : Cell (bits n r H count l) :=
  Fin.castLE (ProtocolRAMPurchaseSampler.lt_span _).le (tag r H count l key)

@[simp] theorem empty_key (r H count l : ℕ) :
    (pack (n:=n) r H count l none).val=0 := rfl

theorem rotor_key (r H count l : ℕ) (label : Cell (r+1)) (layers : Cell l) :
    (pack (n:=n) r H count l (some (.inl (label,layers)))).val=1+(layers.val+2^l*label.val) := by
  change ((finSuccEquiv _).symm (some (Fin.castAdd (treeSlots n r H count)
    (finProdFinEquiv (label,layers))))).val = _
  rw [finSuccEquiv_symm_some]
  exact Nat.add_comm _ 1

theorem tree_key (r H count l : ℕ) (label : Cell (r+1)) (opt : Fin (Y+1)) (arrivals : Cell (width H count)) :
    (pack r H count l (some (.inr (label,opt,arrivals)))).val=
      1+rotorSlots r l+(arrivals.val+2^(width H count)*(opt.val+(Y+1)*label.val)) := by
  change ((finSuccEquiv _).symm (some (Fin.natAdd (rotorSlots r l)
    (finProdFinEquiv (label,finProdFinEquiv (opt,arrivals)))))).val = _
  rw [finSuccEquiv_symm_some]
  change rotorSlots r l + ((arrivals.val + 2^(width H count)*opt.val) +
    ((2^n+1)*2^(width H count))*label.val) + 1 = _
  ring

def unpack (r H count l : ℕ) (x : Cell (bits n r H count l)) : Key (n:=n) r H count l :=
  if ok : x.val<size n r H count l then (tag r H count l).symm ⟨x.val,ok⟩ else none

@[simp] theorem unpack_pack (r H count l : ℕ) (key : Key (n:=n) r H count l) :
    unpack r H count l (pack r H count l key)=key := by
  have small : (pack r H count l key).val < size n r H count l :=
    (tag (n:=n) r H count l key).isLt
  unfold unpack
  rw [dite_eq_left small]
  exact (tag (n:=n) r H count l).symm_apply_apply key

def fallbackFields (r H count : ℕ) (s : Bool) (slot : ℕ) (x : Tree (n:=n) r H count) : Fin 5→ℕ :=
  let shape:=localShape (fun _ q=>heap q) slot x.2.2
  let base:=Fintype.card (Q).Site+trees H*x.2.1.val+kinds H*(x.1.val+labels r*(finTwoEquiv.symm s).val)
  if shape.active=0 then fun _=>0 else ![1,rom G r H (base+shape.source),rom G r H (base+shape.target),tally x.2.2 shape,1]

def values (r H count l C b : ℕ) (s : Bool) (slot : ℕ) : Key (n:=n) r H count l→Fin 5→ℕ
  | none=>fun _=>0
  | some (.inl t)=>DescentPackedRotorPanel.fields G r H C b s slot t.1.val t.2.val
  | some (.inr t)=>fallbackFields G r H count s slot t

def fieldBound (r H count l C b : ℕ) := max count (DescentPackedRotorPanel.ceiling G r H l C b)
def fieldBits (r H count l C b : ℕ) := ProtocolRAMPurchaseSampler.bits (fieldBound G r H count l C b)

theorem tally_le {H count : ℕ} (x : Cell (width H count)) (shape : DescentPrivateTreeTemplate.Template) :
    tally x shape≤count := by
  unfold tally
  calc
    _≤∑ _ : Fin count,1:=Finset.sum_le_sum (fun i _=>by split <;> omega)
    _=count:=by simp

theorem fit (r H count l C b : ℕ) (s : Bool) (slot : ℕ) (key : Key (n:=n) r H count l) (j : Fin 5) :
    values G r H count l C b s slot key j<2^(fieldBits G r H count l C b) := by
  apply Nat.lt_of_le_of_lt _ (ProtocolRAMPurchaseSampler.lt_span _)
  let top:=DescentPackedRotorPanel.ceiling G r H l C b
  have upper : top≤fieldBound G r H count l C b:=Nat.le_max_right ..
  have flags : 1≤fieldBound G r H count l C b:=(Nat.le_max_left _ _).trans upper
  have palette : ∀a,rom G r H a≤fieldBound G r H count l C b:=fun a=>(DescentPackedRotorPanel.rom_bound G r H a).trans
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans upper))
  rcases key with _ | (x|x)
  · simp [values]
  · exact (DescentPackedRotorPanel.field_bound G r H l C b s slot x j).trans upper
  · change fallbackFields G r H count s slot x j ≤ fieldBound G r H count l C b
    by_cases inactive : (localShape (H:=H) (n:=count) (fun _ q=>heap q) slot x.2.2).active=0
    · simpa only [fallbackFields, ite_eq_left inactive] using Nat.zero_le (fieldBound G r H count l C b)
    · have cnt : tally x.2.2 (localShape (H:=H) (n:=count) (fun _ q=>heap q) slot x.2.2)
          ≤ fieldBound G r H count l C b :=
        (tally_le (H:=H) (count:=count) x.2.2 _).trans (Nat.le_max_left _ _)
      simp only [fallbackFields, ite_eq_right inactive]
      fin_cases j <;> first | exact flags | exact palette _ | exact cnt

def panel (r H count l C b cap : ℕ) (s : Bool) (x : Cell (bits n r H count l)) :
    Cell (fieldBits G r H count l C b*(cap*5)) :=
  encode _ _ (fun z=>let q : Fin cap×Fin 5:=finProdFinEquiv.symm z
    ((values G r H count l C b s q.1.val (unpack r H count l x) q.2:ℕ):Cell (fieldBits G r H count l C b)))

theorem cell_read (r H count l C b cap : ℕ) (s : Bool) (key : Key (n:=n) r H count l) (q : Fin cap) (j : Fin 5) :
    digit (fieldBits G r H count l C b) (finProdFinEquiv (q,j)).val
      (panel G r H count l C b cap s (pack r H count l key)).val=values G r H count l C b s q.val key j := by
  rw [panel,digit_encode,Equiv.symm_apply_apply,unpack_pack,Fin.val_cast_of_lt (fit ..)]

theorem compiled {hosts groups M w : ℕ} (g : DescentSIMDLookup.Banks) (out r H count l C b cap : ℕ)
    (s : Bool) (x : Fin hosts→Fin groups→Key (n:=n) r H count l) (pos : 0<M)
    (safe : Fits g (bits n r H count l) (fieldBits G r H count l C b*(cap*5)) M hosts groups w out)
    (m : Memory w) (fixed : resident (panel G r H count l C b cap s) g hosts groups M m)
    (issued : ∀q : Row hosts groups M,m (g.source.base+(row hosts groups M q).val)=
      (data (fun v i=>pack r H count l (x v i)) q).val) :
    let dst:=imageBank hosts groups M out g m
    (program g out hosts groups M w).Exec m dst (4+44*(hosts*chunks groups M)) ∧
    (∀v i (edge : Fin cap) (field : Fin 5),digit (fieldBits G r H count l C b) (finProdFinEquiv (edge,field)).val
      (digit (fieldBits G r H count l C b*(cap*5)) (lane i pos).val (dst (out+(row hosts groups M (position v i pos)).val)).val)=
        values G r H count l C b s edge.val (x v i) field) ∧
    (∀a<out,dst a=m a) ∧ ∀a,out+hosts*chunks groups M≤a→dst a=m a := by
  obtain ⟨run,read,frame⟩:=DescentPackedLocalLookup.compile g out (panel G r H count l C b cap s) (fun v i=>pack r H count l (x v i)) pos safe m fixed issued
  refine ⟨run,?_,frame⟩
  intro v i edge field
  rw [read,cell_read]

theorem tariff (g : DescentSIMDLookup.Banks) (hosts groups r H count l C b cap W a K : ℕ)
    (wide : 2*max (bits n r H count l) (fieldBits G r H count l C b*(cap*5))≤a) (physical : W≤K*a) :
    let span:=max (bits n r H count l) (fieldBits G r H count l C b*(cap*5));let M:=lanes a span
    (4+44*(hosts*chunks groups M))*W≤K*(4*a+44*(hosts*a+4*hosts*groups*span)) := by
  have pos : 0<bits n r H count l := Nat.zero_lt_succ _
  have h:=(invoice g hosts groups (bits n r H count l) (fieldBits G r H count l C b*(cap*5)) a
    (lt_of_lt_of_le pos (le_max_left _ _)) wide).1
  apply DescentPackedPayloadBudget.clock physical
  simpa [lookup_work,Nat.mul_comm 44] using h

end
end Hierarchy.DescentPackedPrivateMenu

end OAI
