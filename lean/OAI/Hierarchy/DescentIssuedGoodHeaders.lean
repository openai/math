import OAI.Hierarchy.DescentGatheredLookupWords
import OAI.Hierarchy.DescentRotorRootPresence
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedLocalLookup
import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentRecordedRotorLayers

namespace OAI
/-! # Native private rotor edge headers from the old capacity, depth and physical stencil -/
namespace Hierarchy.DescentIssuedGoodHeaders
open DescentSIMDLookup DescentPackedFallbackTree.Image DescentPackedZip DescentPackedPrivateMenu
open DescentPacking.PackedMatch.Local.Gather DescentResetHostSize DescentRotorRootPresence
open DescentSixParty DescentRelativeContacts DescentResetPaletteCode DescentColonies
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMGeneratedWrite ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {n h field H G w M : ℕ}
abbrev Input (r : ℕ):=Fin 2 ⊕ Block r
abbrev num (r : ℕ):=2+2^r
def ix {r : ℕ} : Input r ≃ Fin (num r):=finSumFinEquiv
abbrev Data (r field : ℕ):=Input r→Cell field

def key {r : ℕ} (n packet f Ht count l : ℕ) (t : Code r) (v : Data r field) :
    Key (n:=n) r Ht count l:=
  if (v (.inl 1)).val=t.val.1+1 ∧ (v (.inr (sample t))).val%2=0 then
    some (.inl (DescentResetCableSlots.interval r t,
      ⟨DescentRecordedRotorLayers.layers n packet f (v (.inl 0)).val%2^l,Nat.mod_lt _ (Nat.two_pow_pos _)⟩))
  else none

def headers (board : NonlinearExpanders.Graph n h) {r : ℕ} (packet f Ht count l C cap : ℕ)
    (side : Bool) (t : Code r) (v : Data r field) :=
  panel board r Ht count l C packet cap side (pack r Ht count l (key n packet f Ht count l t v))

def decode {r field : ℕ} (x : Cell (field*num r)) : Data r field :=
  fun j=>(encode field (num r)).symm x (ix j)

def word {r field : ℕ} (x : Data r field) := encode field (num r) (fun j=>x (ix.symm j))
theorem decode_word {r field : ℕ} (x : Data r field) : decode (word x)=x := by
  funext j
  simp [decode,word]

theorem gathered {N b : ℕ} (emit : (Fin N→Cell field)→Cell b)
    (tables : Fin N→Tables) (reads : Fin N→Expr) (menu : DescentSIMDLookup.Banks)
    (mid out : ℕ) (x : Fin H→Fin G→Fin N→Cell field) (positive : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*N) b M H G w out)
    (rom : resident (emit ∘ (encode field N).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*N)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit b (lane g positive).val (dst (out+(row H G M (position a g positive)).val)).val=(emit (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,_,read,frame⟩:=gathered_words emit tables reads menu mid out x positive mem bounds constants
    sources room fit rom dictLow maskLow wire
  exact ⟨run,read,frame⟩

/-- All true prior data feed one packed gather and one numerical menu on the same memory. -/
theorem issued_rotor_headers (board : NonlinearExpanders.Graph n h) {r : ℕ} (packet f Ht count l C cap : ℕ)
    (side : Bool) (t : Code r) (tables : Fin (num r)→Tables) (reads : Fin (num r)→Expr)
    (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (x : Fin H→Fin G→Data r field) (positive : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads (ix j)) (fun a g=>x a g j) M mem)
    (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*num r) (fieldBits board r Ht count l C packet*(cap*5)) M H G w out)
    (rom : resident (headers board packet f Ht count l C cap side t ∘ @decode r field) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*num r)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (fieldBits board r Ht count l C packet*(cap*5)) (lane g positive).val
      (dst (out+(row H G M (position a g positive)).val)).val=(headers board packet f Ht count l C cap side t (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=mem addr := by
  let emit (a : Fin (num r)→Cell field):=headers board packet f Ht count l C cap side t (fun j=>a (ix j))
  let sourceRow (a : Fin H) (g : Fin G) (j : Fin (num r)):=x a g (ix.symm j)
  have actual (j : Fin (num r)) : Source (reads j) (fun a g=>sourceRow a g j) M mem := by
    simpa [sourceRow] using sources (ix.symm j)
  obtain ⟨run,read,frame⟩:=gathered emit tables reads menu mid out sourceRow positive mem bounds constants actual
    room fit rom dictLow maskLow wire
  refine ⟨run,?_,frame⟩
  intro a g
  simpa [emit,sourceRow] using read a g

/-- The good-root program only needs the capacity, relative depth plus one and the
    sampled predecessor's bad flag. Its static lookup therefore has three short operands. -/
def compactKey {r : ℕ} (t : Code r) (u : Data r field) : Fin 3→Cell field :=
  fun j=>if j=0 then u (.inl 0) else if j=1 then u (.inl 1) else u (.inr (sample t))

def compactHeaders (board : NonlinearExpanders.Graph n h) {r : ℕ} (packet f Ht count l C cap : ℕ)
    (side : Bool) (t : Code r) (u : Fin 3→Cell field) :=
  headers board packet f Ht count l C cap side t
    (fun q=>match q with | .inl j=>if j=0 then u 0 else u 1 | .inr _=>u 2)

theorem compact_read (board : NonlinearExpanders.Graph n h) {r : ℕ} (packet f Ht count l C cap : ℕ)
    (side : Bool) (t : Code r) (u : Data r field) :
    compactHeaders board packet f Ht count l C cap side t (compactKey t u)=headers board packet f Ht count l C cap side t u := by
  have h₁ : (1:Fin 2)≠0 := by decide
  have h₂ : (1:Fin 3)≠0 := by decide
  have h₃ : (2:Fin 3)≠0 := by decide
  have h₄ : (2:Fin 3)≠1 := by decide
  simp [compactHeaders,compactKey,headers,key,h₁,h₂,h₃,h₄]

theorem issued_three (board : NonlinearExpanders.Graph n h) {r : ℕ} (packet f Ht count l C cap : ℕ)
    (side : Bool) (t : Code r) (tables : Fin 3→Tables) (reads : Fin 3→Expr)
    (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (x : Fin H→Fin G→Data r field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>compactKey t (x a g) j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (fieldBits board r Ht count l C packet*(cap*5)) M H G w out)
    (rom : resident (compactHeaders board packet f Ht count l C cap side t ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (fieldBits board r Ht count l C packet*(cap*5)) (lane g pos).val
      (dst (out+(row H G M (position a g pos)).val)).val=(headers board packet f Ht count l C cap side t (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,read,frame⟩:=gathered (compactHeaders board packet f Ht count l C cap side t) tables reads menu mid out
    (fun a g=>compactKey t (x a g)) pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,fun a g=>(read a g).trans (congrArg Fin.val (compact_read ..)),frame⟩

open DescentResetTrunks DescentChosenRouter DescentCommonHost DescentResetCableSlots
open DescentRouterSlots DescentMixedRouter DescentPackedFallbackTree

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
  {price ε : ℝ} {C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Z.Terminals)
local notation "X" => Z.placement
local notation "r" => Z.k-T.commonDepth
local notation "menu" => selected (X) Z.graph Z.positive Z.pay Z.circuit
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (X).contact (X).input (X).site (X).owner (X).align (D:=d)
local notation "slot" => privateWire (X) Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d

theorem root_fields (v : Z.V) (hi : Block T.commonDepth) (t : Code r) (oldWord : Block r→ℕ)
    (mode : ∀i,oldWord i%2=Bool.toNat (decide ((X).hub v ∨
       (v,group ((X).b v) (DescentIssuedFallbackPanel.join ((T.commonLow v).trans ((X).depth v)) hi i))∈(X).keys)))
    (depth sampleWord : ℕ) (measure : depth=(X).b v-T.commonDepth+1) (sampled : sampleWord%2=oldWord (sample t)%2) :
    (depth=t.val.1+1 ∧ sampleWord%2=0) ↔
      ∃g : (X).Good,Z.rootVertex T (.inl g)=v ∧ Z.rootBlock T (.inl g)=hi ∧ Z.goodLabel T g=t := by
  rw [←DescentRotorRootPresence.root_present Z T v hi t oldWord mode,sampled]
  simp only [present,decide_eq_true_eq]
  have above:=T.commonLow v
  constructor <;> rintro ⟨depthEq,alive⟩ <;> exact ⟨by omega,alive⟩

theorem unused_cable (f count l cap : ℕ) (s : Bool) (t : Code r) (x : Data r field)
    (slotId : Fin cap) (j : Fin 5) (dead : Fintype.card (DescentCommonPalette.rotor Z.graph).Edge≤ slotId.val) :
    digit (fieldBits Z.graph r Ht count l C Z.width) (finProdFinEquiv (slotId,j)).val
      (headers Z.graph Z.width f Ht count l C cap s t x).val=0 := by
  rw [headers,cell_read]
  unfold key
  split
  · simp [values,DescentPackedRotorPanel.fields,DescentRotorPrivateFields.edgeAt_padding Z.graph slotId.val dead]
  · rfl

/-- A padded ticket is absent even when all physical incident wires have width zero. -/
theorem padded (f count l cap : ℕ) (s : Bool) (v : Z.V) (hi : Block T.commonDepth) (t : Code r)
    (x : Data r field) (dep : (x (.inl 1)).val=(X).b v-T.commonDepth+1)
    (mode : ∀i,(x (.inr i)).val%2=Bool.toNat (decide ((X).hub v ∨
       (v,group ((X).b v) (DescentIssuedFallbackPanel.join ((T.commonLow v).trans ((X).depth v)) hi i))∈(X).keys)))
    (absent : ¬∃a : (X).Good,Z.rootVertex T (.inl a)=v ∧ Z.rootBlock T (.inl a)=hi ∧ Z.goodLabel T a=t)
    (e : Fin cap) (j : Fin 5) :
    digit (fieldBits Z.graph r Ht count l C Z.width) (finProdFinEquiv (e,j)).val
      (headers Z.graph Z.width f Ht count l C cap s t x).val=0 := by
  rw [headers,cell_read]
  have miss:=mt (DescentRotorRootPresence.root_present Z T v hi t (fun i=>(x (.inr i)).val) mode).mp absent
  have no : ¬((x (.inl 1)).val=t.val.1+1 ∧ (x (.inr (sample t))).val%2=0) := by
    rintro ⟨depth,old⟩
    apply miss
    simp only [present,decide_eq_true_eq]
    have:=T.commonLow v
    exact ⟨by omega,old⟩
  simp [key,no,values]

/-- Expansion uses just the group's two wide directory names. Each packed private edge keeps
    relative endpoints and its integral width; the root's historical layer scalar comes from the old capacity. -/
theorem actual_header {H : ℕ} (vertex : Z.V↪Fin H) (unit : 0<Z.unit)
    (f count l cap : ℕ) (s : Bool) (g : (X).Good) (v : Z.V) (hi : Block T.commonDepth) (t : Code r)
    (x : Data r field) (dep : (x (.inl 1)).val=(X).b v-T.commonDepth+1)
    (mode : ∀i,(x (.inr i)).val%2=Bool.toNat (decide ((X).hub v ∨
       (v,group ((X).b v) (DescentIssuedFallbackPanel.join ((T.commonLow v).trans ((X).depth v)) hi i))∈(X).keys)))
    (home : Z.rootVertex T (.inl g)=v) (block : Z.rootBlock T (.inl g)=hi) (tag : Z.goodLabel T g=t)
    (calendar : (Z.circuit s g).layers=DescentRecordedRotorLayers.layers Z.n Z.width f (x (.inl 0)).val)
    (levels : (Z.circuit s g).layers<2^l)
    (e : (dev (menu s (.inl g))).Edge) (room : (slot (s,.inl g) e).val<cap) :
    Z.expand T vertex (.inl g) (fun j=>digit (fieldBits Z.graph r Ht count l C Z.width)
      (finProdFinEquiv (⟨_,room⟩,j)).val (headers Z.graph Z.width f Ht count l C cap s t x).val)=
      Z.actualRecord T vertex (Z.privateWireAt T s (.inl g) e) := by
  have hit:=(DescentRotorRootPresence.root_present Z T v hi t (fun i=>(x (.inr i)).val) mode).mpr ⟨g,home,block,tag⟩
  have decision : (x (.inl 1)).val=t.val.1+1 ∧ (x (.inr (sample t))).val%2=0 := by
    simp only [present,decide_eq_true_eq] at hit
    exact ⟨by omega,hit.2⟩
  rw [←Z.rotor_row T vertex unit count s g e]
  apply congrArg
  funext j
  rw [headers,cell_read,key,ite_eq_left decision]
  change DescentPackedRotorPanel.fields Z.graph r Ht C Z.width s (slot (s,.inl g) e).val
    (DescentResetCableSlots.interval r t).val (DescentRecordedRotorLayers.layers Z.n Z.width f (x (.inl 0)).val % 2^l) j=_
  rw [←calendar,Nat.mod_eq_of_lt levels,←tag]
  rfl

end
end Hierarchy.DescentIssuedGoodHeaders

end OAI
