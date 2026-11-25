import OAI.Hierarchy.ProbePackedPartyRead
import OAI.Hierarchy.TaggedWideCalendarDateCost
import OAI.Hierarchy.TaggedWideTimeOccupancy

namespace OAI
/-! # Gathering the actual role digits into the signed packet's local half words -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting.Middle
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal MotifOuterTerms TraceWords
open Tagged AdaptiveProbe TurnShelf CalendarTape Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
set_option quotPrecheck false
variable {F : Type} [Field F] {n S N H copies cap : ℕ}

def owner (ends : Fin n→Chord S) (s : Fin S) (a : Fin n×Bool) : Option ((portGraph S).Port s) :=
  if h : (portGraph S).vertex (ends a.1) a.2=s then some ⟨(ends a.1,a.2),h⟩ else none

def base (ends : Fin n→Chord S) (bits : Fin n→ℕ) (a : Fin n×Bool) :=
  TaggedShorterCommonScan.earlier (NamedAperture.key ends) bits a.1.val (NamedAperture.key ends a.1)

theorem base_top (ends : Fin n→Chord S) (bits : Fin n→ℕ) (a : Fin n×Bool) :
    base ends bits a+bits a.1≤ installedWidths ends bits (ends a.1) :=
  let key:=NamedAperture.key ends
  calc
    _=TaggedShorterCommonScan.earlier key bits (a.1.val+1) (key a.1) := (NativeSlot.next key bits a.1).symm
    _≤TaggedShorterCommonScan.earlier key bits n (key a.1) := NativeSlot.earlier_mono key bits _ a.1.isLt
    _=NativeSlot.mass key bits (key a.1) := NativeSlot.full key bits _
    _=_ := NamedAperture.measured ends bits (ends a.1)

def partsOf (ends : Fin n→Chord S) (bits : Fin n→ℕ) (s : Fin S) (cap : ℕ)
    (fits : ∀i,bits i≤cap) (U : Widths S) (same : installedWidths ends bits=U) :
    PassiveWindow.Parts ((portGraph S).Port s) (Fin n×Bool) cap (fun p=>U p.val.1) where
  owner:=owner ends s
  base:=base ends bits
  width a:=bits a.1
  within a:=fits a.1
  top := by
    intro a p hp
    unfold owner at hp
    split at hp
    · obtain rfl:=Option.some.inj hp
      rw [←same]
      exact base_top ends bits a
    · contradiction
  covers := by
    intro p j
    let digit : Fin (installedWidths ends bits p.val.1):=j.cast (congrArg (fun W : Widths S => W p.val.1) same).symm
    obtain ⟨u,eqn⟩:=(NamedAperture.chordBits ends bits).surjective ⟨p.val.1,digit⟩
    have key : ends u.1=p.val.1:=(NamedAperture.chord_at ends bits u).symm.trans (congrArg Sigma.fst eqn)
    have offset:=congrArg (fun z : Σ ch,Fin (installedWidths ends bits ch)=>z.2.val) eqn
    have loc : (portGraph S).vertex (ends u.1) p.val.2=s:=by rw [key];exact p.property
    refine ⟨(u.1,p.val.2),?_,u.2,(NamedAperture.offset ends bits u).symm.trans offset⟩
    rw [owner,dite_eq_left loc]
    exact congrArg some (Subtype.ext (Prod.ext key rfl))

variable {row : Row F S H copies} {phys : Fin N→Chord S} (R : RowRouting row phys)
local notation "ends" => Installs.starts (source:=R.source) R.order
local notation "Ty" => Fin (Fintype.card R.Roles)×Bool

def parts (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀i,(Installs.numbered R.order (R.bits c)) i≤cap) :=
  partsOf ends (Installs.numbered R.order (R.bits c)) s cap fits (row.output c) ((Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c))

def word (mid : Fin (middleRoom (Fintype.card R.Roles) cap)→Bool) (q : Ty) (j : Fin cap) :=
  mid (finProdFinEquiv (halfCode q.1 q.2,j))

theorem word_read (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀i,(Installs.numbered R.order (R.bits c)) i≤cap)
    (y : State (row.output c) s) (q : Ty) (p : (portGraph S).Port s)
    (own : (parts R c s cap fits).owner q=some p) (u : Fin ((parts R c s cap fits).width q)) :
    word R (packedMiddle c s (middlePlace R c s cap fits) y) q (u.castLE ((parts R c s cap fits).within q))=
      (y p).val.testBit ((parts R c s cap fits).base q+u.val) := by
  change owner ends s q=some p at own
  unfold owner at own
  split at own
  next loc =>
    obtain rfl:=Option.some.inj own
    have here : (rowGraph ends).vertex q.1 q.2=s := by
      cases side : q.2 <;> simpa only [side,portGraph,rowGraph,PortGraph.vertex] using loc
    exact middle_prefix R c s cap fits y q.1 u q.2 here
  next =>contradiction

/-- A signed socket has one fixed representative on its local physical
half chord. Both the source and the chosen side are independent of its
current live width. -/
def socketPin (rowEnds : Fin n→Chord S) (s : Fin S) (p : (portGraph S).Port s) (j : Fin cap) :
    ((Fin n×Bool)×Fin cap)⊕Bool :=
  if hit : ∃q,owner rowEnds s q=some p then .inl (Classical.choose hit,j) else .inr false

theorem socket_read (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀i,(Installs.numbered R.order (R.bits c)) i≤cap)
    (y : State (row.output c) s) (p : (portGraph S).Port s) (j : Fin cap) :
    let o:=parts R c s cap fits
    Sum.elim (Function.uncurry (ChordAperture.canonical o (fun a=>Nat.testBit (y a).val))) id
      (socketPin ends s p j)=(y p).val.testBit j.val := by
  intro o
  by_cases live:j.val<(row.output c) p.val.1
  · obtain ⟨q,h,_,_⟩:=o.covers p ⟨j.val,live⟩
    have hit : ∃q,owner ends s q=some p:=⟨q,h⟩
    have exactOwner : o.owner (Classical.choose hit)=some p:=Classical.choose_spec hit
    simp [socketPin,hit,ChordAperture.canonical,exactOwner,live]
  · have zero : (y p).val.testBit j.val=false:=
      Nat.testBit_eq_false_of_lt ((y p).isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt live)))
    by_cases hit : ∃q,owner ends s q=some p
    · have exactOwner : o.owner (Classical.choose hit)=some p:=Classical.choose_spec hit
      simp [socketPin,hit,ChordAperture.canonical,exactOwner,live,zero]
    · simp [socketPin,hit,zero]

theorem unplaced_read {k : ℕ} (place : Fin k ↪ Fin S) (c : Histogram (Fin H) copies)
    (i : Fin k) (U : Widths k) (eqn : row.output c=Probe.placeWidths place U)
    (cap : ℕ) (fits : ∀a,(Installs.numbered R.order (R.bits c)) a≤cap) (y : State (row.output c) (place i))
    (p : (portGraph k).Port i) (j : Fin cap) :
    let z:=cast (congrArg (fun Z=>State Z (place i)) eqn) y
    let o:=parts R c (place i) cap fits
    Sum.elim (Function.uncurry (ChordAperture.canonical o (fun a=>Nat.testBit (y a).val))) id
      (socketPin ends (place i) (PhysicalMatrix.port place i p) j)=
      ((PhysicalMatrix.read place U i z) p).val.testBit j.val := by
  intro z o
  let : Nonempty (Fin k) := ⟨i⟩
  rw [socket_read R c (place i) cap fits y (PhysicalMatrix.port place i p) j,
    Probe.named_bit place U i p z j.val]
  have unchanged {T Z : Widths S} (h : T=Z) (val : State T (place i)) (port : (portGraph S).Port (place i)) :
      (val port).val=((cast (congrArg (fun w=>State w (place i)) h) val) port).val := by subst Z;rfl
  exact congrArg (fun x : ℕ=>x.testBit j.val) (unchanged eqn y _)

/-- The local format names the original row and both of its two physical
role digits. No permutation of the placed endpoints is part of the pin map. -/
def localTap {k : ℕ} (localEnds : Fin n→Chord k) (i : Fin k) (p : (portGraph k).Port i)
    (j : Fin cap) (b : Bool) : ((Fin n×Bool)×Fin cap)⊕Bool :=
  if hit : ∃a,localEnds a=p.val.1 then .inl ((Classical.choose hit,b),j) else .inr false

private theorem opposite_ne {k : ℕ} (ch : Chord k) (b : Bool) :
    (portGraph k).vertex ch (!b)≠(portGraph k).vertex ch b := by
  cases b <;>simp [portGraph,PortGraph.vertex,ne_of_lt ch.property,ne_of_gt ch.property]

theorem owner_eq (rowEnds : Fin n→Chord S) (s : Fin S) (a : Fin n×Bool) (p : (portGraph S).Port s) :
    owner rowEnds s a=some p ↔ rowEnds a.1=p.val.1 ∧ a.2=p.val.2 := by
  constructor
  · intro eqn
    unfold owner at eqn
    split at eqn
    · exact Prod.mk.inj (congrArg Subtype.val (Option.some.inj eqn))
    · contradiction
  · rintro ⟨edge,side⟩
    have loc : (portGraph S).vertex (rowEnds a.1) a.2=s:=by rw [edge,side];exact p.property
    rw [owner,dite_eq_left loc]
    exact congrArg some (Subtype.ext (Prod.ext edge side))

theorem code_iff (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀a,(Installs.numbered R.order (R.bits c)) a≤cap) (u q : Ty) :
    ChordAperture.code (parts R c s cap fits) u q ↔
      (portGraph S).vertex (ends u.1) u.2=s ∧ (portGraph S).vertex (ends q.1) q.2=s ∧ ends u.1=ends q.1 := by
  constructor
  · rintro ⟨p,left,right⟩
    obtain ⟨le,ls⟩:=(owner_eq ends s u p).mp left
    obtain ⟨re,rs⟩:=(owner_eq ends s q p).mp right
    exact ⟨by rw [le,ls];exact p.property,by rw [re,rs];exact p.property,le.trans re.symm⟩
  · rintro ⟨left,right,key⟩
    have sides : u.2=q.2 := by
      by_contra neq
      have flip : q.2= !u.2 := by cases hu:u.2 <;>cases hq:q.2 <;>simp_all
      rw [←key,flip] at right
      exact opposite_ne _ _ (right.trans left.symm)
    let p : (portGraph S).Port s:=⟨(ends u.1,u.2),left⟩
    exact ⟨p,(owner_eq ends s u p).mpr ⟨rfl,rfl⟩,(owner_eq ends s q p).mpr ⟨key.symm,sides.symm⟩⟩

theorem sizeAt_fields (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀a,(Installs.numbered R.order (R.bits c)) a≤cap) (u q : Ty) :
    (ChordAperture.sizeAt (parts R c s cap fits) u q).val=
      if (portGraph S).vertex (ends u.1) u.2=s ∧ (portGraph S).vertex (ends q.1) q.2=s ∧ ends u.1=ends q.1
      then (Installs.numbered R.order (R.bits c)) u.1 else 0 := by
  by_cases hit : ChordAperture.code (parts R c s cap fits) u q
  · simp only [ChordAperture.sizeAt,ite_eq_left hit,ite_eq_left ((code_iff R c s cap fits u q).mp hit)];rfl
  · have absent:=mt (code_iff R c s cap fits u q).mpr hit
    simp [ChordAperture.sizeAt,hit,absent]

theorem head_fields (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀a,(Installs.numbered R.order (R.bits c)) a≤cap)
    (u : Ty) (side : Bool) :
    (ChordAperture.head (parts R c s cap fits) u side).val=if side then min cap (base ends (Installs.numbered R.order (R.bits c)) u) else 0 := by
  cases side <;>rfl

theorem room_fields (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ) (fits : ∀a,(Installs.numbered R.order (R.bits c)) a≤cap) (u : Ty) :
    ChordAperture.room (parts R c s cap fits) u=
      if (portGraph S).vertex (ends u.1) u.2=s then row.output c (ends u.1) else 0 := by
  change (owner ends s u).elim 0 (fun p => row.output c p.val.1)=_
  by_cases live : (portGraph S).vertex (ends u.1) u.2=s <;> simp [owner,live]

/-- The physically absent half is zero in every genuine complete gathered
bank. OR therefore recovers the local word regardless of the orientation
of the injective placement, with high bits equal to zero. -/
theorem localTap_read {k : ℕ} (localEnds : Fin (Fintype.card R.Roles)→Chord k)
    (place : Fin k ↪ Fin S) (aligned : ∀a,ends a=Probe.physicalChord place (localEnds a))
    (c : Histogram (Fin H) copies) (i : Fin k) (cap : ℕ) (fits : ∀a,(Installs.numbered R.order (R.bits c)) a≤cap)
    (y : State (row.output c) (place i)) (p : (portGraph k).Port i) (j : Fin cap) :
    let o:=parts R c (place i) cap fits
    let bank:=Function.uncurry (ChordAperture.canonical o (fun a=>Nat.testBit (y a).val))
    let read:=fun b=>Sum.elim bank id (localTap localEnds i p j b)
    (read false || read true)=(y (PhysicalMatrix.port place i p)).val.testBit j.val := by
  intro o bank read
  let phys:=PhysicalMatrix.port place i p
  by_cases hit : ∃a,localEnds a=p.val.1
  · let a:=Classical.choose hit
    let side:=PhysicalMatrix.side place p.val.1 p.val.2
    have key : ends a=phys.val.1:=(aligned a).trans (congrArg (Probe.physicalChord place) (Classical.choose_spec hit))
    have here : (portGraph S).vertex (ends a) side=place i := by rw [key];exact phys.property
    have away : (portGraph S).vertex (ends a) (!side)≠place i:=by rw [←here];exact opposite_ne _ _
    have yes : o.owner (a,side)=some phys := by
      change owner ends (place i) (a,side)=some phys
      rw [owner,dite_eq_left here]
      exact congrArg some (Subtype.ext (Prod.ext key rfl))
    have no : o.owner (a,!side)=none := by
      change owner ends (place i) (a,!side)=none
      simp [owner,away]
    have missing : read (!side)=false:=by
      change Sum.elim bank id (localTap localEnds i p j (!side))=false
      rw [localTap,dite_eq_left hit]
      change ChordAperture.canonical o (fun port=>Nat.testBit (y port).val) (a,!side) j=false
      simp [ChordAperture.canonical,no]
    have found : read side=(y phys).val.testBit j.val:=by
      change Sum.elim bank id (localTap localEnds i p j side)=_
      rw [localTap,dite_eq_left hit]
      change ChordAperture.canonical o (fun port=>Nat.testBit (y port).val) (a,side) j=_
      rw [ChordAperture.canonical,yes,Option.elim_some]
      split
      · rfl
      · exact (Nat.testBit_eq_false_of_lt ((y phys).isLt.trans_le (Nat.pow_le_pow_right (by decide)
          (Nat.le_of_not_gt (by assumption))))).symm
    change (read false || read true) = (y phys).val.testBit j.val
    cases orient : side <;> simp [orient] at found missing <;> simp [found,missing]
  · have absent : ¬∃q,owner ends (place i) q=some phys := by
      rintro ⟨⟨a,b⟩,record⟩
      unfold owner at record
      split at record
      next loc =>
        have key:=congrArg (fun port : (portGraph S).Port (place i)=>port.val.1) (Option.some.inj record)
        exact hit ⟨a,PhysicalMatrix.edge_injective place ((aligned a).symm.trans key)⟩
      next =>contradiction
    have rd:=socket_read R c (place i) cap fits y phys j
    simp [socketPin,absent] at rd
    simpa [read,localTap,hit] using rd

section OrientationCircuit
variable {V I : Type} [Fintype V] [Fintype I] (taps : I→Bool→V⊕Bool)
private def orWeight (x : Bool⊕Unit→Bool) : F :=
  if x (.inr ())=(x (.inl false)||x (.inl true)) then 1 else 0

private def orPins (i : I) : Bool⊕Unit → (V⊕I)⊕Bool
  | .inl b=>Sum.map Sum.inl id (taps i b)
  | .inr _=>.inl (.inr i)

private def orGates : BitNetwork F (Fintype.card (V⊕I)) :=
  WideHost.localFamily (fun _ : I=>TypedWiring.localTable (orWeight (F:=F))) (orPins taps)

def orient (consumer : BitNetwork F (Fintype.card (V⊕I))) : BitNetwork F (Fintype.card V) :=
  TypedWiring.glue (fun b : Bool=>if b then consumer else orGates taps) (fun _ bit=>bit)

def merged (v : V→Bool) (i : I) := (Sum.elim v id (taps i false)||Sum.elim v id (taps i true))

private theorem orGates_value (v : V→Bool) (z : I→Bool) :
    TypedWiring.value (F:=F) (orGates taps) (Sum.elim v z)=if z=merged taps v then 1 else 0 := by
  rw [orGates,WideHost.localFamily_eval]
  have peel (x : V⊕Bool) : Sum.elim (Sum.elim v z) id (Sum.map Sum.inl id x)=Sum.elim v id x := by
    cases x <;>rfl
  simp only [TypedWiring.localTable_value,orWeight,Function.comp_apply,orPins,Sum.elim_inl,Sum.elim_inr,peel,
    Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h=>funext h,fun h i=>congrFun h i⟩

theorem orient_value (consumer : BitNetwork F (Fintype.card (V⊕I))) (v : V→Bool) :
    TypedWiring.value (orient taps consumer) v=TypedWiring.value consumer (Sum.elim v (merged taps v)) := by
  rw [orient,TypedWiring.glue_value]
  change (∑z : I→Bool,∏b : Bool,TypedWiring.value (if b then consumer else orGates taps) (Sum.elim v z))=_
  simp only [Fintype.prod_bool,Bool.false_eq_true,ite_false,ite_true,orGates_value,mul_ite,mul_one,mul_zero]
  simp

theorem orient_cost (consumer : BitNetwork F (Fintype.card (V⊕I))) :
    (orient taps consumer).cells+(orient taps consumer).internal=73*Fintype.card I+(consumer.cells+consumer.internal) := by
  have single : (TypedWiring.localTable (orWeight (F:=F))).cells+(TypedWiring.localTable (orWeight (F:=F))).internal=72 := by
    simp [TypedWiring.localTable,TableCompiler.localTableNetwork_cells,TableCompiler.localTableNetwork_internal]
  have gates : (orGates (F:=F) taps).cells+(orGates (F:=F) taps).internal=Fintype.card I*72 := by
    rw [orGates,WideHost.localFamily_size]
    simp [single]
  simp only [orient,TypedWiring.glue_internal,TypedWiring.glue_cells,Fintype.sum_bool,
    Bool.false_eq_true,ite_true,ite_false]
  omega
end OrientationCircuit

section PackedGather
variable {V : Type} [Fintype V] {bits : ℕ}
local notation "Role" => Fin n×Bool
local notation "Pins" => BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits cap) (BinaryBarrelTurns.digits cap) cap
local notation "LenBits" => Fin (BinaryBarrelTurns.digits cap)
variable (lengthPin : (Fin n × Bool) × (Fin n × Bool) → Fin (BinaryBarrelTurns.digits cap) → V⊕Bool)
    (startPin : (Fin n × Bool) → Bool → Fin (BinaryBarrelTurns.digits cap) → V⊕Bool)
    (middlePin : Fin (middleRoom n cap)→V⊕Bool) (roomPin : (Fin n × Bool) → Fin bits → V)

def cut (r : Role×Role) : Pins→(V⊕(Role×Fin cap))⊕Bool
  | .inl b=>Sum.map Sum.inl id (lengthPin r b)
  | .inr (side,.inl b)=>Sum.map Sum.inl id (startPin r.1 side b)
  | .inr (false,.inr b)=>Sum.map Sum.inl id (middlePin (finProdFinEquiv (halfCode r.1.1 r.1.2,b)))
  | .inr (true,.inr b)=>.inl (.inr (r.2,b))

def packetGather (consumer : BitNetwork F (Fintype.card (V⊕(Role×Fin cap)))) : BitNetwork F (Fintype.card V) :=
  ChordAperture.attach (cut lengthPin startPin middlePin) roomPin consumer

theorem packetGather_cost (consumer : BitNetwork F (Fintype.card (V⊕(Role×Fin cap)))) :
    let net : BitNetwork F (Fintype.card V) :=packetGather lengthPin startPin middlePin roomPin consumer
    net.cells+net.internal≤(n*2)*cap+(n*2)*(cap*(200*bits+65))+
      (n*2)*(n*2)*(2308*cap*(cap.log2+2))+(consumer.cells+consumer.internal) := by
  simpa [packetGather] using (ChordAperture.attach_cost (F:=F) (cut lengthPin startPin middlePin) roomPin consumer)
end PackedGather

variable {V : Type} [Fintype V] {bits : ℕ}
local notation "HS" => Ty×Fin cap
local notation "LenBits" => Fin (BinaryBarrelTurns.digits cap)
variable (lengthPin : (Fin (Fintype.card R.Roles) × Bool) × (Fin (Fintype.card R.Roles) × Bool) → Fin (BinaryBarrelTurns.digits cap) → V⊕Bool)
    (startPin : (Fin (Fintype.card R.Roles) × Bool) → Bool → Fin (BinaryBarrelTurns.digits cap) → V⊕Bool)
    (middlePin : Fin (middleRoom (Fintype.card R.Roles) cap)→V⊕Bool) (roomPin : (Fin (Fintype.card R.Roles) × Bool) → Fin bits → V)
    (consumer : BitNetwork F (Fintype.card (V⊕((Fin (Fintype.card R.Roles) × Bool) × Fin cap)))) (v : V→Bool)
    (c : Histogram (Fin H) copies) (s : Fin S) (fits : ∀a,Installs.numbered R.order (R.bits c) a≤cap) (y : State (row.output c) s)
local notation "o" => parts R c s cap fits

theorem packetGather_value (allFit : ∀p : (portGraph S).Port s,(row.output c) p.val.1≤cap)
    (columns : cap≤2^bits) (roomFit : ∀q,ChordAperture.room o q<2^bits)
    (sizeRead : ∀i q b,Sum.elim v id (lengthPin (i,q) b)=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.sizeAt o i q)) b)
    (headRead : ∀i side b,Sum.elim v id (startPin i side b)=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.head o i side)) b)
    (widthRead : ∀q j,v (roomPin q j)=TraceWords.bits (⟨ChordAperture.room o q,roomFit q⟩ : Word bits) j)
    (middleRead : ∀j,Sum.elim v id (middlePin j)=packedMiddle c s (middlePlace R c s cap fits) y j) :
    TypedWiring.value (packetGather lengthPin startPin middlePin roomPin consumer) v=
      TypedWiring.value consumer (Sum.elim v (Function.uncurry (ChordAperture.canonical o (fun p=>Nat.testBit (y p).val)))) := by
  apply ChordAperture.attach_value o allFit _ roomPin consumer v (fun p=>Nat.testBit (y p).val)
    (word R (packedMiddle c s (middlePlace R c s cap fits) y)) (word_read R c s cap fits y) columns roomFit widthRead
  intro bank i q
  have peel (x : V⊕Bool) : Sum.elim (Sum.elim v bank) id (Sum.map Sum.inl id x)=Sum.elim v id x := by cases x <;>rfl
  funext p
  rcases p with b|⟨side,b|b⟩
  · exact (peel _).trans (sizeRead i q b)
  · exact (peel _).trans (headRead i side b)
  · cases side
    · exact (peel _).trans (middleRead _)
    · rfl

section LocalDevice
variable {k n : ℕ} (localEnds : Fin n→Chord k) (i : Fin k)
local notation "Pin" => (portGraph k).Port i×Fin cap
local notation "Role" => Fin n×Bool
local notation "Pool" => Role×Fin cap
local notation "Len" => Fin (BinaryBarrelTurns.digits cap)
variable (lengthPin : (Fin n × Bool) × (Fin n × Bool) → Fin (BinaryBarrelTurns.digits cap) → V⊕Bool)
    (startPin : (Fin n × Bool) → Bool → Fin (BinaryBarrelTurns.digits cap) → V⊕Bool)
    (middlePin : Fin (middleRoom n cap)→V⊕Bool) (roomPin : (Fin n × Bool) → Fin bits → V)
    (use : BitNetwork F (Fintype.card (V⊕((portGraph k).Port i × Fin cap))))

private def narrow : BitNetwork F (Fintype.card ((V⊕Pool)⊕Pin)) :=
  WideHost.localFamily (fun _ : Unit=>use) (fun _ a=>.inl (Sum.map Sum.inl id a))

/-- One fixed local strip-format program converts the old signed output slab
to its original, unplaced socket order. All dynamic operands arrive as
ordinary pins to the width/prefix barrels and the packed middle. -/
def packetOrient : BitNetwork F (Fintype.card V) :=
  packetGather lengthPin startPin middlePin roomPin <|
    orient (fun u side=>Sum.map Sum.inr id (localTap localEnds i u.1 u.2 side)) (narrow (n:=n) i use)

theorem packetOrient_cost :
    let net : BitNetwork F (Fintype.card V) :=packetOrient localEnds i lengthPin startPin middlePin roomPin use
    net.cells+net.internal≤(n*2)*cap+(n*2)*(cap*(200*bits+65))+(n*2)*(n*2)*(2308*cap*(cap.log2+2))+
      (73*(Fintype.card ((portGraph k).Port i)*cap)+(use.cells+use.internal)) := by
  intro net
  have trim : (narrow (n:=n) i use).cells+(narrow (n:=n) i use).internal=use.cells+use.internal := by
    rw [narrow,WideHost.localFamily_size];simp
  have bound:=packetGather_cost lengthPin startPin middlePin roomPin
    (orient (fun u side=>Sum.map Sum.inr id (localTap localEnds i u.1 u.2 side)) (narrow (n:=n) i use))
  simpa only [net,packetOrient,orient_cost,trim,Fintype.card_prod,Fintype.card_fin] using bound

end LocalDevice

variable {k : ℕ} (localEnds : Fin (Fintype.card R.Roles)→Chord k) (place : Fin k ↪ Fin S) (i : Fin k)
    (aligned : ∀a,Installs.starts (source:=R.source) R.order a=Probe.physicalChord place (localEnds a))
    (use : BitNetwork F (Fintype.card (V⊕((portGraph k).Port i×Fin cap))))
    (yy : State (row.output c) (place i))
local notation "oi" => parts R c (place i) cap fits

include aligned in
theorem packetOrient_value (U : Widths k) (eqn : row.output c=Probe.placeWidths place U)
    (allFit : ∀p : (portGraph S).Port (place i),(row.output c) p.val.1≤cap)
    (columns : cap≤2^bits) (roomFit : ∀q,ChordAperture.room oi q<2^bits)
    (sizeRead : ∀u q b,Sum.elim v id (lengthPin (u,q) b)=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.sizeAt oi u q)) b)
    (headRead : ∀u side b,Sum.elim v id (startPin u side b)=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.head oi u side)) b)
    (widthRead : ∀q j,v (roomPin q j)=TraceWords.bits (⟨ChordAperture.room oi q,roomFit q⟩ : Word bits) j)
    (middleRead : ∀j,Sum.elim v id (middlePin j)=packedMiddle c (place i) (middlePlace R c (place i) cap fits) yy j) :
    let z:=cast (congrArg (fun Z=>State Z (place i)) eqn) yy
    TypedWiring.value (packetOrient localEnds i lengthPin startPin middlePin roomPin use) v=
      TypedWiring.value use (Sum.elim v (fun t=>((PhysicalMatrix.read place U i z) t.1).val.testBit t.2.val)) := by
  intro z
  let : Nonempty (Fin k) := ⟨i⟩
  unfold packetOrient
  rw [packetGather_value R lengthPin startPin middlePin roomPin _ v c (place i) fits yy allFit columns
    roomFit sizeRead headRead widthRead middleRead,orient_value,narrow,WideHost.localFamily_eval]
  simp only [Fintype.prod_unique]
  apply congrArg (TypedWiring.value use)
  funext u
  rcases u with a|⟨p,j⟩
  · rfl
  · let bank:=Function.uncurry (ChordAperture.canonical oi (fun p=>Nat.testBit (yy p).val))
    have peel (a : HS⊕Bool) : Sum.elim (Sum.elim v bank) id (Sum.map Sum.inr id a)=Sum.elim bank id a := by cases a <;>rfl
    change (Sum.elim (Sum.elim v bank) id (Sum.map Sum.inr id (localTap localEnds i p j false)) ||
      Sum.elim (Sum.elim v bank) id (Sum.map Sum.inr id (localTap localEnds i p j true)))=_
    rw [peel,peel,localTap_read R localEnds place aligned c i cap fits yy p j]
    change (yy (PhysicalMatrix.port place i p)).val.testBit j.val = (PhysicalMatrix.read place U i z p).val.testBit j.val
    rw [Probe.named_bit]
    have same {T Z : Widths S} (h : T=Z) (t : State T (place i)) (p : (portGraph S).Port (place i)) :
        (t p).val=((cast (congrArg (fun w=>State w (place i)) h) t) p).val := by subst Z;rfl
    exact congrArg (fun a : ℕ=>a.testBit j.val) (same eqn yy _)

end Hierarchy.WireTelescope.ChosenPackets.RowRouting.Middle
end

end OAI
