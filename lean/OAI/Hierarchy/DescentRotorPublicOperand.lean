import OAI.Hierarchy.DescentRotorFlatPhysical
import OAI.Hierarchy.DescentOrderedRotorDigits
import OAI.Hierarchy.DescentRotorWindowArchive

namespace OAI
/-! # The selected public rotor tap on its original sorted old occurrence -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates
open DescentBaseProfile DescentCommonHost DescentHostDirectory DescentDenseHostOrder DescentResetHostSize DescentResetLaneIssue
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G
local notation "H₀" => Physical.host G.arcs 0 0 0 0 0

/-- The first private lane of a selected tap precedes the public lane, even when
the affine spine uses several p-word arguments. -/
structure Mouth (n : ℕ) where
  pin : Bool
  vertex : Fin (2^n)
  layer : ℕ
  batch : ℕ
  digit : ℕ
  within : ℕ

def publicTap (mult layers p node arg : ℕ) : (Q).Site→Option (Mouth n)
  | ⟨_,.inl _⟩=>none
  | ⟨v,.inr i⟩=>
    let order:=tapOrder layers C.batches (C.subrow G mult v) i
    if live : node<Fintype.card (SpineRow (r:=layers) (m:=C.batches) (C.subrow G mult v) ⊕
        Block layers C.batches (C.subrow G mult v i)) then
      match order.symm ⟨node,live⟩ with
      | .inl _=>none
      | .inr t=>
        match name H₀ v i with
        | .inr _=>none
        | .inl (vertex,pin)=>
          let back:=C.spineReference G mult layers p v i true ⟨i,t⟩
          let offset_:=back.count G C mult layers p
          if offset_≤arg then some ⟨pin,vertex,t.1.val,t.2.1.val,t.2.2.val,arg-offset_⟩ else none
    else none

theorem public_tap_at (mult layers p : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v))
    (t : Block layers C.batches (C.subrow G mult v i)) (vertex : Fin (2^n)) (pin : Bool)
    (socket : name H₀ v i=.inl (vertex,pin)) (digit : ℕ) :
    let back:=C.spineReference G mult layers p v i true ⟨i,t⟩
    C.publicTap G mult layers p (tapOrder layers C.batches (C.subrow G mult v) i (.inr t)).val
      (back.count G C mult layers p+digit) ⟨v,.inr i⟩=
      some ⟨pin,vertex,t.1.val,t.2.1.val,t.2.2.val,digit⟩ :=by
  simp [publicTap,socket]
  simpa using (tapOrder layers C.batches (C.subrow G mult v) i (.inr t)).isLt


def public_selector (mult p node arg : ℕ) (x : Fin 4→Cell C.fieldBits) :
    Option (Bool×Code C.residual×Mouth n) :=do
  guard ((x 1).val>0 ∧ (x 2).val%2=0)
  if hit : (x 3).val<(roster G C.residual C.depth).card then
    match ((DescentResetTrunkPalette.order G C.residual C.depth).symm ⟨(x 3).val,hit⟩).val with
    | .good side z actor=>
      let root:=((x 1).val-1,z.2)
      if fresh : root∈codes C.residual then
        let req←C.publicTap G mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) p node arg actor
        return (side,⟨root,fresh⟩,req)
      else none
    | _=>none
  else none

theorem public_selector_at (mult p node arg : ℕ) (x : Fin 4→Cell C.fieldBits) (side : Bool) (key : Code C.residual)
    (v : (Q).Site) (shape : ↥(roster G C.residual C.depth)) (req : Mouth n)
    (depth : (x 1).val=key.val.1+1) (safe : (x 2).val%2=0)
    (seen : (x 3).val=(localRank G C.residual C.depth shape).val) (good : shape.val=.good side ((),key.val.2) v)
    (socket : C.publicTap G mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) p node arg v=some req) :
    C.public_selector G mult p node arg x=some (side,key,req) :=by
  have real : (x 3).val<(roster G C.residual C.depth).card:=seen ▸ (localRank G C.residual C.depth shape).isLt
  have actual : (⟨(x 3).val,real⟩ : Fin (roster G C.residual C.depth).card)=
      DescentResetTrunkPalette.order G C.residual C.depth shape:=Fin.ext seen
  simp [public_selector,safe,depth,real,actual,good,key.property,socket]

/-- Evaluate the original packet scheduler on a physical old rail's ordered cell
serial. Ghost packets and digits outside the matrix get no ticket. -/
def schedule (packet layers : ℕ) (matrix : Fin (2^n)→Fin (2^n)→ℕ)
    (src dst : Fin (2^n)) (rank : ℕ) : Option (ℕ×ℕ) :=
  if positive : 0<packet then
    if valid : rank/packet<groups packet (matrix src dst) then
      let q : Packet packet matrix:=⟨src,dst,⟨rank/packet,valid⟩⟩
      some ((Scheduler.color (Scheduler.matrixRun packet (layers/2) matrix) (Scheduler.packetIDs matrix positive q)).val,rank%packet)
    else none
  else none

variable {E F : Type} [Field F] [Fintype E] {packet u mult cap : ℕ} {hp : 0<packet}
    {src dst : E→Fin (2^n)} {pay : ℝ} (P : BaseCircuit F G mult packet u hp src dst pay)
    (key : E↪Fin cap)
local notation "ordered" => Ordered.orderedAddress key src dst hp
local notation "serial" e => (Ordered.ordinal key src dst (src e,dst e) ((Ordered.cells src dst e).2)).val

theorem scheduled_old (e : E) :
    schedule packet P.layers (matrixOfBundles src dst) (src e) (dst e) (serial e)=
      some ((P.choose (ordered e).1).val,(ordered e).2.val) :=by
  obtain ⟨L,count,yes,_⟩:=P.scheduled
  have halves : P.layers/2=L:=by omega
  have pos:=(Ordered.orderedAddress_read key src dst hp e).1
  have bit:=(Ordered.orderedAddress_read key src dst hp e).2
  have small : (serial e)/packet<groups packet (matrixOfBundles src dst (src e) (dst e)):=pos ▸ (ordered e).1.2.2.isLt
  simp only [schedule,dite_eq_left hp,dite_eq_left small]
  have layer:=congrArg Fin.val (yes (ordered e).1)
  have identify : (⟨src e,dst e,⟨(serial e)/packet,small⟩⟩ : Packet packet (matrixOfBundles src dst))=(ordered e).1 :=rfl
  rw [identify]
  apply congrArg some
  apply Prod.ext _ bit.symm
  apply Eq.trans _ layer.symm
  exact congrArg (fun l => (Scheduler.color (Scheduler.matrixRun packet l (matrixOfBundles src dst))
    (Scheduler.packetIDs (matrixOfBundles src dst) hp (ordered e).1)).val) halves

theorem realized_focus (dir : Bool) (e : E) :
    let site:=if dir then dst else src
    let slot:=fun q : Packet packet (matrixOfBundles src dst)=>(P.choose q,if dir then q.2.1 else q.1)
    let agree : ∀z,(slot (ordered z).1).2=site z:=by intro z;cases dir <;> rfl
    Ordered.focus ordered slot site agree (P.choose (ordered e).1) (site e) (ordered e).2=.inr ⟨e,rfl⟩ :=by
  intro site slot agree
  apply Ordered.focus_used
  · exact Ordered.orderedAddress_injective key src dst hp
  · intro q t same
    have level : P.choose q=P.choose t:=congrArg Prod.fst same
    apply P.proper q t level
    cases dir with
    | false=>exact congrArg Prod.snd same
    | true=>
      have target : q.2.1=t.2.1:=congrArg Prod.snd same
      apply (P.rotation (P.choose q)).injective
      calc
        _=q.2.1:=P.routed q
        _=t.2.1:=target
        _=_:=by rw [level];exact (P.routed t).symm

/-- The check is executable on a preceding physical rail: its admitted (source,destination)
cell, ordinal in that cell, and matrix all come from the prior roster. -/
def railMatch (packet layers : ℕ) (traffic : Fin (2^n)→Fin (2^n)→ℕ)
    (req : Mouth n) (src dst : Fin (2^n)) (rank : ℕ) : Prop :=
  (if req.pin then dst else src)=req.vertex ∧
    schedule packet layers traffic src dst rank=some (req.layer,req.digit)

theorem matches_iff (req : Mouth n) (e : E) :
    railMatch packet P.layers (matrixOfBundles src dst) req (src e) (dst e) (serial e) ↔
      (if req.pin then dst e else src e)=req.vertex ∧
      (P.choose (ordered e).1).val=req.layer ∧ (ordered e).2.val=req.digit :=by
  rw [railMatch,scheduled_old G P key e]
  simp

theorem matches_unique (req : Mouth n) (e f : E)
    (first : railMatch packet P.layers (matrixOfBundles src dst) req (src e) (dst e) (serial e))
    (second : railMatch packet P.layers (matrixOfBundles src dst) req (src f) (dst f) (serial f)) : e=f :=by
  obtain ⟨v₁,r₁,j₁⟩:=(matches_iff G P key req e).mp first
  obtain ⟨v₂,r₂,j₂⟩:=(matches_iff G P key req f).mp second
  have layer : P.choose (ordered e).1=P.choose (ordered f).1:=Fin.ext (r₁.trans r₂.symm)
  have source : src e=src f:=by
    by_cases dir : req.pin=true
    · have dstEq : dst e=dst f:=by simpa [dir] using v₁.trans v₂.symm
      apply (P.rotation (P.choose (ordered e).1)).injective
      calc
        _=dst e:=P.routed (ordered e).1
        _=dst f:=dstEq
        _=_:=by rw [layer];exact (P.routed (ordered f).1).symm
    · simpa [dir] using v₁.trans v₂.symm
  apply Ordered.orderedAddress_injective key src dst hp
  exact Prod.ext (P.proper _ _ layer source) (Fin.ext (j₁.trans j₂.symm))

/-- A missing matched row leaves only the model's fixed rotor padding. -/
theorem focus_missing {A «Q» R V : Type} {w : ℕ} (addr : A→«Q»×Fin w) (slot : «Q»→R×V) (origin : A→V)
    (agrees : ∀e,(slot (addr e).1).2=origin e) (r : R) (v : V) (digit : Fin w)
    (absent : ∀e,slot (addr e).1=(r,v)→(addr e).2≠digit) :
    ∃b,Ordered.focus addr slot origin agrees r v digit=.inl b :=by
  unfold Ordered.focus
  split
  next row=>
    have empty : ¬∃e,addr e=(row.choose,digit):=by
      rintro ⟨e,eqn⟩
      exact absent e ((congrArg slot (congrArg Prod.fst eqn)).trans row.choose_spec) (congrArg Prod.snd eqn)
    rw [dite_eq_right empty]
    exact ⟨_,rfl⟩
  next=>exact ⟨_,rfl⟩

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
