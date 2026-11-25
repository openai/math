import OAI.Hierarchy.DescentRotorOperandQueryROM
import OAI.Hierarchy.DescentResetTrunkPalette
import OAI.Hierarchy.DescentBatchedNodeOrder
import OAI.Hierarchy.DescentDenseHostOrder
import OAI.Hierarchy.DescentResetPublicShapeSelf

namespace OAI
/-! # Selecting a private rotor socket independently in each packed receiver -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPackedZip DescentDenseHostOrder DescentResetHostSize DescentPhysicalSplit
open DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost DescentHostDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor board
local notation "H₀" => Physical.host board.arcs 0 0 0 0 0
local notation "P" => ↥(roster board C.residual C.depth)
local notation "Entry" => Bool×(Q).Edge×ℕ

/-- Subrow widths of the trivalent template are independent of the installed layer count. -/
def subrow (mult : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v)) : ℕ :=
  match name H₀ v i with
  | .inl _=>C.packet
  | .inr _=>mult*C.packet

/-- At a mixed reset site the old cap determines the local operation order, including the
individual block of a spine row. Selectors whose second operand is a public socket are left
for the public-contact issuer. -/
def socket (mult layers node arg : ℕ) : (Q).Site→Option Entry
  | ⟨v,.inl false⟩=>if node<layers*C.batches ∧ arg<Fintype.card (RowBit board.arcs mult C.packet v) then some (false,.inr ⟨v,0⟩,node) else none
  | ⟨_,.inl true⟩=>none
  | ⟨v,.inr i⟩=>
    let order:=tapOrder layers C.batches (C.subrow board mult v) i
    if live : node<Fintype.card (SpineRow (r:=layers) (m:=C.batches) (C.subrow board mult v) ⊕
        Block layers C.batches (C.subrow board mult v i)) then
      match order.symm ⟨node,live⟩ with
      | .inl ⟨_,rr,b,_⟩=>
        if arg<2 then some (decide (arg=0),.inr ⟨v,if arg=0 then i.castSucc else i.succ⟩,rr.val*C.batches+b.val) else none
      | .inr (rr,b,_)=>if arg=0 then some (true,.inr ⟨v,i.castSucc⟩,rr.val*C.batches+b.val)
        else if arg=1 then match name H₀ v i with
          | .inl _=>none
          | .inr (e,dir)=>some (dir,.inl e,rr.val*C.batches+b.val)
        else none
    else none

theorem root_socket (mult layers : ℕ) (v : Fin (2^n)) (r : Fin layers) (b : Fin C.batches)
    (a : Fin (Fintype.card (RowBit board.arcs mult C.packet v))) :
    C.socket board mult layers (r.val*C.batches+b.val) a.val ⟨v,.inl false⟩=
      some (false,.inr ⟨v,0⟩,r.val*C.batches+b.val) := by
  have upper:=Nat.mul_le_mul_right C.batches r.isLt
  rw [Nat.succ_mul] at upper
  have row : r.val*C.batches+b.val<layers*C.batches:=(Nat.add_lt_add_left b.isLt _).trans_le upper
  simp only [socket]
  split
  · rfl
  · rename_i rejected
    apply False.elim
    apply rejected
    refine ⟨row,?_⟩
    have sameCard {α : Type} (first second : Fintype α) :
        @Fintype.card α first = @Fintype.card α second :=
      congrArg (@Fintype.card α) (Subsingleton.elim first second)
    apply Nat.lt_of_lt_of_eq a.isLt
    apply sameCard

theorem spine_socket (mult layers : ℕ) (v : Fin (2^n)) (i j : Fin (DescentPhysicalSplit.count H₀ v))
    (t : Block layers C.batches (C.subrow board mult v j)) (a : Fin 2) :
    C.socket board mult layers (tapOrder layers C.batches (C.subrow board mult v) i (.inl ⟨j,t⟩)).val a.val ⟨v,.inr i⟩=
      some (decide (a.val=0),.inr ⟨v,if a.val=0 then i.castSucc else i.succ⟩,t.1.val*C.batches+t.2.1.val) := by
  have live := (tapOrder layers C.batches (C.subrow board mult v) i (.inl ⟨j,t⟩)).isLt
  have decoded : (tapOrder layers C.batches (C.subrow board mult v) i).symm ⟨_,live⟩=.inl ⟨j,t⟩ :=
    (tapOrder layers C.batches (C.subrow board mult v) i).symm_apply_apply _
  simp only [socket,dite_eq_left live,decoded,ite_eq_left a.isLt]

theorem selector_socket (mult layers : ℕ) (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H₀ v))
    (t : Block layers C.batches (C.subrow board mult v i)) (a : ℕ) :
    C.socket board mult layers (tapOrder layers C.batches (C.subrow board mult v) i (.inr t)).val a ⟨v,.inr i⟩=
      (if a=0 then some (true,.inr ⟨v,i.castSucc⟩,t.1.val*C.batches+t.2.1.val)
       else if a=1 then match name H₀ v i with
        | .inl _=>none
        | .inr (e,dir)=>some (dir,.inl e,t.1.val*C.batches+t.2.1.val)
       else none) := by
  have live := (tapOrder layers C.batches (C.subrow board mult v) i (.inr t)).isLt
  have decoded : (tapOrder layers C.batches (C.subrow board mult v) i).symm ⟨_,live⟩=.inr t :=
    (tapOrder layers C.batches (C.subrow board mult v) i).symm_apply_apply _
  simp only [socket,dite_eq_left live,decoded]

def registers (x : Fin 4→Cell C.fieldBits) (i : Fin 3) :=x i.castSucc

/-- The input words are old capacity, observed depth plus one, selected stencil and actual
compact receiver shape. The shape contains the real rotor vertex and tap socket. -/
def mixedLaw (mult node arg : ℕ) (x : Fin 4→Cell C.fieldBits) : Cell C.queryBits :=
  if present : (x 1).val>0 ∧ (x 3).val<(roster board C.residual C.depth).card then
    match ((DescentResetTrunkPalette.order board C.residual C.depth).symm ⟨(x 3).val,present.2⟩).val with
    | .good s z v=>
      let root:=((x 1).val-1,z.2)
      if allowed : root∈codes C.residual then
        let layers:=DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val
        match C.socket board mult layers node arg v with
        | some (face,e,addr)=>if safe : addr<C.addresses then
            C.value board (s,face,⟨root,allowed⟩,e,⟨addr,safe⟩) (C.registers x) else 0
        | none=>0
      else 0
    | _=>0
  else 0

theorem mixed_good (mult node arg : ℕ) (x : Fin 4→Cell C.fieldBits) (code : Code C.residual)
    (s face : Bool) (shape : P) (v : (Q).Site) (e : (Q).Edge) (addr : Fin C.addresses)
    (atShape : (x 3).val=(localRank board C.residual C.depth shape).val)
    (good : shape.val=.good s ((),code.val.2) v) (depth : (x 1).val=code.val.1+1)
    (where_ : C.socket board mult (DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val) node arg v=
      some (face,e,addr.val)) :
    C.mixedLaw board mult node arg x=C.value board (s,face,code,e,addr) (C.registers x) := by
  have real : (x 3).val<(roster board C.residual C.depth).card:=atShape ▸ (localRank board C.residual C.depth shape).isLt
  have known : (⟨(x 3).val,real⟩ : Fin (roster board C.residual C.depth).card)=
      DescentResetTrunkPalette.order board C.residual C.depth shape:=Fin.ext atShape
  have active : code.val.1+1>0 ∧ (x 3).val<(roster board C.residual C.depth).card := ⟨Nat.zero_lt_succ _,real⟩
  simp only [mixedLaw,depth,dite_eq_left active,known,Equiv.symm_apply_apply,good,Nat.add_sub_cancel,
    Prod.mk.eta,code.property,dite_eq_left,where_,addr.isLt]

def mixedBook (mult slots nodes : ℕ) (j : Fin (slots*nodes)) :=
  C.mixedLaw board mult (finProdFinEquiv.symm j : Fin slots×Fin nodes).2.val
    (finProdFinEquiv.symm j : Fin slots×Fin nodes).1.val

theorem mixed_index (mult : ℕ) {slots nodes : ℕ} (a : Fin slots) (node : Fin nodes) :
    C.mixedBook board mult slots nodes (finProdFinEquiv (a,node))=C.mixedLaw board mult node.val a.val:=by
  simp [mixedBook]

def mixedExpr (mult slots nodes base : ℕ) (j : Fin (slots*nodes)) (old : Fin 4→Expr) :=
  DescentOperandFamilyBook.expr (C.mixedBook board mult slots nodes) C.lanes base j old

theorem mixed_issued {H G w : ℕ} (mult slots nodes base : ℕ) (a : Fin slots) (node : Fin nodes) (old : Fin 4→Expr) (mem : Memory w)
    (x : Fin H→Fin G→Fin 4→Cell C.fieldBits) (held : ∀j,(old j).Fits w base)
    (prior : ∀j,Source (old j) (fun v g=>x v g j) C.lanes mem)
    (room : DescentOperandFamilyBook.endAddress (slots*nodes) 4 C.fieldBits C.lanes base<2^w) :
    (C.mixedExpr board mult slots nodes base (finProdFinEquiv (a,node)) old).Fits w
        (DescentOperandFamilyBook.endAddress (slots*nodes) 4 C.fieldBits C.lanes base) ∧
    Source (C.mixedExpr board mult slots nodes base (finProdFinEquiv (a,node)) old)
      (fun v g=>C.mixedLaw board mult node.val a.val (x v g)) C.lanes
      (DescentOperandFamilyBook.image (C.mixedBook board mult slots nodes) C.lanes base mem) := by
  have dead (j) : C.mixedBook board mult slots nodes j (fun _=>0)=0:=by simp [mixedBook,mixedLaw]
  simpa only [mixedExpr,mixed_index] using DescentOperandFamilyBook.issued (C.mixedBook board mult slots nodes)
    dead C.lanes base (finProdFinEquiv (a,node)) old mem x held prior room

end
end Hierarchy.DescentRotorOperandQueryROM.Shape

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentCommonHost DescentDenseHostOrder
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)

theorem installed_rotor_shape (s : Bool) (g : Z.placement.Good) (v : (DescentCommonPalette.rotor Z.graph).Site) :
    (Z.localShape T (Z.placed T (Z.rotorSiteAt T s g v))).val=.good s ((),(Z.goodLabel T g).val.2) v := by
  let equiv := DescentCommonPalette.rotorSiteEquiv Z.graph d
    (DescentChosenRouter.selectedRotorLayers Z.placement Z.graph Z.positive Z.pay Z.circuit s g) C Z.width Z.unit
  let site : (Bool × Z.Fallback) ⊕ Z.bank.Site := .inr ⟨(s,.inl g),equiv v⟩
  let name := rawName Z.placement Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d
  refine (congrArg (fun z => shape Z.graph (name z)) ((Z.resetNames T).apply_symm_apply site)).trans ?_
  exact congrArg (Node.good s ((),(Z.goodLabel T g).val.2)) (equiv.symm_apply_apply v)
end
end Hierarchy.DescentSixParty.ResetInput


namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster DescentRotorOperandTicket
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n



open DescentNextSignedWindow
local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding

open DescentRotorOperandQueryROM DescentSIMDLookup DescentDenseHostOrder
/-- A dated lane uses its true compact host shape at this receiver. Its other three registers
are the genuine preceding cap, interval depth and approved occupancy stencil. -/
theorem mixed_rotor_query_at {p₀ field target lanes span : ℕ} (proof : B.Recorded p₀) (u : Host)
    (s : Bool) (g₀ : (placement).Good) (site : (DescentCommonPalette.rotor (Z).graph).Site)
    (e : (DescentCommonPalette.rotor (Z).graph).Edge) (m node arg : ℕ)
    (x : Fin 4→Cell field) (capRead : (x 0).val=input.placement.cap)
    (chosen : (x 1).val=((Z).goodLabel T g₀).val.1+1 ∧ (x 2).val%2=0)
    (host : u.1.2=(Z).placed T ((Z).rotorSiteAt T s g₀ site))
    (shortShape : (x 3).val=((Z).rawHostRank T vertexCode u.1.2).val%(DescentDenseHostOrder.roster (Z).graph r height).card)
    (face : Roster.Face A₁ ord₁ (blocks B) u) (isEdge : face.val.1=privateWire B (goodOccurrence B s g₀ e))
    (layer : Fin ((Z).circuit s g₀).layers) (batch : Fin m)
    (within : layer.val*m+batch.val<span) (wide : 2*totalLocal B<2^target)
    (lane : (rotorQueryShape B m span field target lanes).socket (Z).graph C ((Z).circuit s g₀).layers node arg site=
      some (face.val.2,e,layer.val*m+batch.val)) :
    ((rotorQueryShape B m span field target lanes).mixedLaw (Z).graph C node arg x).val=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 := by
  let cfg:=rotorQueryShape B m span field target lanes
  let badge:=(Z).localShape T u.1.2
  have rank : (x 3).val=(localRank (Z).graph r height badge).val := by
    let fields₀ := (Z).hostFields T vertexCode u.1.2
    let palette := (DescentDenseHostOrder.roster (Z).graph r height).card
    calc
      _ = ((Z).rawHostRank T vertexCode u.1.2).val % palette := shortShape
      _ = (fields₀.2.val + palette*fields₀.1.val) % palette := rfl
      _ = fields₀.2.val := (Nat.add_mul_mod_self_left ..).trans (Nat.mod_eq_of_lt fields₀.2.isLt)
      _ = _ := rfl
  have real : badge.val=.good s ((),((Z).goodLabel T g₀).val.2) site:=by
    dsimp only [badge]
    rw [host]
    exact (Z).installed_rotor_shape T s g₀ site
  have calendar:=(DescentRecordedRotorLayers.from_prior_cap B proof s g₀ _ capRead).1
  have result:=cfg.mixed_good (Z).graph C node arg x ((Z).goodLabel T g₀) s face.val.2 badge site e
    ⟨layer.val*m+batch.val,within⟩ rank real chosen.1 (by change cfg.socket (Z).graph C (DescentRecordedRotorLayers.layers (Z).n (Z).width f (x 0).val) node arg site = _; rw [←calendar]; exact lane)
  have decode:=rotor_query_at B (target:=target) (lanes:=lanes) proof u s g₀ e m (cfg.registers x)
    capRead chosen face isEdge layer batch within wide
  let key : Coord (Z).graph r span := (s,face.val.2,(Z).goodLabel T g₀,e,⟨layer.val*m+batch.val,within⟩)
  have registered := cfg.registered (Z).graph key (cfg.registers x)
  exact (congrArg Fin.val result).trans ((congrArg Fin.val registered).symm.trans decode)


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
