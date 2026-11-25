import OAI.Hierarchy.ProtocolRAMPortRanks
import OAI.Hierarchy.DescentTerminalGraphVolume
import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentTerminalBoundaryBasis
import OAI.Hierarchy.DescentBitDescription

namespace OAI
/-! # Terminal argument rows for exactly the aligned blocks used by a retained scalar -/

namespace Hierarchy.DescentTerminalBundleRows
open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentTerminalGraphPositions
open DescentTerminalRecipeRows DescentTerminalBinReaddress ThreeFlat.Routing
open scoped BigOperators Classical
noncomputable section

variable {Tag B F : Type} [CommSemiring F] {tags : ℕ}
abbrev Public (r : Recipe Tag B) := {s : (v : r.Node) × Fin (r.arity v) // (r.operand s.1 s.2).isLeft}
def useCount (r : Recipe Tag B) := Fintype.card (Public r)

def ref (r : Recipe Tag B) (s : Public r) : B := (r.operand s.val.1 s.val.2).getLeft s.property

theorem use_le (r : Recipe Tag B) : useCount r ≤ ∑v,r.arity v := by
  have le:=Fintype.card_subtype_le (fun s : (v : r.Node) × Fin (r.arity v)=>(r.operand s.1 s.2).isLeft=true)
  simpa [useCount,Public,Fintype.card_sigma] using le

/-- A recipe's true operand address precedes all the arguments of later
births. Within one birth it increases in the recorded argument order. -/
def raw (r : Recipe Tag B) (birth : r.Node ↪ ℕ) (a : Public r) : ℕ :=
  (ProtocolRAMPortRanks.address r.arity birth a.val).val

theorem raw_injective (r : Recipe Tag B) (birth : r.Node ↪ ℕ) : Function.Injective (raw r birth) := by
  intro a b h
  exact Subtype.ext (ProtocolRAMPortRanks.injective r.arity birth birth.injective (Fin.ext h))

theorem raw_before (r : Recipe Tag B) (birth : r.Node ↪ ℕ) (a b : Public r) :
    raw r birth a<raw r birth b ↔ birth a.val.1<birth b.val.1 ∨
      (birth a.val.1=birth b.val.1 ∧ a.val.2.val<b.val.2.val) := by
  have advance (x y : Public r) (h : birth x.val.1<birth y.val.1) : raw r birth x<raw r birth y := by
    have disjoint:=ProtocolRAMPortRanks.prefix_disjoint r.arity birth h
    have live:=x.val.2.isLt
    unfold raw ProtocolRAMPortRanks.address
    dsimp only
    omega
  rcases lt_trichotomy (birth a.val.1) (birth b.val.1) with less|same|more
  · simp [less,advance a b less]
  · have eqv:=birth.injective same
    have start:=congrArg (ProtocolRAMPortRanks.prefix r.arity birth) eqv
    simp only [raw,ProtocolRAMPortRanks.address,Fin.val_mk,start,same,lt_self_iff_false,
      true_and,false_or,Nat.add_lt_add_iff_left]
  · have back:=advance b a more
    omega

def publicOrdinal (r : Recipe Tag B) (birth : r.Node ↪ ℕ) : Public r ≃ Fin (useCount r) :=
  let unit : Public r ≃ ProtocolRAMPortRanks.Units (fun _ : Public r=>1) :=
    { toFun:=fun a=>⟨a,0⟩,invFun:=fun a=>a.1,left_inv:=fun _=>rfl,
      right_inv:=fun ⟨a,b⟩=>by obtain rfl:=Subsingleton.elim b 0; rfl }
  unit.trans ((ProtocolRAMPortRanks.enumerate (fun _ : Public r=>1) (raw r birth)
    (raw_injective r birth)).trans (finCongr (by simp [useCount])))

/-- The compact public address is the exclusive count from a single
chronological scan; private occurrences never reserve a table argument. -/
theorem publicOrdinal_val (r : Recipe Tag B) (birth : r.Node ↪ ℕ) (a : Public r) :
    (publicOrdinal r birth a).val=(Finset.univ.filter (fun b : Public r=>
      birth b.val.1<birth a.val.1 ∨ (birth b.val.1=birth a.val.1 ∧ b.val.2.val<a.val.2.val))).card := by
  change ProtocolRAMPortRanks.prefix (fun _ : Public r=>1) (raw r birth) a+0=_
  simp [ProtocolRAMPortRanks.prefix,raw_before]

/-- Public uses get physical slots. Hidden operands keep their genuine local
index and are contracted inside the row. A repeated public name can fill
multiple argument positions without reloading its entire cable. -/
def numbered (r : Recipe Tag B) (birth : r.Node ↪ ℕ) (code : Tag→Fin tags) : Recipe (Fin tags) (Fin (useCount r)) where
  Hidden:=r.Hidden
  width:=r.width
  Node:=r.Node
  tag:=code ∘ r.tag
  arity:=r.arity
  operand v j:=if live : (r.operand v j).isLeft then .inl (publicOrdinal r birth ⟨⟨v,j⟩,live⟩)
    else .inr ((r.operand v j).getRight (by cases h : r.operand v j <;> simp_all))

theorem numbered_value (r : Recipe Tag B) (birth : r.Node ↪ ℕ) (code : Tag→Fin tags) (dict : Fin tags→List (List Bool)→F)
    (scalar : Tag→List (List Bool)→F) (tagRead : ∀v xs,dict (code (r.tag v)) xs=scalar (r.tag v) xs)
    (words : B→List Bool) :
    (numbered r birth code).value dict (fun i=>words (ref r ((publicOrdinal r birth).symm i)))=r.value scalar words := by
  apply Finset.sum_congr rfl
  intro hidden _
  apply Finset.prod_congr rfl
  intro v _
  change dict (code (r.tag v)) _=_
  rw [tagRead v]
  congr 2
  funext j
  cases h : r.operand v j with
  | inr t=>simp [numbered,ref,h]
  | inl b=>
    let a : Public r:=⟨⟨v,j⟩,by simp [h]⟩
    have tag := (publicOrdinal r birth).symm_apply_apply a
    have projected : ref r ((publicOrdinal r birth).symm (publicOrdinal r birth a))=b:=by
      rw [tag]
      simp [ref,a,h]
    simpa [numbered,h,a] using congrArg words projected

variable {D S p q W piece machineBits pool H N A w V : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
    (G : Network D P bits) (order : Order G S p)
abbrev SiteRef (v : G.Site) := BlockRef p (boundaryWidth G v)
variable (r : (v : G.Site)→Recipe Tag (SiteRef (p:=p) G v))

def part (hp : 0<p) {v : G.Site} (b : SiteRef (p:=p) G v) : DescentTerminalGraphRows.Part G p v :=
  DescentTerminalBoundaryBasis.part G hp b

omit [Fintype P] in
theorem read_part (hp : 0<p) {v : G.Site} (b : SiteRef (p:=p) G v) (a : G.Assignment) (x : Ports bits) :
    Order.readName (N:=G) a x (name G (part G hp b))=fun d=>bitInput G a x v (b.atBit d) :=
  DescentTerminalBoundaryBasis.read_part G hp b a x

variable {G} (hp : 0<p) (birth : ∀v,(r v).Node ↪ ℕ)
/-- Every genuine incident p-grain is paid exactly once in the vertex's argument tuple.
Repeated operands in its scalar description address that same slot. -/
def site (r : (v : G.Site)→Recipe Tag (SiteRef (p:=p) G v)) (_hp : 0<p) (_birth : ∀v,(r v).Node ↪ ℕ)
    (i : Fin S) : Site := order.site i

theorem site_name (i : Fin S) (v : Fin ((site order r hp birth i).nodes)) (j : Fin ((site order r hp birth i).arity v)) :
    order.catalog i ((site order r hp birth i).arg v j)=order.args i v j :=
  order.catalog_arg i v j

theorem total_uses : (∑i,∑v,(site order r hp birth i).arity v)=∑v,DescentTerminalGraphRows.arity G p v :=
  DescentTerminalGraphVolume.total_arity order

theorem paid_rows (positive : 0<q) :
    (∑i,(site order r hp birth i).rows q)*q ≤ 3*DescentTerminalGraphVolume.bundleBudget (p:=p) G+
      ((∑i,(order.site i).groups)+2*S)*q :=
  DescentTerminalGraphVolume.paid_rows order positive

variable (positive : 0<W) (slotPositive : 0<q) (payloadWidth : p=W*piece)
local notation "sites" => site order r hp birth

def payload (a : G.Assignment) (x : Ports bits) : Fin (Bins (W:=W) (q:=q) sites)→Payload W q piece :=
  let word (z : Named sites):=fun d : Fin (W*piece)=>Order.readName (N:=G) a x (order.catalog z.1 z.2) (d.cast payloadWidth.symm)
  Function.curry (Function.extend (source sites positive slotPositive) word (fun _ _=>false))

theorem payload_source (a : G.Assignment) (x : Ports bits) (z : Named sites) (d : Fin (W*piece)) :
    let src:=source sites positive slotPositive z
    payload order r hp birth positive slotPositive payloadWidth a x src.1 src.2 d=
      Order.readName (N:=G) a x (order.catalog z.1 z.2) (d.cast payloadWidth.symm) := by
  intro src
  let nameRow (y:Named sites) (j:Fin (W*piece)):=Order.readName (N:=G) a x (order.catalog y.1 y.2) (j.cast payloadWidth.symm)
  change Function.extend (source sites positive slotPositive) nameRow (fun _ _=>false)
    (source sites positive slotPositive z) d=nameRow z d
  rw [(source_unique sites positive slotPositive).extend_apply]

def recipes (code : Tag→Fin tags) (i : Fin S) (v : Fin ((sites i).nodes)) :=
  DescentTerminalBoundaryBasis.numbered G hp (order.node i v) (order.operandRank _) (r (order.node i v)) code

private theorem ofFn_cast_read {m n : ℕ} (e:m=n) (f:Fin m→Bool) :
    List.ofFn (fun d:Fin n=>f (d.cast e.symm))=List.ofFn f:=by
  cases e
  rfl

private theorem payload_argument (a:G.Assignment) (x:Ports bits) (i:Fin S)
    (v:Fin ((sites i).nodes)) (j:Fin ((sites i).arity v)) :
    let src:=source sites positive slotPositive (sourceName sites ⟨i,v,j⟩)
    List.ofFn (payload order r hp birth positive slotPositive payloadWidth a x src.1 src.2)=
      wordList (Order.readName (N:=G) a x (order.args i v j)) :=by
  let z : Named sites:=sourceName sites ⟨i,v,j⟩
  have label:order.catalog z.1 z.2=order.args i v j:=site_name order r hp birth i v j
  let f:=Order.readName (N:=G) a x (order.args i v j)
  calc
    _ = List.ofFn (fun t:Fin (W*piece)=>f (t.cast payloadWidth.symm)):=by
      apply congrArg List.ofFn
      funext t
      exact (payload_source order r hp birth positive slotPositive payloadWidth a x z t).trans
        (congrArg (fun label=>Order.readName (N:=G) a x label (t.cast payloadWidth.symm)) label)
    _ = _ := ofFn_cast_read payloadWidth f

theorem site_product (code : Tag→Fin tags) (dict : Fin tags→List (List Bool)→F)
    (scalar : Tag→List (List Bool)→F) (tagRead : ∀v u xs,dict (code ((r v).tag u)) xs=scalar ((r v).tag u) xs)
    (values : G.Site→G.Assignment→Ports bits→F) (valid : ∀v a x,(r v).value scalar (fun b=>wordList (fun d=>bitInput G a x v (b.atBit d)))=values v a x)
    (a : G.Assignment) (x : Ports bits) :
    (∏i,∏v,(recipes order r hp birth code i v).value dict (fun j=>
      let src:=source sites positive slotPositive (sourceName sites ⟨i,v,j⟩)
      List.ofFn (payload order r hp birth positive slotPositive payloadWidth a x src.1 src.2)))=∏v,values v a x := by
  have one (i : Fin S) (v : Fin ((sites i).nodes)) :
      (recipes order r hp birth code i v).value dict
        (fun j=>wordList (Order.readName (N:=G) a x (order.args i v j)))=values (order.node i v) a x :=
    (DescentTerminalBoundaryBasis.graph_value G hp (order.node i v) (order.operandRank _)
      (r (order.node i v)) code dict scalar (tagRead _) a x).trans (valid _ a x)
  calc
    _ = ∏i,∏v:Fin ((sites i).nodes),values (order.node i v) a x :=by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro v _
      refine Eq.trans ?_ (one i v)
      apply congrArg ((recipes order r hp birth code i v).value dict)
      funext j
      exact payload_argument order r hp birth positive slotPositive payloadWidth a x i v j
    _ = ∏i,∏v : order.Nodes i,values v.val a x := by
      apply Finset.prod_congr rfl
      intro i _
      exact (order.nodes i).symm.prod_comp (fun v=>values v.val a x)
    _ = _ := Fintype.prod_fiberwise order.home (fun v=>values v a x)

theorem graph_product (code : Tag→Fin tags) (dict : Fin tags→List (List Bool)→F)
    (scalar : Tag→List (List Bool)→F) (tagRead : ∀v u xs,dict (code ((r v).tag u)) xs=scalar ((r v).tag u) xs)
    (T : G.Tables F) (valid : ∀v a x,(r v).value scalar (fun b=>wordList (fun d=>bitInput G a x v (b.atBit d)))=G.read T a x v)
    (a : G.Assignment) (x : Ports bits) :
    (∏i,∏v,(recipes order r hp birth code i v).value dict (fun j=>
      let src:=source sites positive slotPositive (sourceName sites ⟨i,v,j⟩)
      List.ofFn (payload order r hp birth positive slotPositive payloadWidth a x src.1 src.2)))=∏v,G.read T a x v :=
  site_product order r hp birth positive slotPositive payloadWidth code dict scalar tagRead
    (fun v a x=>G.read T a x v) valid a x

/-- One common finite dictionary is evaluated on the purchased row pool.
Its domain contains only bounded tag fields and local operand addresses. -/
theorem requests_site_functions (code : Tag→Fin tags) (dict : Fin tags→List (List Bool)→F)
    (scalar : Tag→List (List Bool)→F) (tagRead : ∀v u xs,dict (code ((r v).tag u)) xs=scalar ((r v).tag u) xs)
    (values : G.Site→G.Assignment→Ports bits→F) (valid : ∀v a x,(r v).value scalar (fun b=>wordList (fun d=>bitInput G a x v (b.atBit d)))=values v a x)
    (machine : sliceWidth W q piece ≤ machineBits) (space : DescentTerminalBinPack.purchased W (counts (q:=q) sites) ≤ pool)
    (fit : ∀i,(sites i).rows q ≤ W) (small : ∀i v,(sites i).arity v ≤ q)
    (hH : ∀v,Fintype.card (r v).Hidden ≤ H) (hN : ∀v,Fintype.card (r v).Node ≤ N)
    (hA : ∀v u,(r v).arity u ≤ A) (hw : ∀v u,(r v).width u ≤ w) (hV : ∀i,(sites i).nodes ≤ V)
    (a : G.Assignment) (x : Ports bits) :
    let req:=DescentTerminalRowBooks.request sites positive slotPositive machine
      (payload order r hp birth positive slotPositive payloadWidth a x) space (recipes order r hp birth code)
      (fun i v=>hH (order.node i v)) (fun i v=>hN (order.node i v)) (fun i v=>hA (order.node i v))
      (fun i v=>hw (order.node i v)) hV
    (∏u,DescentTerminalRowBooks.menu q H N A w V (W*piece) dict (req u))=∏v,values v a x := by
  intro req
  rw [show (∏u,DescentTerminalRowBooks.menu q H N A w V (W*piece) dict (req u))=
    ∏i,∏v,(recipes order r hp birth code i v).value dict (fun j=>
      let src:=source sites positive slotPositive (sourceName sites ⟨i,v,j⟩)
      List.ofFn (payload order r hp birth positive slotPositive payloadWidth a x src.1 src.2)) from
    DescentTerminalRowBooks.requests_product _ _ _ fit machine _ _ _ _ _ _ _ _ small dict]
  exact site_product order r hp birth positive slotPositive payloadWidth code dict scalar tagRead values valid a x

theorem requests_graph_product (code : Tag→Fin tags) (dict : Fin tags→List (List Bool)→F)
    (scalar : Tag→List (List Bool)→F) (tagRead : ∀v u xs,dict (code ((r v).tag u)) xs=scalar ((r v).tag u) xs)
    (T : G.Tables F) (valid : ∀v a x,(r v).value scalar (fun b=>wordList (fun d=>bitInput G a x v (b.atBit d)))=G.read T a x v)
    (machine : sliceWidth W q piece ≤ machineBits) (space : DescentTerminalBinPack.purchased W (counts (q:=q) sites) ≤ pool)
    (fit : ∀i,(sites i).rows q ≤ W) (small : ∀i v,(sites i).arity v ≤ q)
    (hH : ∀v,Fintype.card (r v).Hidden ≤ H) (hN : ∀v,Fintype.card (r v).Node ≤ N)
    (hA : ∀v u,(r v).arity u ≤ A) (hw : ∀v u,(r v).width u ≤ w) (hV : ∀i,(sites i).nodes ≤ V)
    (a : G.Assignment) (x : Ports bits) :
    let req:=DescentTerminalRowBooks.request sites positive slotPositive machine
      (payload order r hp birth positive slotPositive payloadWidth a x) space (recipes order r hp birth code)
      (fun i v=>hH (order.node i v)) (fun i v=>hN (order.node i v)) (fun i v=>hA (order.node i v))
      (fun i v=>hw (order.node i v)) hV
    (∏u,DescentTerminalRowBooks.menu q H N A w V (W*piece) dict (req u))=∏v,G.read T a x v :=
  requests_site_functions order r hp birth positive slotPositive payloadWidth code dict scalar tagRead
    (fun v a x=>G.read T a x v) valid machine space fit small hH hN hA hw hV a x

end
end Hierarchy.DescentTerminalBundleRows

end OAI
