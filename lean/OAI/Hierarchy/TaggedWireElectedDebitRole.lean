import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.ProbeFixedStripQuotes
import OAI.Hierarchy.ProtocolRAMCatalystArchiveChronology
import OAI.Hierarchy.TaggedWireCommodityGraphs
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDates

namespace OAI
/-! # A positive physical input tap belongs to its good or its single catalyst pair -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar Calendar.StockCommit RepairHistogram PurchaseStage
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical BigOperators Fin.CommRing

namespace CatalystArchive
variable {w q d num payload : ℕ} {C : Chart w q d} {ev : Attempt} {before : Memory w} {owner : Expr}
    {a : Area} {s : Sources} (date : Date C ev before owner (a.direct+a.occurrences) a.occurrences num payload)

/-- This is the width stored by this issued date, at the very offset of the
native debit occurrence. The inactive owner beside a zero debit is immaterial. -/
theorem Date.issued_at (labels : LabelSource) (b : Batch q d) (physical : C.commit ev=pricedSegment a s labels w b)
    (ready : Calendar.ready C (.attempt ev) before) (board : EventBoard (fresh a s) w)
    (budget : payload<2^w) (i : Fin a.occurrences) :
    let st:=fresh a s
    let m:=stageInput a s labels (postOutput (C.layout ev) (repair C ev) (prepared C ev before))
    date.entry.bits (Fin.cast date.shape.symm i)=
      if kind (goods:=a.goods) st.plan.bank st.columns m i=none then consumedBits st.columns m i else 0 := by
  intro st m
  let z:=Fin.cast date.shape.symm i
  let debit := if kind (goods:=a.goods) st.plan.bank st.columns m i=none then consumedBits st.columns m i else 0
  have word : (date.entry.bits z : Word w) = (debit : Word w) :=
    (date.posted z).symm.trans (priced_debit C ev before a s labels b physical ready board i)
  have fit : date.entry.bits z<2^w := (date.entry.fits z).trans_lt budget
  have native : debit<2^w := by
    dsimp only [debit]
    split
    · exact (st.columns.charge.eval m (i.val:Word w)).isLt
    · exact Nat.two_pow_pos _
  calc
    date.entry.bits z = (date.entry.bits z : Word w).val := (Fin.val_cast_of_lt fit).symm
    _ = (debit : Word w).val := congrArg Fin.val word
    _ = debit := Fin.val_cast_of_lt native

/-- Positive native debits have one decoded archive owner. A zero-width
entry contributes to no reserve account. -/
def Date.physicalCatalystKey {V : Type*} {base size : ℕ} (day : Date C ev before owner base size num payload)
    (keys : V≃Fin num) (i : Fin size) : Option V :=
  let v:=Fin.cast day.shape.symm i
  if 0<day.entry.bits v then some (keys.symm (day.entry.owner v)) else none

/-- Summing the positive occurrence keys produces exactly the dated debit
counter for the selected pair, in the native archived row numbering. -/
theorem Date.physicalCatalystKey_sum {V : Type*} [Fintype V] {base size : ℕ} (day : Date C ev before owner base size num payload)
    (keys : V≃Fin num) (c : V) :
    OuterBank.resourceBits (day.physicalCatalystKey keys) (fun i=>day.entry.bits (Fin.cast day.shape.symm i)) c=
      ∑j,if day.entry.owner j=keys c then day.entry.bits j else 0 := by
  classical
  unfold OuterBank.resourceBits
  rw [←(finCongr day.shape.symm).sum_comp (fun j=>if day.entry.owner j=keys c then day.entry.bits j else 0)]
  apply Finset.sum_congr rfl
  intro i _
  let j:=Fin.cast day.shape.symm i
  change (if (day.physicalCatalystKey keys i)=some c then day.entry.bits j else 0)=
    if day.entry.owner j=keys c then day.entry.bits j else 0
  by_cases pos : 0<day.entry.bits j
  · unfold Date.physicalCatalystKey
    change (if (if 0<day.entry.bits j then some (keys.symm (day.entry.owner j)) else none)=some c then _ else _)=_
    simp only [pos,ite_true,Option.some.injEq,Equiv.symm_apply_eq]
  · have zero:=Nat.eq_zero_of_not_pos pos
    simp [zero]

section Slots
open ColumnWires Calendar.StockCommit
open LinearAlgebra.SpectralBooks.ChordGraph
variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N z D : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}
local notation "Roles" => Role C H (A⊕B) k
variable {e : Role C H (A⊕B) k → Chord sites}
    {menu : Probe.FixedMenu F e
      (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
      ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
      ε tree N}
    (x : StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)

omit [Nonempty (Fin k)] in
/-- Read the signed kind from the true selector at each original strip port.
Only ordinary positions have an address expression in the native compiler. -/
theorem StripInput.checkedKinds (j : Fin x.raw.market.rows) (stock : A→Fin x.raw.coordinates)
    (located : ∀u,(x.addr u).eval x.mem (j.val:Word w)=((stock u).val:Word w)) (r : Roles) :
    let st:=fresh x.form.pricedArea x.form.stockSource
    let port:=PortPadding.inject x.ports (Fintype.equivFin Roles r)
    kind (goods:=st.goods) st.plan.bank st.columns x.mem (x.plan.enum ⟨j,port⟩)=account stock r := by
  apply x.role_kind j stock _ r
  intro u
  have bounded : (stock u).val<2^w := (stock u).isLt.trans_le ((Nat.le_add_left ..).trans x.bankFit.le)
  rw [located,Fin.val_cast_of_lt bounded]

end Slots

end CatalystArchive

namespace Calendar.CatalogueRows
open ProbeStage CoreBoard Strip WireTelescope CatalystArchive
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor Probe ChosenPackets RowRouting StripPaths PacketTurns
open ThreeFlat.Diagonal.MotifOuterTerms

variable {sam : PurchaseSampler} {h d k n K w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "col" => TreeColumn n
local notation "R" => ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k
local notation "Good" => Commodity (Fin (2^h)) (Stages h d) k
local notation "Pairs" => Columns h d×Fin k
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
local notation "line" => reportedRole place (ColumnWires.ends (horizontal n) extra) u

/-- Reindex the actual endpoint graph by the linear stock-bank ordinal. -/
def ordinalGoods (π : Equiv.Perm (Fin (2^h))) (name : Site h d k↪Fin K) {goods : ℕ}
    (code : Good≃Fin goods) : PortGraph (Fin K) (Fin goods) :=
  ⟨(commodityGraph π name).tail ∘ code.symm,(commodityGraph π name).head ∘ code.symm⟩

private theorem single_endpoints {V : Type} (G : PortGraph (Fin K) V) (i : V) (bits : ℕ)
    (apart : G.tail i≠G.head i) :
    Finsupp.single (Probe.orderedEnds (G.tail i) (G.head i) apart) bits=G.chordWidth i bits := by
  rcases lt_or_gt_of_ne apart with lt|gt
  · simp [Probe.orderedEnds,PortGraph.chordWidth,lt]
  · simp [Probe.orderedEnds,PortGraph.chordWidth,gt,not_lt.mpr gt.le]

variable (g : EarnedInstall p b π extra place u endRow name addr m reg)

include g in
omit [Fintype A] [Fintype B] [Fintype Ball] in
theorem EarnedInstall.single_ordinary {goods : ℕ} (code : Good≃Fin goods) (x : A) (bits : ℕ) :
    Finsupp.single (line (.extra (.inl x))) bits=(ordinalGoods π name code).chordWidth (code (addr x)) bits := by
  let graph:=ordinalGoods π name code
  have apart : graph.tail (code (addr x))≠graph.head (code (addr x)) := by
    simpa only [graph,ordinalGoods,Function.comp_apply,Equiv.symm_apply_apply] using
      commodityGraph_distinct π name name.injective (addr x)
  have eqn:=single_endpoints graph (code (addr x)) bits apart
  simpa only [graph,ordinalGoods,reportedRole,ColumnWires.ends,commodityGraph,Function.comp_apply,
    Equiv.symm_apply_apply,g.mapped,g.goods] using eqn

include g in
omit [Fintype A] [Fintype B] [Fintype Ball] in
theorem EarnedInstall.single_catalyst (c : col) (j : Fin k) (bits : ℕ) :
    Finsupp.single (line (.catalyst c j)) bits=(catalystGraph name).chordWidth (g.col c,j) bits := by
  have eqn:=single_endpoints (catalystGraph name) (g.col c,j) bits
    (catalystGraph_distinct name name.injective (g.col c,j))
  simpa only [reportedRole,ColumnWires.ends,g.mapped,catalystGraph,Prod.map,id_eq] using eqn

omit [Fintype Ball] in
/-- The native owner pass at this row reports the column and axis of the
original physical placement. The column equality allows the dated birth
decoder and the terminal strip operand to be evaluated in their own memories. -/
theorem EarnedInstall.owner_port (head : PortHeader) (bound : Fintype.card R≤head.ports)
    (row : Fin head.rows) (c : col) (axis : Fin k) (before : Memory w)
    (loaded : head.Loaded before) (room : head.ports≤2^w) (column : col→Expr)
    (atRow : (column c).eval before (row.val:Word w)=(p.column c).eval m reg) :
    let port:=PortPadding.inject bound (Fintype.equivFin R (.catalyst c axis))
    (CatalystArchive.select (D:=head.ports) head.fieldTerm head.ballTerm (ownerExpr (H:=Fin n) (E:=A⊕B) (k:=k) column)).eval
      before ((head.enum ⟨row,port⟩).val:Word w)=((pairKeys (Columns h d) k (g.col c,axis)).val:Word w) := by
  intro port
  have pair:=StripDirectory.header_pair head before loaded row port
  apply owner_read column head.fieldTerm head.ballTerm before _ bound room c axis (g.col c)
  · exact (congrArg Fin.val pair.2).trans (Fin.val_cast_of_lt (port.isLt.trans_le room))
  · rw [pair.1,atRow,←g.placed.1 c,Fin.cast_val_eq_self]

private theorem chordWidth_zero {E : Type} (G : PortGraph (Fin K) E) (i : E) : G.chordWidth i 0=0 := by
  unfold PortGraph.chordWidth
  split_ifs <;> simp

omit [Fintype A] [Fintype B] in
private theorem request_of_debit {J : Type} [Fintype J] (req : J→R) (bits : ℕ) (r : R)
    (pos : 0<debited req bits r) : ∃j,req j=r := by
  by_contra! none
  have zero : debited req bits r=0 := by simp [debited,none]
  omega

variable {F J : Type} [Field F] [Fintype J] (requests : J→(TreeColumn n×Fin k)⊕A)
local notation "req" => (ColumnWires.demand (H:=Fin n) (Sum.inl (α:=A) (β:=B))) ∘ requests
variable {sites : ℕ} [Nonempty (Fin sites)] {edge : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Chord sites}
    {P : Packet F edge ((ColumnWires.demand (I:=TreeColumn n) (H:=Fin n) (k:=k)
      (Sum.inl (α:=A) (β:=B))) ∘ requests)}
    {spare ports rows : ℕ} {a : Area} {s : Sources} {post : Memory w}
    {ballot : Batch (P.terms+spare) ports} {L : PortPlan (fresh a s) ballot post rows} {j : Fin rows}
    (N : NativePacketRow P spare ballot L j)
local notation "oc" => fun r:R=>L.enum ⟨j,N.ports r⟩
local notation "tag" => kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post
local notation "used" => consumedBits (n:=a.occurrences) (fresh a s).columns post
local notation "catKeys" => pairKeys (Columns h d) k
variable {payload : ℕ} {chart : Chart w (P.terms+spare) ports} {ev : Attempt} {before : Memory w} {owner : Expr}
    (date : CatalystArchive.Date chart ev before owner (a.direct+a.occurrences) a.occurrences (Fintype.card (Columns h d)*k) payload)
local notation "offset" => Fin.cast date.shape.symm
local notation "get" => fun i : Fin a.occurrences => date.entry.bits (offset i)
local notation "who" => fun i : Fin a.occurrences => (catKeys).symm (date.entry.owner (offset i))
variable (code : Commodity (Fin (2^h)) (Stages h d) k ≃ Fin a.goods)
    (source : ∀r : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k,
      kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post (L.enum ⟨j,N.ports r⟩)
        = ColumnWires.account (code ∘ addr) r)
    (recorded : ∀i : Fin a.occurrences, date.entry.bits (Fin.cast date.shape.symm i) =
      if kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post i=none then
        consumedBits (fresh a s).columns post i else 0)
    (ownerRead : ∀ (c : TreeColumn n) (axis : Fin k),
      owner.eval before ((L.enum ⟨j,N.ports (.catalyst c axis)⟩).val:Word w) =
        ((pairKeys (Columns h d) k (g.col c,axis)).val:Word w))
    (keyFit : Fintype.card (Columns h d)*k≤2^w)

include source recorded ownerRead keyFit in
omit [Fintype Ball] [Nonempty (Fin sites)] in
/-- A physical positive request uses the same reserve key as its native
issued entry. A catalyst contributes one chord joining the two signed radial
endpoints. Ordinary commodities contribute the original sorted commodity chord. -/
theorem EarnedInstall.debit_role (r : R) :
    Finsupp.single (line r) (used (oc r)) =
      (tag (oc r)).elim 0 (fun i=>(ordinalGoods π name code).chordWidth i (used (oc r)))+
      (catalystGraph name).chordWidth (who (oc r)) (get (oc r)) := by
  by_cases pos : 0<used (oc r)
  · have amount : used (oc r) = debited req (ballot.copies*P.width) r := (N.amounts r).2
    obtain ⟨z,eqn⟩:=request_of_debit req (ballot.copies*P.width) r (pos.trans_le amount.le)
    cases step : requests z with
    | inl v =>
      rcases v with ⟨c,axis⟩
      have hit : (.catalyst c axis:R)=r := by simpa only [Function.comp_apply,step,ColumnWires.demand] using eqn
      clear eqn
      subst r
      have money : tag (oc (.catalyst c axis))=none:=source _
      have charge : get (oc (.catalyst c axis))=used (oc (.catalyst c axis)) :=
        (recorded _).trans (ite_eq_left money)
      have archivedPos : 0 < get (oc (.catalyst c axis)) := pos.trans_le charge.symm.le
      have emitted:=(date.ownerRows.word (offset (oc (.catalyst c axis))) archivedPos).symm.trans (ownerRead c axis)
      have first := (date.entry.owner (offset (oc (.catalyst c axis)))).isLt.trans_le keyFit
      have second := (catKeys (g.col c,axis)).isLt.trans_le keyFit
      have same : date.entry.owner (offset (oc (.catalyst c axis)))=catKeys (g.col c,axis) :=
        Fin.ext (by simpa only [Fin.val_cast_of_lt first,Fin.val_cast_of_lt second] using congrArg Fin.val emitted)
      have key : who (oc (.catalyst c axis))=(g.col c,axis) :=
        (congrArg (catKeys).symm same).trans ((catKeys).symm_apply_apply _)
      rw [money,charge,key]
      simpa using g.single_catalyst c axis (used (oc (.catalyst c axis)))
    | inr x =>
      have hit : (.extra (.inl x):R)=r := by simpa only [Function.comp_apply,step,ColumnWires.demand] using eqn
      clear eqn
      subst r
      have money : tag (oc (.extra (.inl x)))=some (code (addr x)):=source _
      have empty : get (oc (.extra (.inl x)))=0 :=
        (recorded _).trans (ite_eq_right (fun absent => Option.some_ne_none _ (money.symm.trans absent)))
      rw [money,empty,chordWidth_zero,add_zero]
      exact g.single_ordinary code x _
  · have zero := Nat.eq_zero_of_not_pos pos
    have empty : get (oc r)=0 := (recorded _).trans (by simp only [zero,ite_self])
    rw [zero,Finsupp.single_zero,empty]
    cases tag (oc r) <;> simp [chordWidth_zero]

include source recorded ownerRead keyFit in
omit [Fintype Ball] [Nonempty (Fin sites)] in
/-- Pad fields need no fabricated physical edge or catalyst owner. Both words
are zero for the actual layout. -/
theorem EarnedInstall.debit_port (wire : Fin ports→Chord K) (named : ∀r:R,wire (N.ports r)=line r) (v : Fin ports) :
    let i:=L.enum ⟨j,v⟩
    Finsupp.single (wire v) (used i)=
      (tag i).elim 0 (fun g=>(ordinalGoods π name code).chordWidth g (used i))+
      (catalystGraph name).chordWidth (who i) (get i) := by
  intro i
  by_cases image : ∃r,N.ports r=v
  · obtain ⟨r,rfl⟩:=image
    simpa only [i,named] using g.debit_role requests N date code source recorded ownerRead keyFit r
  · have dead:= (N.unused v (fun r h=>image ⟨r,h⟩)).2
    change used i=0 at dead
    have empty : get i=0 := (recorded _).trans (by simp only [dead,ite_self])
    rw [dead,Finsupp.single_zero,empty]
    cases tag i <;> simp [chordWidth_zero]

/-- The archived optional key gives the same chord width as its stored
total owner field, including all zero rows. -/
theorem dated_key_width {V : Type} {number payload size w q d base : ℕ} {ev : Attempt} {C : Chart w q d}
    {before : Memory w} {owner : Expr} (date : CatalystArchive.Date C ev before owner base size number payload)
    (keys : V≃Fin number) (G : PortGraph (Fin K) V) (i : Fin size) :
    (if 0<date.entry.bits (Fin.cast date.shape.symm i) then
        some (keys.symm (date.entry.owner (Fin.cast date.shape.symm i))) else none).elim 0
      (fun k=>G.chordWidth k (date.entry.bits (Fin.cast date.shape.symm i)))=
    G.chordWidth (keys.symm (date.entry.owner (Fin.cast date.shape.symm i))) (date.entry.bits (Fin.cast date.shape.symm i)) := by
  by_cases h : 0<date.entry.bits (Fin.cast date.shape.symm i)
  · simp [h]
  · simp [Nat.eq_zero_of_not_pos h,chordWidth_zero]

/-- Extend the elected classifications to every occurrence in the physical
rectangle. Uncommitted rows debit zero by the actual batch decoder. -/
theorem all_debit_ports {q ports rows payload : ℕ} {a : Area} {s : Sources} {post before : Memory w}
    {b : Batch q ports} (L : PortPlan (fresh a s) b post rows)
    {V : Type} {num : ℕ} {ev : Attempt} {chart : Chart w q ports} {owner : Expr}
    (receipt : CatalystArchive.Date chart ev before owner (a.direct+a.occurrences) a.occurrences num payload)
    (keys : V≃Fin num) (G : PortGraph (Fin K) (Fin a.goods)) (Cat : PortGraph (Fin K) V)
    (wire : Fin a.occurrences→Chord K)
    (posted : ∀i,receipt.entry.bits (Fin.cast receipt.shape.symm i)=if kind (n:=a.occurrences) (goods:=a.goods) (fresh a s).plan.bank
      (fresh a s).columns post i=none then consumedBits (n:=a.occurrences) (fresh a s).columns post i else 0)
    (elected : ∀j,j∈liveRows b post rows→∀v:Fin ports,
      let i:=L.enum ⟨j,v⟩
      let r:=Fin.cast receipt.shape.symm i
      let debit:=consumedBits (n:=a.occurrences) (fresh a s).columns post i
      Finsupp.single (wire i) debit=(kind (n:=a.occurrences) (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post i).elim
        0 (fun g=>G.chordWidth g debit)+Cat.chordWidth (keys.symm (receipt.entry.owner r)) (receipt.entry.bits r))
    (i : Fin a.occurrences) :
    let debit:=consumedBits (n:=a.occurrences) (fresh a s).columns post i
    Finsupp.single (wire i) debit=(kind (n:=a.occurrences) (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post i).elim
      0 (fun g=>G.chordWidth g debit)+(receipt.physicalCatalystKey keys i).elim 0
        (fun c=>Cat.chordWidth c (receipt.entry.bits (Fin.cast receipt.shape.symm i))) := by
  dsimp only
  unfold CatalystArchive.Date.physicalCatalystKey
  rw [dated_key_width]
  by_cases on : (L.enum.symm i).1∈liveRows b post rows
  · have inverse : L.enum ⟨(L.enum.symm i).1,(L.enum.symm i).2⟩=i := L.enum.apply_symm_apply i
    have row := elected _ on (L.enum.symm i).2
    dsimp only at row
    rw [inverse] at row
    exact row
  · have zero : consumedBits (n:=a.occurrences) (fresh a s).columns post i=0 := (L.off i on).2
    rw [zero,Finsupp.single_zero,posted,zero]
    cases kind (n:=a.occurrences) (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post i <;> simp [chordWidth_zero]

end Calendar.CatalogueRows
end Hierarchy.ProtocolRAM
end

end OAI
