import OAI.Hierarchy.ProbePaidBirthRow
import OAI.Hierarchy.ProbePaidStripHits

namespace OAI
/-! # Native direct and second-radius occupancy at every original reporter row -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard StockCommit RepairHistogram CatalogueRows Strip
open scoped Classical Fin.CommRing BigOperators

variable {w edges q ports rows : ℕ} {Ball X V : Type}

/-- The immutable first endpoint identifies the ball of every positive
occurrence at this exact physical row, even for a padded catalogue and an
empty set of selected purchases. The second occurrence coordinate is the
field of the actual finite stock packet. -/
theorem StockCommit.PortPlan.endpoint_hits {st : StockCommit} {batch : Batch q ports} {pre : Memory w}
    (P : PortPlan st batch pre rows) (s : PaidWidths.Slice) (m : Memory w) (e : Fin edges)
    (eqCount : s.count=st.occurrences) (atRow : Ball ↪ Fin rows) (place : Ball×X ↪ V)
    (source : Fin edges→V) (active : ∀ j∈liveRows batch pre rows,∃u,atRow u=j)
    (credit : ∀i : Fin s.count,(s.amount.eval m (i.val:Word w)).val≤ installedBits st.columns pre (i.cast eqCount))
    (inside : ∀u t,let i:=(P.enum ⟨atRow u,t⟩).cast eqCount.symm
      (s.edge.eval m (i.val:Word w)).val=e.val → 0<(s.amount.eval m (i.val:Word w)).val →
        ∃x,place (u,x)=source e) :
    s.load m e≤ports*(batch.maxWidth*batch.copies) := by
  let split (i : s.Positive m e):=P.enum.symm (i.val.cast eqCount)
  have admitted (i : s.Positive m e) : (split i).1∈liveRows batch pre rows := by
    by_contra dead
    have no:=(P.off (i.val.cast eqCount) dead).1
    exact (Nat.not_lt_of_ge ((credit i.val).trans_eq no)) i.property.2
  let owner (i : s.Positive m e):=Classical.choose (active _ (admitted i))
  have ownerAt (i : s.Positive m e) : atRow (owner i)=(split i).1 :=
    Classical.choose_spec (active _ (admitted i))
  have recover (i : s.Positive m e) : (P.enum ⟨atRow (owner i),(split i).2⟩).cast eqCount.symm=i.val := by
    apply Fin.ext
    change (P.enum ⟨atRow (owner i),(split i).2⟩).val=i.val.val
    rw [ownerAt i]
    change (P.enum (P.enum.symm (i.val.cast eqCount))).val=i.val.val
    rw [P.enum.apply_symm_apply];rfl
  apply s.live_load m e place source ports (batch.maxWidth*batch.copies) owner (fun i=>(split i).2)
  · intro i
    exact inside (owner i) (split i).2 (by rw [recover];exact i.property.1) (by rw [recover];exact i.property.2)
  · intro i j same field
    apply Subtype.ext
    rw [←recover i,←recover j,same,field]
  · intro i
    exact (credit i.val).trans (P.actual_width _)

theorem StockCommit.PortPlan.positive_source {st : StockCommit} {batch : Batch q ports} {pre : Memory w}
    (P : PortPlan st batch pre rows) (slice : PaidWidths.Slice) (m : Memory w) (e : Fin edges)
    (eqCount : slice.count=st.occurrences) (atRow : Ball ↪ Fin rows)
    (active : ∀j∈liveRows batch pre rows,∃u,atRow u=j)
    (credit : ∀i : Fin slice.count,(slice.amount.eval m (i.val:Word w)).val≤ installedBits st.columns pre (i.cast eqCount))
    (i : slice.Positive m e) : ∃u t,(P.enum ⟨atRow u,t⟩).cast eqCount.symm=i.val := by
  let fields:=P.enum.symm (i.val.cast eqCount)
  have yes : fields.1∈liveRows batch pre rows := by
    by_contra dead
    exact (Nat.not_lt_of_ge ((credit i.val).trans_eq (P.off (i.val.cast eqCount) dead).1)) i.property.2
  obtain ⟨u,original⟩:=active _ yes
  refine ⟨u,fields.2,Fin.ext ?_⟩
  change (P.enum ⟨atRow u,fields.2⟩).val=i.val.val
  rw [original]
  change (P.enum (P.enum.symm (i.val.cast eqCount))).val=i.val.val
  rw [P.enum.apply_symm_apply];rfl

namespace CatalogueRows
variable {h d k : ℕ} {S : PurchaseSampler} {C H A B : Type} [Fintype C] [Fintype H] [Fintype A] [Fintype B]
local notation "Role" => ColumnWires.Role C H (A⊕B) k
local notation "Ports" => StripPorts S h d k C H B

private theorem first_endpoint {Y : Type} (f : X→Y) (p : DistinctPair X) (a : Y×Y) (faces : Faces f p a) :
    ∃x,f x=a.1 := by
  rcases faces with eq|eq
  · exact ⟨p.left,congrArg Prod.fst eq.symm⟩
  · exact ⟨p.right,congrArg Prod.fst eq.symm⟩

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
/-- Charged widths here are the actual archive's direct and masked
second-radius words. The physical role decoder checks every radius, catalyst,
cross, horizontal and purchased birth against the original board. -/
theorem StripPorts.direct_mate_load (p : Ports) (board : Board) (a : Area) (s : Sources) (g : LabelSource)
    (batch : Batch q ports) (pre m : Memory w) (P : PortPlan (fresh a s) batch pre a.rows)
    (mask other : Expr) (e : Fin board.rows) (π : Equiv.Perm (Fin (2^h)))
    (order : Fin board.coreRows≃Edges S h d k) (directory : CoreLookup.Loaded p.directory order m)
    (room : board.rows<2^w) (countRoom : a.occurrences≤2^w)
    (horizontal : H→DistinctPair C) (extra : A⊕B→DistinctPair (ColumnSite C k))
    (atRow : Ball ↪ Fin a.rows) (col : Ball→C → Columns h d)
    (place : Ball×ColumnSite C k ↪ Site h d k)
    (site : ∀u x,place (u,x)=Prod.map (col u) id x)
    (endRow : Fin board.rows→Site h d k×Site h d k)
    (core : ∀f,endRow (board.coreIndex (order.symm f))=CoreBoard.ends π f)
    (live : ∀j∈liveRows batch pre a.rows,∃u,atRow u=j)
    (archive : ∀i : Fin a.occurrences,
      (m (a.direct+i.val)).val=if kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns pre i=none
        then installedBits (fresh a s).columns pre i else 0)
    (columns : ∀u c,((p.column c).eval m ((atRow u).val:Word w)).val=((Fintype.equivFin _) (col u c)).val)
    (horiz : ∀u f l (v : Fin board.rows),((board.coreOnly (p.horizontal f l)).eval m ((atRow u).val:Word w)).val=v.val →
      Faces (Prod.map (col u) id) (ColumnWires.ends horizontal extra (.horizontal f l)) (endRow v))
    (birth : ∀u j (v : Fin board.rows),((p.probe j).eval m ((atRow u).val:Word w)).val=v.val →
      Faces (Prod.map (col u) id) (extra (.inr j)) (endRow v))
    (direct : ∀u t,(g.edge.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val=e.val →
      ∃r : Role,((p.primary board r).eval m ((atRow u).val:Word w)).val=e.val)
    (second : ∀u t,(other.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val=e.val →
      0<((PaidWidths.paidMate a s mask other).amount.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val →
      ∃r : Role,((p.mate board r).eval m ((atRow u).val:Word w)).val=e.val) :
    (PaidWidths.paidDirect a s g).load m e≤ports*(batch.maxWidth*batch.copies) ∧
      (PaidWidths.paidMate a s mask other).load m e≤ports*(batch.maxWidth*batch.copies) := by
  obtain ⟨creditD,creditM⟩:=archive_widths a s g batch m pre mask other countRoom archive
  constructor
  · apply P.endpoint_hits _ m e rfl atRow place (fun t=>(endRow t).1) live creditD
    intro u t i hit _
    obtain ⟨role,read⟩:=direct u t hit
    have f:=p.primary_faces board m ((atRow u).val:Word w) order directory room π horizontal extra (col u)
      (columns u) endRow core (horiz u) (birth u) role e read
    obtain ⟨x,hx⟩:=first_endpoint _ _ _ f
    exact ⟨x,(site u x).trans hx⟩
  · apply P.endpoint_hits _ m e rfl atRow place (fun t=>(endRow t).1) live creditM
    intro u t i hit active
    obtain ⟨role,read⟩:=second u t hit active
    have f:=p.mate_faces board m ((atRow u).val:Word w) order directory room π horizontal extra (col u)
      (columns u) endRow core role e read
    obtain ⟨x,hx⟩:=first_endpoint _ _ _ f
    exact ⟨x,(site u x).trans hx⟩

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
theorem StripPorts.direct_mate_support (p : Ports) (board : Board) (a : Area) (s : Sources) (g : LabelSource)
    (batch : Batch q ports) (pre m : Memory w) (P : PortPlan (fresh a s) batch pre a.rows)
    (mask other : Expr) (e : Fin board.rows) (π : Equiv.Perm (Fin (2^h)))
    (order : Fin board.coreRows≃Edges S h d k) (directory : CoreLookup.Loaded p.directory order m)
    (room : board.rows<2^w) (countRoom : a.occurrences≤2^w)
    (horizontal : H→DistinctPair C) (extra : A⊕B→DistinctPair (ColumnSite C k))
    (atRow : Ball ↪ Fin a.rows) (col : Ball→C → Columns h d)
    (place : Ball×ColumnSite C k ↪ Site h d k)
    (_site : ∀u x,place (u,x)=Prod.map (col u) id x)
    (endRow : Fin board.rows→Site h d k×Site h d k)
    (core : ∀f,endRow (board.coreIndex (order.symm f))=CoreBoard.ends π f)
    (live : ∀j∈liveRows batch pre a.rows,∃u,atRow u=j)
    (archive : ∀i : Fin a.occurrences,
      (m (a.direct+i.val)).val=if kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns pre i=none
        then installedBits (fresh a s).columns pre i else 0)
    (columns : ∀u c,((p.column c).eval m ((atRow u).val:Word w)).val=((Fintype.equivFin _) (col u c)).val)
    (horiz : ∀u f l (v : Fin board.rows),((board.coreOnly (p.horizontal f l)).eval m ((atRow u).val:Word w)).val=v.val →
      Faces (Prod.map (col u) id) (ColumnWires.ends horizontal extra (.horizontal f l)) (endRow v))
    (birth : ∀u j (v : Fin board.rows),((p.probe j).eval m ((atRow u).val:Word w)).val=v.val →
      Faces (Prod.map (col u) id) (extra (.inr j)) (endRow v))
    (direct : ∀u t,(g.edge.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val=e.val →
      ∃r : Role,((p.primary board r).eval m ((atRow u).val:Word w)).val=e.val)
    (second : ∀u t,(other.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val=e.val →
      0<((PaidWidths.paidMate a s mask other).amount.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val →
      ∃r : Role,((p.mate board r).eval m ((atRow u).val:Word w)).val=e.val)
    (Covers : Prop) (resolved : ∀u t, Faces (Prod.map (col u) id) t (endRow e) → Covers) :
    ((PaidWidths.paidDirect a s g).Positive m e → Covers) ∧
      ((PaidWidths.paidMate a s mask other).Positive m e → Covers) := by
  obtain ⟨creditD,creditM⟩:=archive_widths a s g batch m pre mask other countRoom archive
  constructor
  · intro i
    obtain ⟨u,t,atI⟩:=P.positive_source _ m e rfl atRow live creditD i
    have hit:=i.property.1
    rw [←atI] at hit
    obtain ⟨role,read⟩:=direct u t hit
    exact resolved _ _ (p.primary_faces board m ((atRow u).val:Word w) order directory room π horizontal extra
      (col u) (columns u) endRow core (horiz u) (birth u) role e read)
  · intro i
    obtain ⟨u,t,atI⟩:=P.positive_source _ m e rfl atRow live creditM i
    have hit:=i.property.1
    have charged:=i.property.2
    rw [←atI] at hit charged
    obtain ⟨role,read⟩:=second u t hit charged
    exact resolved _ _ (p.mate_faces board m ((atRow u).val:Word w) order directory room π horizontal extra
      (col u) (columns u) endRow core role e read)

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
theorem StripPorts.direct_mate_result (p : Ports) (board : Board) (a : Area) (s : Sources) (g : LabelSource)
    (batch : Batch q ports) (pre m : Memory w) (P : PortPlan (fresh a s) batch pre a.rows)
    (mask other : Expr) (e : Fin board.rows) (π : Equiv.Perm (Fin (2^h)))
    (order : Fin board.coreRows≃Edges S h d k) (directory : CoreLookup.Loaded p.directory order m)
    (room : board.rows<2^w) (countRoom : a.occurrences≤2^w)
    (horizontal : H→DistinctPair C) (extra : A⊕B→DistinctPair (ColumnSite C k))
    (atRow : Ball ↪ Fin a.rows) (col : Ball→C → Columns h d)
    (place : Ball×ColumnSite C k ↪ Site h d k)
    (site : ∀u x,place (u,x)=Prod.map (col u) id x)
    (endRow : Fin board.rows→Site h d k×Site h d k)
    (core : ∀f,endRow (board.coreIndex (order.symm f))=CoreBoard.ends π f)
    (live : ∀j∈liveRows batch pre a.rows,∃u,atRow u=j)
    (archive : ∀i : Fin a.occurrences,
      (m (a.direct+i.val)).val=if kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns pre i=none
        then installedBits (fresh a s).columns pre i else 0)
    (columns : ∀u c,((p.column c).eval m ((atRow u).val:Word w)).val=((Fintype.equivFin _) (col u c)).val)
    (horiz : ∀u f l (v : Fin board.rows),((board.coreOnly (p.horizontal f l)).eval m ((atRow u).val:Word w)).val=v.val →
      Faces (Prod.map (col u) id) (ColumnWires.ends horizontal extra (.horizontal f l)) (endRow v))
    (birth : ∀u j (v : Fin board.rows),((p.probe j).eval m ((atRow u).val:Word w)).val=v.val →
      Faces (Prod.map (col u) id) (extra (.inr j)) (endRow v))
    (direct : ∀u t,(g.edge.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val=e.val →
      ∃r : Role,((p.primary board r).eval m ((atRow u).val:Word w)).val=e.val)
    (second : ∀u t,(other.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val=e.val →
      0<((PaidWidths.paidMate a s mask other).amount.eval m ((P.enum ⟨atRow u,t⟩).val:Word w)).val →
      ∃r : Role,((p.mate board r).eval m ((atRow u).val:Word w)).val=e.val)
    (Covers : Prop) (resolved : ∀u t, Faces (Prod.map (col u) id) t (endRow e) → Covers) :
    ((PaidWidths.paidDirect a s g).load m e≤ports*(batch.maxWidth*batch.copies) ∧
      (PaidWidths.paidMate a s mask other).load m e≤ports*(batch.maxWidth*batch.copies)) ∧
    (((PaidWidths.paidDirect a s g).Positive m e → Covers) ∧
      ((PaidWidths.paidMate a s mask other).Positive m e → Covers)) := by
  exact ⟨p.direct_mate_load board a s g batch pre m P mask other e π order directory room countRoom
    horizontal extra atRow col place site endRow core live archive columns horiz birth direct second,
    p.direct_mate_support board a s g batch pre m P mask other e π order directory room countRoom
    horizontal extra atRow col place site endRow core live archive columns horiz birth direct second Covers resolved⟩

end CatalogueRows
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
