import OAI.Hierarchy.TaggedWireEarnedCoordinate
import OAI.Hierarchy.ProbePaidStripTree
import OAI.Hierarchy.ProbePaidTreeArchive
import OAI.Hierarchy.ProtocolRAMSelectorChargeTable
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # Exact broadcast charge on the earned packet's physical tree lanes -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip StockCommit
open ThreeFlat.RAM DescriptorExpr
open scoped BigOperators Classical Fin.CommRing
variable {sam : PurchaseSampler} {h d k n w K : ℕ} {A B Ball : Type}
local notation "T" => TreeLink n k
local notation "R" => ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k
local notation "Ports" => StripPorts sam h d k (TreeColumn n) (Fin n) B
variable (p : StripPorts sam h d k (TreeColumn n) (Fin n) B) (b : Board) (a : Area) (t : Traversals) (m : Memory w) (pos : 0<b.coreRows)

/-- Enumerating the two authenticated traversal columns recovers every copy
of every tree link on the candidate row, including repeated edge IDs. -/
theorem measured_tree_load (copies maxBits : ℕ) (e : Fin b.rows) (reads : t.Reads m (fun i : Fin a.rows => broadcastWalk p b m i.val pos))
    (size : maxBits<2^w) (copyFit : copies<2^w)
    (bound : ∀i : Fin a.rows,(m (a.broadcast+i.val)).val≤ maxBits)
    (full : ∀i : Fin a.rows,copies*(m (a.broadcast+i.val)).val<2^w) :
    (PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m e =
      ∑i : Fin a.rows, ∑l : T,if b.coreIndex (treeTarget p b m i.val l pos)=e
        then copies*(m (a.broadcast+i.val)).val else 0 := by
  let s:=PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits
  let num:=Fintype.card T
  let path (i : Fin a.rows):=broadcastWalk p b m i.val pos
  have length (i : Fin a.rows) : (path i).length=num := by simp [path,num,broadcastWalk]
  let loc : Fin s.count ≃ (Σ _ : Fin a.rows,Fin num) :=
    reads.enum.trans (Equiv.sigmaCongrRight (fun i=>finCongr (length i)))
  have owner (i : Fin s.count) : (t.sourceRow.eval m (i.val:Word w)).val=(loc i).1.val :=
    reads.ownerAt i
  have amount (i : Fin s.count) : (s.amount.eval m (i.val:Word w)).val=copies*(m (a.broadcast+(loc i).1.val)).val :=
    PaidWidths.paidBroadcast_bits a _ _ _ _ _ _ _ m _ (loc i).1 (owner i) size (bound _) copyFit (full _)
  have key (i : Fin s.count) : (s.edge.eval m (i.val:Word w)).val=
      (b.coreIndex (treeTarget p b m (loc i).1.val ((Fintype.equivFin T).symm (loc i).2) pos)).val := by
    calc
      _ = ((path (reads.enum i).1)[(reads.enum i).2.val]'(reads.enum i).2.isLt).val := reads.edgeAt i
      _ = _ := by simp only [path, broadcastWalk, List.getElem_ofFn]; rfl
  let cell (i : Fin a.rows) (l : T) := if b.coreIndex (treeTarget p b m i.val l pos)=e
    then copies*(m (a.broadcast+i.val)).val else 0
  change s.load m e=∑i,∑l,cell i l
  unfold PaidWidths.Slice.load
  simp only [key,amount,Fin.val_inj]
  change (∑i,cell (loc i).1 ((Fintype.equivFin T).symm (loc i).2))=_
  rw [loc.sum_comp (fun x=>cell x.1 ((Fintype.equivFin T).symm x.2)),Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _=>(Fintype.equivFin T).symm.sum_comp (cell i))

private theorem core_only_range (x : Expr) (m : Memory w) (r : Word w) (wide : b.rows<2^w)
    (valid : ((b.coreOnly x).eval m r).val<b.rows) : ((b.coreOnly x).eval m r).val<b.coreRows := by
  have coreFit : b.coreRows<2^w := by unfold Board.rows at wide;omega
  by_cases low : (x.eval m r).val<b.coreRows
  · simpa only [Board.coreOnly,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,
      Fin.val_cast_of_lt coreFit,ite_eq_left low] using low
  · simp only [Board.coreOnly,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,
      Fin.val_cast_of_lt coreFit,ite_eq_right low,Fin.val_cast_of_lt wide,lt_self_iff_false] at valid

/-- The fallback zero of a dormant row is never used for a genuine earned
tree link. All active native tree terms are already in the original core. -/
theorem earned_tree_target (r : ℕ) (l : T) (wide : b.rows<2^w)
    (valid : ((p.primary b (treeRole n k l:R)).eval m (r:Word w)).val<b.rows) :
    (b.coreIndex (treeTarget p b m r l pos)).val=((p.primary b (treeRole n k l:R)).eval m (r:Word w)).val := by
  have eq : treeTerm p b l=p.primary b (treeRole n k l:R) := by rcases l with j|⟨c,j,side⟩ <;> rfl
  have core : ((p.primary b (treeRole n k l:R)).eval m (r:Word w)).val<b.coreRows := by
    rcases l with j|⟨c,j,side⟩ <;> exact core_only_range b _ m _ wide valid
  change (if ((treeTerm p b l).eval m (r:Word w)).val<b.coreRows then _ else 0)=_
  rw [eq,ite_eq_left core]

/-- Convert the archived broadcast to a sum over the elected packets' actual
tree operands. Inactive candidates vanish even if their padded row maps to zero. -/
theorem measured_elected_tree_load (copies maxBits : ℕ) (e : Fin b.rows) (reads : t.Reads m (fun i : Fin a.rows => broadcastWalk p b m i.val pos))
    (size : maxBits<2^w) (copyFit : copies<2^w) (wide : b.rows<2^w)
    (bound : ∀i : Fin a.rows,(m (a.broadcast+i.val)).val≤ maxBits)
    (full : ∀i : Fin a.rows,copies*(m (a.broadcast+i.val)).val<2^w)
    (keep : Fin a.rows→Prop) (selectors : Subtype keep→ℕ)
    (price : ∀i : Subtype keep,(m (a.broadcast+i.val.val)).val=selectors i)
    (idle : ∀i,¬keep i→(m (a.broadcast+i.val)).val=0)
    (valid : ∀i : Subtype keep,∀l:T,((p.primary b (treeRole n k l:R)).eval m (i.val.val:Word w)).val<b.rows) :
    (PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m e=
      ∑i : Subtype keep, ∑l : T,if ((p.primary b (treeRole n k l:R)).eval m (i.val.val:Word w)).val=e.val
        then copies*selectors i else 0 := by
  rw [measured_tree_load p b a t m pos copies maxBits e reads size copyFit bound full]
  let term (i : Fin a.rows) := ∑l : T,if b.coreIndex (treeTarget p b m i.val l pos)=e
      then copies*(m (a.broadcast+i.val)).val else 0
  change (∑i,term i)=_
  rw [←Fintype.sum_subtype_add_sum_subtype keep term]
  have empty : (∑i : {r // ¬keep r},term i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [term,idle i.val i.property]
  rw [empty,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  change (∑l : T,if b.coreIndex (treeTarget p b m i.val.val l pos)=e
      then copies*(m (a.broadcast+i.val.val)).val else 0)=_
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fin.ext_iff,earned_tree_target (A:=A) p b m pos i.val.val l wide (valid i l),price i]

/-- A source-indexed installation supplies exactly the valid core operand
premise at any later memory preserving the original paid banks. -/
theorem EarnedInstall.tree_range_at [Fintype A] [Fintype B] [Fintype Ball]
    {p : Ports} {b : Board} {π : Equiv.Perm (Fin (2^h))} {extra : A⊕B→DistinctPair (TreeSite n k)}
    {place : Ball×TreeSite n k↪Fin K} {u : Ball} {endRow : Fin b.rows→Site h d k×Site h d k}
    {name : Site h d k↪Fin K} {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
    (g : EarnedInstall p b π extra place u endRow name addr m reg)
    (out : Memory w) (cut : ℕ) (low : PrefixAgreement.Low cut out m)
    (safe : ∀r:R,(p.primary b r).Fits w cut) (l : T) :
    ((p.primary b (treeRole n k l:R)).eval out reg).val<b.rows := by
  have paid : paidRole (treeRole n k l:R) := by rcases l with a|⟨c,j,side⟩ <;> trivial
  rw [PrefixAgreement.expr _ out m cut (PrefixAgreement.inputEnd_of_fits _ (safe _)) low reg,
    g.placed.2.choose_spec.choose_spec.1 _ paid]
  exact (g.index (treeRole n k l)).isLt

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical
variable {F E D : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype D]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : D→E} {box : Set (E→ℝ)}
  {ε tree : ℝ} {N W q d : ℕ} (menu : Probe.FixedMenu F edge req box ε tree N)

/-- At a committed candidate the price bank supplies the selector width of the
elected packet's public menu ordinal. An uncommitted candidate has a zero
archived selector, including on padded rows. -/
theorem archived_selector_bits (C : Chart W q d) (flag : ℕ) (mem : Memory W) (pre post : List Event)
    (event : Attempt) (split : events C.mesh=pre++(.attempt event)::post)
    (a : StockCommit.Area) (src : StockCommit.Sources) (g : StockCommit.LabelSource) (b : Batch q d)
    (i : Fin a.rows) (v : Memory W) (physical : C.commit event=StockCommit.pricedSegment a src g W b)
    (snap : PurchaseStage.postOutput (C.layout event) (repair C event) (prepared C event (run C pre mem))=v)
    (ready : (StockCommit.pricedSegment a src g W b).ready v)
    (bc : BroadcastRoom (StockCommit.fresh a src) b a.rows W)
    (qFit : q≤2^W) (copyFit : b.copies<2^W) (sumFit : q*b.copies<2^W)
    (eligible : mounted C post (after C (.attempt event) (run C pre mem)))
    (keep : ∀x∈post,protected C (a.broadcast+i.val) x) (apart : a.broadcast+i.val≠flag)
    (base : ℕ) (table : (StockCommit.fresh a src).price=(MenuROM.selectorCharges menu base).bank 0)
    (rom : (MenuROM.selectorCharges menu base).Resident (StockCommit.stageInput a src g v))
    (chosen : committed b (StockCommit.stageInput a src g v) (i.val:Word W)→menu.index)
    (tag : ∀h, b.packet.eval (StockCommit.stageInput a src g v) (i.val:Word W)=
       (((Fintype.equivFin _ (chosen h)).val+1:ℕ):Word W))
    (fits : ∀h, (menu.packet (chosen h)).selectorBits<2^W) :
    (checkedOut C flag mem (a.broadcast+i.val)).val=
      if h : committed b (StockCommit.stageInput a src g v) (i.val:Word W)
        then (menu.packet (chosen h)).selectorBits else 0 := by
  rw [archived_broadcast C flag mem pre post event split a src g b i v physical snap ready bc qFit copyFit
    sumFit eligible keep apart]
  by_cases h : committed b (StockCommit.stageInput a src g v) (i.val:Word W)
  · rw [ite_eq_left h,dite_eq_left h,table,tag h,MenuROM.charge_lookup menu base _ rom (chosen h),Fin.val_cast_of_lt (fits h)]
  · simp [h]

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
