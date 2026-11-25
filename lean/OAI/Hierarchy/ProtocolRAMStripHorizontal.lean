import OAI.Hierarchy.ProtocolRAMStripColumnPrograms
import OAI.Hierarchy.ProtocolRAMStripEdgeIDs
import OAI.Hierarchy.ProtocolRAMBoughtSockets
import OAI.Hierarchy.ProbePayloadFixedJoins

namespace OAI
/-! # The three physical horizontal edge kinds on original strip occurrences -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard PurchaseFrozen StockCommit
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {h d k R w H : ℕ} {S : PurchaseSampler}

/-- Canonical core orientation of a true fixed identification. -/
def fixedLink (u v : Columns h d) (adj : (permutationFabric h d).fixedAll (fabricBoard h d u) (fabricBoard h d v))
    (diff : u≠v) : Fixed h d :=
  if lt : Fintype.equivFin _ u<Fintype.equivFin _ v then ⟨(u,v),adj,lt⟩
  else ⟨(v,u),(permutationFabric h d).fixedAll_symm _ _ adj,
    lt_of_le_of_ne (le_of_not_gt lt) (fun same=>diff ((Fintype.equivFin _).injective same.symm))⟩

theorem fixedLink_touches (u v : Columns h d) (adj) (diff : u≠v) :
    CoreLookup.touches (fixedLink u v adj diff) u := by
  unfold fixedLink;split <;> simp [CoreLookup.touches]

theorem payload_tile (base : ℕ) (col : PayloadStrip.Columns (Stages h d)→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (installed : CoreLookup.Loaded base order m)
    (p : Fin (2^h)) (e : Fin (PayloadStrip.edgeCount (Stages h d))) (t : StageAt h d) (layer : ColumnLayer k)
    (tileAt : e.val=2*t.val+1) (wide : 2^h≤2^w) :
    (payloadHorizontal S h d k base col e layer).eval m (p.val:Word w)=((order.symm (.inr ((p,t),layer))).val:Word w) := by
  unfold payloadHorizontal
  rw [dite_eq_right (by omega)]
  let index : Fin (CoreLookup.positions h d) := ⟨p.val,p.isLt.trans_le (Nat.le_max_right _ _)⟩
  have pos : (⟨e.val/2,by
    change e.val/2 < Stages h d
    have bound : t.val < Stages h d := t.isLt
    omega⟩ : StageAt h d)=t :=
    Fin.ext (by change e.val/2=t.val; omega)
  rw [pos]
  exact installed.read (CoreLookup.tile t layer) .row (p.val:Word w) index
    (Fin.val_cast_of_lt (p.isLt.trans_le wide)) _ (CoreLookup.resolve_tile p t layer)

theorem payload_fixed (base : ℕ) (col : PayloadStrip.Columns (Stages h d)→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (installed : CoreLookup.Loaded base order m)
    (r : Word w) (e : Fin (PayloadStrip.edgeCount (Stages h d))) (even : e.val%2=0) (layer : ColumnLayer k)
    (fromCol toCol : Columns h d) (adj : (permutationFabric h d).fixedAll (fabricBoard h d fromCol) (fabricBoard h d toCol))
    (diff : fromCol≠toCol)
    (live : ((col (Strip.horizontal (PayloadStrip.edgeCount (Stages h d)) e).left).eval m r).val=((Fintype.equivFin _) fromCol).val) :
    (payloadHorizontal S h d k base col e layer).eval m r=
      ((order.symm (.inl (.inr (.inr (.inl (fixedLink fromCol toCol adj diff,layer)))))).val:Word w) := by
  let index : Fin (CoreLookup.positions h d) := ⟨((Fintype.equivFin _) fromCol).val,
    ((Fintype.equivFin _) fromCol).isLt.trans_le (Nat.le_max_left _ _)⟩
  rw [payloadHorizontal,dite_eq_left even]
  exact installed.read _ _ _ index live _ (CoreLookup.resolve_fixed _ _ (fixedLink_touches ..) _)

/-- The actual immutable header and native shelf jointly supply all three
dispatched values. -/
theorem chain_keys (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (H start : ℕ)
    (key : Key h d k) (m : Shelf.Mem h d) (records : sh.PortData S π H key m)
    (ix : PurchaseDirectory.Index (2^h) S.degree H)
    (headLoaded : (StripDirectory.stratumHeader h d k S.degree H start).Loaded m)
    (keys : count h d k≤2^Native.wordBits h d Native.copies)
    (room : (H+1)*paths h S.degree H≤2^Native.wordBits h d Native.copies) :
    let head:=StripDirectory.stratumHeader h d k S.degree H start
    let localRow : Fin head.ports:=⟨ix.val,by change ix.val < 2^h*S.degree^H; simpa using ix.isLt⟩
    let atRow : Word (Native.wordBits h d Native.copies):=(head.enum ⟨key,localRow⟩).val
    (stageKey head h d k).eval m atRow=((stage key).val:Word _) ∧
    (∀ j,(rowKey sh S head h d k H j).eval m atRow=((Shelf.pathRows S π H key ix j).val:Word _)) ∧
    (∀ j,(digitKey sh S head h d k H j).eval m atRow=(((PurchaseDirectory.item ix).2 j).val:Word _)) := by
  intro head localRow atRow
  have pair:=StripDirectory.header_pair head m headLoaded key localRow
  have get (terms : Key h d k→Expr) :
      (BoughtSockets.select head terms).eval m atRow=(terms key).eval m (ix.val:Word _) :=
    BoughtSockets.select_read head terms m atRow (ix.val:Word _) key keys
      (by rw [pair.1,Fin.val_cast_of_lt (key.isLt.trans_le keys)]) pair.2
  refine ⟨get _,fun j=>(get _).trans (BoughtSockets.read_tile sh S π H key m records room ix j),
    fun j=>(get _).trans (records.directory.digit ix j)⟩

theorem chain_tile (sh : Shelf) (S : PurchaseSampler) (base start : ℕ) (col : ChainStrip.Columns H→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (installed : CoreLookup.Loaded base order m)
    (e : Fin (ChainStrip.edgeCount H)) (j : Fin (H+1)) (which : e.val=2*j.val) (layer : ColumnLayer k)
    (r : Word w) (t : StageAt h d) (p : Fin (2^h))
    (stagesFit : Stages h d≤2^w)
    (stageAtRow : ((stageKey (StripDirectory.stratumHeader h d k S.degree H start) h d k).eval m r).val=t.val)
    (recordAtRow : ((rowKey sh S (StripDirectory.stratumHeader h d k S.degree H start) h d k H j).eval m r).val=p.val) :
    (chainHorizontal sh S h d k H base start col e layer).eval m r=((order.symm (.inr ((p,t),layer))).val:Word w) := by
  let head:=StripDirectory.stratumHeader h d k S.degree H start
  let index : Fin (CoreLookup.positions h d) := ⟨p.val,p.isLt.trans_le (Nat.le_max_right _ _)⟩
  unfold chainHorizontal
  rw [dite_eq_left (by omega)]
  have pos : (⟨e.val/2,by have := j.isLt;omega⟩ : Fin (H+1))=j :=
    Fin.ext (by change e.val/2=j.val; omega)
  rw [pos,eval_chooseField _ 0 _ _ m r t (by simpa using stagesFit) (by simpa using stageAtRow)]
  exact installed.read _ _ _ index recordAtRow _ (CoreLookup.resolve_tile p t layer)

theorem chain_sample (sh : Shelf) (S : PurchaseSampler) (base start : ℕ) (col : ChainStrip.Columns H→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (installed : CoreLookup.Loaded base order m)
    (e : Fin (ChainStrip.edgeCount H)) (j : Fin H) (which : e.val=2*j.val+1) (layer : ColumnLayer k)
    (r : Word w) (c : Columns h d) (digit : Fin S.degree) (edge : Sample S h d)
    (degreeFit : S.degree≤2^w)
    (digitAtRow : ((digitKey sh S (StripDirectory.stratumHeader h d k S.degree H start) h d k H j).eval m r).val=digit.val)
    (colAt : ((col (Strip.horizontal (ChainStrip.edgeCount H) e).left).eval m r).val=((Fintype.equivFin _) c).val)
    (physical : CoreLookup.neighbor S c digit=some edge) :
    (chainHorizontal sh S h d k H base start col e layer).eval m r=
      ((order.symm (.inl (.inr (.inr (.inr (edge,layer)))))).val:Word w) := by
  let index : Fin (CoreLookup.positions h d) := ⟨((Fintype.equivFin _) c).val,
    ((Fintype.equivFin _) c).isLt.trans_le (Nat.le_max_left _ _)⟩
  unfold chainHorizontal
  rw [dite_eq_right (by omega)]
  have pos : (⟨e.val/2,by have := j.isLt;omega⟩ : Fin H)=j :=
    Fin.ext (by change e.val/2=j.val; omega)
  rw [pos,eval_chooseField _ 0 _ _ m r digit (by simpa using degreeFit) (by simpa using digitAtRow)]
  exact installed.read _ _ _ index colAt _ (CoreLookup.resolve_sample _ _ _ physical _)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
