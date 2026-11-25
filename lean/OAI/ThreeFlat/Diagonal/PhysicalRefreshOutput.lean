import OAI.ThreeFlat.Diagonal.CompressorHalfPorts
import OAI.ThreeFlat.Diagonal.RefreshPartyBounds
import OAI.ThreeFlat.Diagonal.PhysicalRefreshCharge
import OAI.ThreeFlat.Diagonal.PhysicalRefreshCall
import OAI.ThreeFlat.Diagonal.RefreshCursorAddresses
import OAI.ThreeFlat.RAM.NavigationNodeRows

namespace OAI
/-! # The physical state and all retained refresh arrays at the native continuation -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory CompressorPacking Native
open RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {W s rem h pad K : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)
set_option quotPrecheck false
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "G" => numberedRefreshGraph A
local notation "E" => DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero
local notation "m" => 2^s
local notation "d" => 1+h+pad
local notation "v" => Fintype.card A.Base
local notation "n" => v*m*2^rem
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn

structure RefreshOutput (K : ℕ) (cur : Word W) (csr : Cursor) (branch : Fin (M).rules.count)
    (prepared out : Memory W) : Prop where
  pointer : (out cur.val).val=csr.header+64
  graph : let X := (M).next branch
    SlotImage.Stored X.graph X.order (tagOrdinal rem) (nextColumns (allocate K csr (.refresh v m (2^rem) h pad)) v m h pad)
      (fun i=>(out i).val) X.width
  records : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ q,Records.Reads out (CursorSpace.recordPointers en) csr.header K (CompressorRefresh.graph G E hm pad)
      (refreshNumericWidths T A hm hh sym rows zero conn branch) (fun i=>(prepared i).val) q
  sparse : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ (u : A.Base×BitWord rem) (p : Fin m) (j : Fin h), (out (en.words 3+(blockId (numBlock A u)*m+p.val)*h+j.val)).val=
      T.widths (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
        (refreshBinaryBranchOrder T A hm hh sym rows zero conn branch) u ((numbering c rows).symm (p,j))
  child : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ i : Fin n,out (en.words 42+i.val)=(csr.node+RefreshOwnership.child m (2^rem) i.val:Word W)
  owner : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ i : Fin n,out (en.words 44+i.val)=(RefreshOwnership.owner m (2^rem) i.val:Word W)
  descriptors : ∀ i,csr.heap≤ i → i<csr.heap+3*(v*2^rem) → out i=prepared i
  frame : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ i,i≠cur.val → (i<csr.heap ∨ en.next.heap≤ i) → out i=prepared i
  degreeWord : (out (csr.header+48)).val=2^s
  archivedHeader : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ j,j≤63→(out (csr.header+j)).val=en.words j
  headerBelow : csr.header+64≤csr.heap
  oldRanges : csr.graph+6*(v*m)≤csr.heap ∧ csr.width+v*m*(m*2^rem)≤csr.heap
  archivedSource : let en := allocate K csr (.refresh v m (2^rem) h pad)
    ∀ r : Fin 7→Word W,(r 0).val=csr.header→
      RefreshParty.Source out r G (oldColumns csr v m) (en.words 12) (numberedRefreshWidths A)


/-- Physical numbering before and after the owner transpose. -/
def refreshOldOrder (A : State (2^s) (s+rem)) : A.Site ≃ Fin (Fintype.card A.Base*2^s*2^rem) :=
  (A.chart.symm.trans (RefreshStageLayout.pair A.order (tagOrdinal (s+rem)))).trans
    (finCongr (by rw [pow_add,Nat.mul_assoc]))

def refreshFinalOrder (branch : Fin (M).rules.count) : ((M).next branch).Site ≃ Fin n :=
  (((M).next branch).chart.symm.trans ((A.order.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _))).trans
    Records.siteOrder

def refreshParentSites (branch : Fin (M).rules.count) : A.Site ≃ ((M).next branch).Site :=
  A.chart.symm.trans (StageAddress.refreshSite (splitWord s rem) (tagOrdinal s).symm)

theorem refreshParentSites_apply (branch : Fin (M).rules.count) (x : A.Site) :
    refreshParentSites T A hm hh sym rows zero conn branch x=(M).rules.owner branch x := rfl

/-- There is exactly one old site in each refresh child row. -/
def refreshChildFiber (branch : Fin (M).rules.count) (y : ((M).next branch).Site) :
    Fin 1 ≃ {x : A.Site // (M).rules.owner branch x=y} :=
  let p := refreshParentSites T A hm hh sym rows zero conn branch
  { toFun := fun _ => ⟨p.symm y,p.apply_symm_apply y⟩
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun x => Subtype.ext (by
      apply p.injective
      rw [p.apply_symm_apply]
      exact x.property.symm) }

theorem refresh_owner_ordinals (branch : Fin (M).rules.count) (x : A.Site) :
    let old := (refreshOldOrder A x).val
    let new := (refreshFinalOrder T A hm hh sym rows zero conn branch ((M).rules.owner branch x)).val
    RefreshOwnership.child m (2^rem) new=old ∧ RefreshOwnership.owner m (2^rem) old=new := by
  dsimp only
  let p := A.chart.symm x
  let base := A.order p.1
  let bits := splitWord s rem p.2
  let port := tagOrdinal s bits.1
  let lane := tagOrdinal rem bits.2
  have old : (refreshOldOrder A x).val=
      RefreshOwnership.oldSite m (2^rem) base.val port.val lane.val := by
    change (RefreshStageLayout.pair A.order (tagOrdinal (s+rem)) p).val=_
    rw [RefreshStageLayout.pair_index,ordinal_split,pow_add]; rfl
  have fresh : (refreshFinalOrder T A hm hh sym rows zero conn branch ((M).rules.owner branch x)).val=
      RefreshOwnership.newSite m (2^rem) base.val port.val lane.val := by
    change (Records.siteOrder ((base,port),bits.2)).val=_
    exact Records.siteOrder_val _
  rw [old,fresh]
  exact RefreshOwnership.true_site base bits.1 bits.2

def refreshOutputLayer (K : ℕ) (csr : Cursor) (bases ports lanes degree padding : ℕ) :
    NavigationNodeRows.Layer :=
  let en := allocate K csr (.refresh bases ports lanes degree padding)
  ⟨en.next.node,bases*ports*lanes,2,1,en.words 42,en.words 34,en.words 38,csr.header⟩

/-- The archived row contains its physical predecessor, both halves of each new slot,
and the copy count in the selected three-word choice record. -/
def refreshOutputData (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) (prepared : Memory W) :
    NavigationNodeRows.LayerData (refreshOutputLayer K csr v m (2^rem) h pad) where
  child j _ := csr.node+RefreshOwnership.child m (2^rem) j.val
  halfWidth j := List.ofFn fun i : Fin (2*d) =>
    refreshNumericWidths T A hm hh sym rows zero conn branch
      (ShrinkStage.Halves.sourceHalf (CompressorRefresh.graph G E hm pad) (Records.siteOrder.symm j) i)
  motifCopies j :=
    let u := Records.siteOrder.symm j
    let en := allocate K csr (.refresh v m (2^rem) h pad)
    [(prepared (en.words 2+blockId (u.1.1,u.2)*3)).val]

theorem refresh_child_id (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) (prepared : Memory W)
    (y : ((M).next branch).Site) (j : Fin 1) :
    (refreshOutputData T A hm hh sym rows zero conn K csr branch prepared).child
      (refreshFinalOrder T A hm hh sym rows zero conn branch y) j =
    csr.node+(refreshOldOrder A ((refreshChildFiber T A hm hh sym rows zero conn branch y) j).val).val := by
  let q := (refreshChildFiber T A hm hh sym rows zero conn branch y) j
  have eq := (refresh_owner_ordinals T A hm hh sym rows zero conn branch q.val).1
  rw [q.property] at eq
  exact congrArg (csr.node+·) eq

theorem RefreshOutput.owner_index {K : ℕ} {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count}
    {prepared out : Memory W} (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out)
    (nodeRoom : n≤2^W) (x : A.Site) :
    let en := allocate K csr (.refresh v m (2^rem) h pad)
    (out (en.words 44+(refreshOldOrder A x).val)).val =
      (refreshFinalOrder T A hm hh sym rows zero conn branch ((M).rules.owner branch x)).val := by
  let fresh := refreshFinalOrder T A hm hh sym rows zero conn branch ((M).rules.owner branch x)
  have eq := result.owner (refreshOldOrder A x)
  rw [(refresh_owner_ordinals T A hm hh sym rows zero conn branch x).2] at eq
  exact (congrArg Fin.val eq).trans (Fin.val_cast_of_lt (fresh.isLt.trans_le nodeRoom))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
/-- The child, half-width and motif-count reads used by the chronological navigation pass
all lie in the completed stage allocation. -/
theorem RefreshOutput.archiveHalfTail {K : ℕ} {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count}
    {prepared out : Memory W} (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out)
    (heapRoom : (allocate K csr (.refresh v m (2^rem) h pad)).next.heap ≤ 2^W)
    (nodesRoom : csr.node+n ≤ 2^W) :
    let data := refreshOutputData T A hm hh sym rows zero conn K csr branch prepared
    data.Reads (fun x => (out x).val) ∧ data.Below (allocate K csr (.refresh v m (2^rem) h pad)).next.heap
      (fun x => (out x).val) ∧
      data.Footprint (fun x=>csr.heap≤x ∧ x<(allocate K csr (.refresh v m (2^rem) h pad)).next.heap)
        (fun x=>(out x).val) ∧
    ∀ j : Fin n,(data.halfWidth j).sum<2^W →
      let last := (out ((refreshOutputLayer K csr v m (2^rem) h pad).incident+j.val*2+1)).val+4*(2*d-1)
      csr.heap≤last+3 ∧ last+3<(allocate K csr (.refresh v m (2^rem) h pad)).next.heap ∧
      (out (last+3)).val+(out (last+2)).val=(data.halfWidth j).sum := by
  let en := allocate K csr (.refresh v m (2^rem) h pad)
  change en.next.heap ≤ 2^W at heapRoom
  let P := CursorSpace.recordPointers en
  let graph := CompressorRefresh.graph G E hm pad
  let width := refreshNumericWidths T A hm hh sym rows zero conn branch
  let u := (Records.siteOrder («v» := v) («m» := m) (t:=rem)).symm
  let data := refreshOutputData T A hm hh sym rows zero conn K csr branch prepared
  change data.Reads (fun x => (out x).val) ∧ data.Below en.next.heap (fun x => (out x).val) ∧
    data.Footprint (fun x=>csr.heap≤x ∧ x<en.next.heap) (fun x=>(out x).val) ∧
    ∀ j : Fin n,(data.halfWidth j).sum<2^W →
      let last := (out (P.headers+j.val*2+1)).val+4*(2*d-1)
      csr.heap≤last+3 ∧ last+3<en.next.heap ∧ (out (last+3)).val+(out (last+2)).val=(data.halfWidth j).sum
  have id (j : Fin n) : Records.siteId ((u j).1.1,(u j).2) (u j).1.2=j.val :=
    (Records.siteOrder_val (u j)).symm.trans (congrArg Fin.val (u.symm_apply_apply j))
  have ordinal (q : Records.Table) (j : Fin n) (f : Fin (q.cols d)) :
      (Records.rowOrder d q (u j,f)).val=j.val*q.cols d+f.val := by
    rw [Records.rowOrder,RefreshStageLayout.pair_index]
    simp only [u,Equiv.apply_symm_apply,Equiv.refl_apply]
  have word (q : Records.Table) (j : Fin n) (f : Fin (q.cols d)) :
      out (P.dst q+j.val*q.cols d+f.val) =
        (q.value P csr.header K graph width (fun x=>(prepared x).val) (u j,f):Word W) := by
    simpa only [ordinal,Nat.add_assoc] using result.records q (u j,f)
  obtain ⟨_,startR,_,_,endR⟩ := CursorSpace.retained_addresses
    (c:=csr) (K:=K) («v» := v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  obtain ⟨lastChild,lastOwner,_,_⟩ := RefreshNodeOwners.owner_spans
    (c:=csr) (K:=K) («v» := v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  change en.words 42+n=en.words 44 at lastChild
  change en.words 44+n=en.next.heap at lastOwner
  have below (q : Records.Table) (j : Fin n) (f : Fin (q.cols d)) :
      P.dst q+j.val*q.cols d+f.val<en.next.heap := by
    have hi := (Records.rowOrder d q (u j,f)).isLt
    rw [ordinal] at hi
    have box : P.dst q+n*q.cols d≤en.words 42 := endR q
    omega
  have val {addr x : ℕ} (stored : out addr=(x:Word W)) (room : x<2^W) : (out addr).val=x :=
    (congrArg Fin.val stored).trans (Fin.val_cast_of_lt room)
  have halfCount (j : Fin n) : (out (P.headers+j.val*2)).val=2*d := by
    have r := word .halfHeader j (0 : Fin 2)
    change out (P.headers+j.val*2+0)=((2*d:ℕ):Word W) at r
    have f : 2*d<8*d := by omega
    have b := below .halves j ⟨2*d,f⟩
    change P.halves+j.val*(8*d)+2*d<en.next.heap at b
    exact val (x:=2*d) (by simpa only [Nat.add_zero] using r)
      ((Nat.le_add_left (2*d) _).trans_lt (b.trans_le heapRoom))
  have halfPtr (j : Fin n) : (out (P.headers+j.val*2+1)).val=P.halves+j.val*(8*d) := by
    have r := word .halfHeader j (1 : Fin 2)
    change out (P.headers+j.val*2+1)=((P.halves+Records.siteId ((u j).1.1,(u j).2) (u j).1.2*(8*d):ℕ):Word W) at r
    rw [id] at r
    have b := below .halves j ⟨0,by change 0<8*(1+h+pad); positivity⟩
    change P.halves+j.val*(8*d)+0<en.next.heap at b
    exact val r (by simpa only [Nat.add_zero] using b.trans_le heapRoom)
  have halfValue (j : Fin n) (k : Fin (2*d)) :
      (out (P.halves+j.val*(8*d)+(4*k.val+2))).val =
        width (ShrinkStage.Halves.sourceHalf graph (u j) k) := by
    have r := word .halves j (Records.halfCol (k,2))
    simp only [Records.Table.value,Equiv.symm_apply_apply] at r
    change out (P.halves+j.val*(8*d)+(Records.halfCol (k,2)).val)=
      (width (ShrinkStage.Halves.sourceHalf graph (u j) k):Word W) at r
    rw [Records.halfCol_val,Nat.mul_comm k.val 4] at r
    apply val r
    obtain ⟨e,he⟩ := (numFreshEdge A).surjective (ShrinkStage.Halves.sourceHalf graph (u j) k)
    have num : width (numFreshEdge A e)=((M).next branch).width e :=
      refreshBinary_width_numeric T A rows hm hh sym zero conn branch e
    rw [←he,num,←result.graph.widthWord e]
    exact Fin.isLt _
  have motifCount (j : Fin n) : (out (P.kernel+j.val*5+3)).val=1 := by
    have r := word .kernel j (3 : Fin 5)
    change out (P.kernel+j.val*5+3)=(1:Word W) at r
    have b := below .kernel j (3 : Fin 5)
    change P.kernel+j.val*5+3<en.next.heap at b
    exact val (x:=1) r (by have cap:=b.trans_le heapRoom; omega)
  have motifPtr (j : Fin n) : (out (P.kernel+j.val*5+4)).val=P.motif+j.val*6 := by
    have r := word .kernel j (4 : Fin 5)
    change out (P.kernel+j.val*5+4)=((P.motif+Records.siteId ((u j).1.1,(u j).2) (u j).1.2*6:ℕ):Word W) at r
    rw [id] at r
    have b := below .motif j (0 : Fin 6)
    change P.motif+j.val*6+0<en.next.heap at b
    exact val r (by simpa only [Nat.add_zero] using b.trans_le heapRoom)
  have motifValue (j : Fin n) : (out (P.motif+j.val*6+3)).val =
      (prepared (P.choices+blockId ((u j).1.1,(u j).2)*3)).val := by
    have r := word .motif j (3 : Fin 6)
    change out (P.motif+j.val*6+3)=((prepared (P.choices+blockId ((u j).1.1,(u j).2)*3)).val:Word W) at r
    exact val r (Fin.isLt _)
  have childBound (j : Fin n) : RefreshOwnership.child m (2^rem) j.val < n := by
    let p := (u j).1.2
    let l := tagOrdinal rem (u j).2
    let b := (u j).1.1
    have row : j.val=RefreshOwnership.newSite m (2^rem) b.val p.val l.val := (id j).symm
    rw [row,RefreshOwnership.child_new]
    have tail : p.val+m*l.val < m*2^rem := by
      calc
        _ < m+m*l.val := Nat.add_lt_add_right p.isLt _
        _ = (l.val+1)*m := by ring
        _ ≤ 2^rem*m := Nat.mul_le_mul_right _ l.isLt
        _ = _ := Nat.mul_comm ..
    calc
      _ < b.val*(m*2^rem)+m*2^rem := Nat.add_lt_add_left tail _
      _ = (b.val+1)*(m*2^rem) := by ring
      _ ≤ v*(m*2^rem) := Nat.mul_le_mul_right _ b.isLt
      _ = _ := by ring
  have len (j : Fin n) : (data.halfWidth j).length=2*d := List.length_ofFn
  have singleton (j : Fin n) : (data.motifCopies j).length=1 := rfl
  have legacy : data.Reads (fun x=>(out x).val) ∧ data.Below en.next.heap (fun x=>(out x).val) := by
    constructor
    · constructor
      · intro j i
        have only : i.val=0 := by have := i.isLt; change i.val<1 at this; omega
        have stored := result.child j
        rw [←Nat.cast_add] at stored
        have g := val stored ((Nat.add_lt_add_left (childBound j) csr.node).trans_le nodesRoom)
        simpa only [data,refreshOutputData,refreshOutputLayer,only,Nat.mul_one,Nat.add_zero] using g
      · intro j
        exact (halfCount j).trans (len j).symm
      · intro j i
        let k : Fin (2*d) := ⟨i.val,(len j) ▸ i.isLt⟩
        change (out ((out (P.headers+j.val*2+1)).val+(4*i.val+2))).val=_
        rw [halfPtr j]
        refine (halfValue j k).trans ?_
        let widths := fun z : Fin (2*d) => width (ShrinkStage.Halves.sourceHalf graph (u j) z)
        have within : i.val < (List.ofFn widths).length := i.isLt
        exact (List.getElem_ofFn (f:=widths) within).symm
      · intro _ j
        exact (motifCount j).trans (singleton j).symm
      · intro _ j i
        have only : i.val=0 := Nat.lt_one_iff.mp (show i.val < 1 from i.isLt)
        change (out ((out (P.kernel+j.val*5+4)).val+(6*i.val+3))).val=_
        rw [motifPtr j]
        have first : i = ⟨0,by exact Nat.zero_lt_one⟩ := Fin.ext only
        rw [first]
        exact motifValue j
    · constructor
      · intro j i
        change en.words 42+j.val*1+i.val<en.next.heap
        have fj : j.val<n := j.isLt
        have fi : i.val<1 := i.isLt
        omega
      · intro j
        exact below .halfHeader j (1 : Fin 2)
      · intro j i
        let k : Fin (2*d) := ⟨i.val,(len j) ▸ i.isLt⟩
        change (out (P.headers+j.val*2+1)).val+(4*i.val+2)<en.next.heap
        rw [halfPtr j]
        have b := below .halves j (Records.halfCol (k,2))
        change P.halves+j.val*(8*d)+(Records.halfCol (k,2)).val<en.next.heap at b
        rw [Records.halfCol_val,Nat.mul_comm k.val 4] at b
        exact b
      · intro _ j
        exact below .kernel j (4 : Fin 5)
      · intro _ j i
        have only : i.val=0 := Nat.lt_one_iff.mp (show i.val < 1 from i.isLt)
        change (out (P.kernel+j.val*5+4)).val+(6*i.val+3)<en.next.heap
        rw [motifPtr j,only]
        exact below .motif j (3 : Fin 6)
  refine ⟨legacy.1,legacy.2,?_⟩
  have top := legacy.2.footprint
  obtain ⟨_,km,mh,hhp,_⟩ := CursorSpace.record_layout
    (c:=csr) (K:=K) («v» := v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  change csr.heap+3*(v*2^rem)≤P.kernel at startR
  change P.kernel+n*5=P.motif at km
  change P.motif+n*6=P.headers at mh
  change P.headers+n*2=P.halves at hhp
  have kc : P.kernel+n*5≤en.words 42 := endR .kernel
  constructor
  · constructor
    · intro j i
      exact ⟨by change csr.heap≤en.words 42+_+_;omega,top.child j i⟩
    · intro j
      exact ⟨by change csr.heap≤P.headers+_;omega,top.halves j⟩
    · intro j
      exact ⟨by change csr.heap≤P.headers+_+_;omega,top.halfPtr j⟩
    · intro j i
      refine ⟨?_,top.width j i⟩
      change csr.heap≤(out (P.headers+j.val*2+1)).val+_
      rw [halfPtr j]
      omega
    · intro h j
      exact ⟨by change csr.heap≤P.kernel+_+_;omega,top.motifs h j⟩
    · intro h j
      exact ⟨by change csr.heap≤P.kernel+_+_;omega,top.motifPtr h j⟩
    · intro h j i
      refine ⟨?_,top.copies h j i⟩
      change csr.heap≤(out (P.kernel+j.val*5+4)).val+_
      rw [motifPtr j]
      omega
  · intro j small
    let k : Fin (2*d) := ⟨2*d-1,by omega⟩
    let f := fun i : Fin (2*d)=>width (ShrinkStage.Halves.sourceHalf graph (u j) i)
    have total : ShrinkStage.Halves.prefixValue graph width (u j) k+f k=(data.halfWidth j).sum := by
      change (∑ i : Fin (2*d),if i.val<k.val then f i else 0)+f k=(List.ofFn f).sum
      rw [List.sum_ofFn]
      calc
        _ = (∑ i : Fin (2*d),if i.val<k.val then f i else 0)+
            ∑ i : Fin (2*d),if i=k then f i else 0 := by simp
        _ = _ := by
          rw [←Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          by_cases eq : i=k
          · simp [eq]
          · have ne : i.val≠k.val := fun e=>eq (Fin.ext e)
            have lt : i.val<k.val := by have:=i.isLt;dsimp [k] at *;omega
            simp [eq,lt]
    have pre := word .halves j (Records.halfCol (k,3))
    simp only [Records.Table.value,Equiv.symm_apply_apply] at pre
    change out (P.halves+j.val*(8*d)+(Records.halfCol (k,3)).val)=
      (ShrinkStage.Halves.prefixValue graph width (u j) k:Word W) at pre
    rw [Records.halfCol_val,Nat.mul_comm k.val 4] at pre
    have limit:=below .halves j (Records.halfCol (k,3))
    change P.halves+j.val*(8*d)+(Records.halfCol (k,3)).val<en.next.heap at limit
    rw [Records.halfCol_val,Nat.mul_comm k.val 4] at limit
    have pr:=val pre (by omega)
    have wi:=halfValue j k
    change _=f k at wi
    dsimp only
    rw [halfPtr]
    change csr.heap≤P.halves+j.val*(8*d)+4*k.val+3 ∧
      P.halves+j.val*(8*d)+4*k.val+3<en.next.heap ∧
      (out (P.halves+j.val*(8*d)+4*k.val+3)).val+
      (out (P.halves+j.val*(8*d)+4*k.val+2)).val=(data.halfWidth j).sum
    simp only [Nat.add_assoc] at limit pr wi ⊢
    exact ⟨by omega,limit,(congrArg₂ Nat.add pr wi).trans total⟩

theorem RefreshOutput.archiveWithFootprint {K : ℕ} {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count}
    {prepared out : Memory W} (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out)
    (heapRoom : (allocate K csr (.refresh v m (2^rem) h pad)).next.heap ≤ 2^W)
    (nodesRoom : csr.node+n ≤ 2^W) :
    let data := refreshOutputData T A hm hh sym rows zero conn K csr branch prepared
    data.Reads (fun x => (out x).val) ∧ data.Below (allocate K csr (.refresh v m (2^rem) h pad)).next.heap
      (fun x => (out x).val) ∧
      data.Footprint (fun x=>csr.heap≤x ∧ x<(allocate K csr (.refresh v m (2^rem) h pad)).next.heap)
        (fun x=>(out x).val) := by
  obtain ⟨reads,low,foot,_⟩ := RefreshOutput.archiveHalfTail T A hm hh sym rows zero conn result heapRoom nodesRoom
  exact ⟨reads,low,foot⟩

theorem RefreshOutput.archive {K : ℕ} {cur : Word W} {csr : Cursor} {branch : Fin (M).rules.count}
    {prepared out : Memory W} (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out)
    (heapRoom : (allocate K csr (.refresh v m (2^rem) h pad)).next.heap ≤ 2^W)
    (nodesRoom : csr.node+n ≤ 2^W) :
    let data := refreshOutputData T A hm hh sym rows zero conn K csr branch prepared
    data.Reads (fun x => (out x).val) ∧ data.Below (allocate K csr (.refresh v m (2^rem) h pad)).next.heap
      (fun x => (out x).val) := by
  obtain ⟨reads,below,_⟩ := RefreshOutput.archiveWithFootprint T A hm hh sym rows zero conn result heapRoom nodesRoom
  exact ⟨reads,below⟩

private theorem successor_away (cur : Word W) (mem : Memory W) (i : ℕ) (hi : i≠cur.val) :
    NextStage.memory cur mem i=mem i := by
  simp only [NextStage.memory, writeMemory, ite_eq_right hi]

private theorem successor_header (cur : Word W) (mem : Memory W) (head : ℕ) (values : ℕ→ℕ)
    (data : Scans.Header cur mem head 63 values) :
    (NextStage.memory cur mem cur.val).val=values 4 := by
  simp only [NextStage.memory, writeMemory]
  exact data.get 4 (by decide)

set_option maxHeartbeats 1800000 in
theorem refresh_after_physical (cur : Word W) (mid : Memory W) (csr : Cursor)
    (uc : CursorSpace cur mid csr K v s rem h pad)
    (source : Source cur mid G (oldColumns csr v m)
      ((allocate K csr (.refresh v m (2^rem) h pad)).words 12) (numberedRefreshWidths A))
    (branch : Fin (M).rules.count) (fit : (Q).Fits K W)
    (parsed : ∀ (i : Fin (Q).motifs) (j : Fin K), (mid (csr.dense+i.val*K+j.val)).val=
      (HistogramRegister.words ((Q).rows fit) ((Q).sequence fit branch) i j).val)
    (bases : v*m≤2^W) (lanes : 2^rem<2^W) (deg : 2*d<2^W) (small : 6<2^W)
    (rom : m*h≤2^W) (rot : 2*m<2^W) (full : m*2^rem<2^W) (tiles : T.last+1≤2^W)
    (alphabet : refreshSymbolBound T≤K) (room : 1+2*m*m*A.maxWidth+refreshBaseBound T<2^W)
    (widthFit : refreshWidthFactor T*(1+A.maxWidth)<2^W) :
    RefreshOutput T A hm hh sym rows zero conn K cur csr branch mid (refreshAfter T sym rows zero cur K mid) := by
  let en := allocate K csr (.refresh v m (2^rem) h pad)
  let P := CursorSpace.recordPointers en
  let safe := fun i : ℕ=>i<csr.heap ∨ en.next.heap≤ i
  let p := refreshPost T sym rows zero cur K
  let r := recordScans cur m d K
  let o := RefreshNodeOwners.both cur m
  let memP := (p.pipeline cur).run mid
  let memR := (r.pipeline cur).run memP
  let memO := (o.pipeline cur).run memR
  let out := NextStage.memory cur memO
  let fresh := nextColumns en v m h pad
  change RefreshOutput T A hm hh sym rows zero conn K cur csr branch mid out
  have srcP := uc.post_safe E T.base (fun j=>Fintype.card (T.block j).Alphabet) (fun j=>(T.block j).bits) (poolOf T rows)
  have pf := p.run_spec cur mid csr.header 63 en.words safe uc.header (.inr uc.controls) uc.start_live srcP
  have up : CursorSpace cur memP csr K v s rem h pad := uc.frame _ pf.2.2
  have rf := r.run_spec cur memP csr.header 63 en.words safe up.header (.inr up.controls) up.start_live up.recorder_safe
  have ur : CursorSpace cur memR csr K v s rem h pad := up.frame _ rf.2.2
  have ofn := o.run_spec cur memR csr.header 63 en.words safe ur.header (.inr ur.controls) ur.start_live (RefreshNodeOwners.safe ur)
  have uo : CursorSpace cur memO csr K v s rem h pad := ur.frame _ ofn.2.2
  have m1 := refresh_publish_physical T A hm hh sym rows zero conn cur mid (oldColumns csr v m) fresh (en.words 12)
    K (en.words 3) source branch fit (by rw [show info (fun i=>(mid i).val) cur 1=csr.dense from uc.read 1 (by decide)]; exact parsed)
    uc.archive bases lanes (by omega) rom rot tiles alphabet room widthFit
  have descP (i : ℕ) (hi : i<csr.heap+3*(v*2^rem)) : memP i=mid i :=
    uc.post_retains E T.base _ _ (poolOf T rows) i hi
  have recordData := up.record_data (fun i=>(mid i).val) m1.2.1 (fun i _ hi=>congrArg Fin.val (descP i hi))
  have stored := Records.records_image recordData (up.record_limits small (by change 2^s<2^W; omega) deg lanes) up.record_alloc K
  have owner := RefreshNodeOwners.image ur (by change 2^s<2^W; omega) full
  obtain ⟨sa,ca,ga,wa,recordEnd⟩ := CursorSpace.retained_addresses (c:=csr) (K:=K) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
  obtain ⟨h34,h42,h44⟩ := CursorSpace.stage_bounds W cur mid uc
  change en.words 34 ≤ en.words 42 at h34
  change en.words 42 ≤ cur.val at h42
  change en.words 44+n ≤ cur.val at h44
  change csr.heap+3*(v*2^rem) ≤ en.words 34 at ca
  change en.words 3+v*2^rem*m*h ≤ en.words 34 at sa
  have heap34 : csr.heap≤en.words 34 := (Nat.le_add_right _ _).trans ca
  have heapEnd : csr.heap≤en.next.heap := by
    dsimp only [en]
    rw [heap_step]
    omega
  have ctrlRoom : en.next.heap≤cur.val := uc.controls
  have belowCtrl (j : ℕ) (hj : j≤63) : csr.header+j≠cur.val := by
    have earlier:=uc.earlier
    omega
  have nstep (i : ℕ) (other : i≠cur.val) : out i=memO i := successor_away cur memO i other
  have fromR (i : ℕ) (hi : i<en.words 42) : out i=memR i :=
    (nstep i (ne_of_lt (hi.trans_le h42))).trans (owner.2.2 i hi)
  have fromP (i : ℕ) (hi : i<en.words 34) : out i=memP i :=
    (fromR i (hi.trans_le h34)).trans (up.records_retain i hi)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (successor_header cur memO csr.header en.words uo.header).trans
      (header_words K csr (.refresh v m (2^rem) h pad)).2.2.1
  · apply m1.1.frame
    · exact fun i _ hi=>congrArg Fin.val (fromP i (hi.trans_le ga))
    · intro i _ hi
      rw [refreshBinary_next_base] at hi
      exact congrArg Fin.val (fromP i (hi.trans_le wa))
  · dsimp only
    intro q x
    have endR := recordEnd q
    change P.dst q+Records.length v m rem d q≤en.words 42 at endR
    have lt : (Records.rowOrder d q x).val < Records.length v m rem d q := (Records.rowOrder d q x).isLt
    exact (fromR _ ((Nat.add_lt_add_left lt (P.dst q)).trans_le endR)).trans (stored.2 q x)
  · dsimp only
    intro u pt j
    let q := (((numBlock A u),pt),j)
    have hi := (RefreshStageLayout.sparseEntries (pad:=pad) q).isLt
    rw [RefreshStageLayout.sparse_index] at hi
    have top : (blockId (numBlock A u)*m+pt.val)*h+j.val<v*2^rem*m*h := hi
    have addr : en.words 3+(blockId (numBlock A u)*m+pt.val)*h+j.val < en.words 34 := by
      rw [Nat.add_assoc]
      exact (Nat.add_lt_add_left top (en.words 3)).trans_le sa
    exact (congrArg Fin.val (fromP _ addr)).trans (m1.2.2 u pt j)
  · dsimp only
    intro i
    have la := RefreshNodeOwners.owner_spans (c:=csr) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad) (K:=K)
    have span : en.words 42+n=en.words 44 := la.1
    have within : i.val < n := i.isLt
    have endChild : en.words 42+n ≤ cur.val :=
      span.le.trans ((Nat.le_add_right (en.words 44) n).trans h44)
    have beforeControl := (Nat.add_lt_add_left within (en.words 42)).trans_le endChild
    rw [nstep _ (ne_of_lt beforeControl)]
    have child : memO (en.words 42+i.val) =
        ((csr.node+RefreshOwnership.child m (2^rem) i.val : ℕ) : Word W) := owner.1 i
    simpa only [Nat.cast_add] using child
  · dsimp only
    intro i
    have within : i.val < n := i.isLt
    have beforeControl := (Nat.add_lt_add_left within (en.words 44)).trans_le h44
    rw [nstep _ (ne_of_lt beforeControl)]
    exact owner.2.1 i
  · intro i _ hi
    exact (fromP i (hi.trans_le ca)).trans (descP i hi)
  · dsimp only
    intro i other hi
    exact ((nstep i other).trans (ofn.2.2 i hi)).trans ((rf.2.2 i hi).trans (pf.2.2 i hi))

  · rw [nstep _ (belowCtrl 48 (by decide))]
    exact (uo.header.values 48 (by decide)).trans (family_degree K csr (.refresh v m (2^rem) h pad))
  · dsimp only
    intro j hj
    rw [nstep _ (belowCtrl j hj)]
    exact uo.header.values j hj
  · exact uc.earlier
  · exact ⟨uc.graph,uc.widths⟩
  · dsimp only
    intro r r0
    have start : RefreshParty.Source mid r G (oldColumns csr v m) (en.words 12) (numberedRefreshWidths A) := by
      have field (j:ℕ) : (RefreshParty.stageField j).natural W (fun _=>0) (fun i=>(mid i).val) (fun i=>(r i).val)=
          info (fun i=>(mid i).val) cur j := by
        change (mid ((r 0).val+j)).val=(mid ((mid cur.val).val+j)).val
        rw [r0,uc.header.pointer]
      exact ⟨source.image,source.shifts,by rw [r0];have :=uc.header.fit;omega,
        (field 8).trans source.remaining,(field 9).trans source.width,(field 10).trans source.graph,
        (field 11).trans source.rows,(field 12).trans source.splitBase,source.graphBound,
        source.widthBound,source.shiftsBound⟩
    have earlier (i:ℕ) (hi:i<csr.heap) : out i=mid i :=
      (fromP i (hi.trans_le heap34)).trans (descP i (hi.trans_le (Nat.le_add_right _ _)))
    apply start.reopen rfl
    · intro j _ hj
      rw [r0]
      exact earlier _ (by have:=uc.earlier;omega)
    · exact fun i _ hi=>earlier i (hi.trans_le uc.graph)
    · exact fun i _ hi=>earlier i (hi.trans_le uc.widths)
    · intro i lo hi
      obtain ⟨_,_,endSplit,_,_⟩:=CursorSpace.ordered (c:=csr) (K:=K) («v»:=v) (a:=s) (t:=rem) (h:=h) (pad:=pad)
      have limit : en.words 12+3*(oldColumns csr v m).rows=fresh.graph:=endSplit
      exact (fromP i (hi.trans_le (limit.le.trans ((Nat.le_add_right ..).trans ga)))).trans
        (uc.post_retains_split E T.base _ _ (poolOf T rows) i lo hi)

/-- Inversion of a slot chart also commutes with the displacement on the return half. -/
theorem chart_half {B B' : Type} {q t : ℕ} {H : LiftedSlots B q (BitWord t)}
    {H' : LiftedSlots B' q (BitWord t)} {base : B ≃ B'} (chart : SlotImage.Chart H H' base)
    (z : B×BitWord t) (i : Fin (2*q)) :
    ShrinkStage.Halves.sourceHalf H' (base z.1,z.2) i =
      SlotImage.baseEdges base (ShrinkStage.Halves.sourceHalf H z i) := by
  let p := (z.1,ShrinkStage.Halves.halfSlot i)
  by_cases back : i.val<q
  · simp [ShrinkStage.Halves.sourceHalf,back,SlotImage.baseEdges,SlotImage.baseSlots]
  · have rev := chart.oriented p true
    have shift := chart.shift p true
    change H'.base.target.symm (SlotImage.baseSlots base p)=SlotImage.baseSlots base (H.base.target.symm p) at rev
    change H'.displacement (H'.base.target.symm (SlotImage.baseSlots base p))=
      H.displacement (H.base.target.symm p) at shift
    simp only [ShrinkStage.Halves.sourceHalf,ite_eq_right back]
    exact Prod.ext rev (congrArg (fun g=>z.2-g) shift)

/-- Numeric row order and the typed successor chart choose exactly the same oriented
half edge, including reversed incoming arcs and their actual lane transport. -/
theorem refresh_half_edge (branch : Fin (M).rules.count) (y : ((M).next branch).Site) (i : Fin (2*d)) :
    ShrinkStage.Halves.sourceHalf (CompressorRefresh.graph G E hm pad)
      (Records.siteOrder.symm (refreshFinalOrder T A hm hh sym rows zero conn branch y)) i=
    numFreshEdge A (ShrinkStage.Halves.sourceHalf ((M).next branch).graph (((M).next branch).chart.symm y) i) := by
  let X:=(M).next branch
  let f:=SlotImage.baseSlots («d»:=m) A.order
  let z:=X.chart.symm y
  have site : Records.siteOrder.symm (refreshFinalOrder T A hm hh sym rows zero conn branch y)=(f z.1,z.2) :=
    Records.siteOrder.symm_apply_apply _
  rw [site]
  exact chart_half ((SlotImage.ownChart (refreshBinaryGraph A) A.order).refresh E hm pad) z i

theorem refresh_half_src (branch : Fin (M).rules.count) (y : ((M).next branch).Site) (i : Fin (2*d)) :
    ShrinkStage.Halves.edgeNumber finProdFinEquiv (ShrinkStage.Halves.sourceHalf (CompressorRefresh.graph G E hm pad)
      (Records.siteOrder.symm (refreshFinalOrder T A hm hh sym rows zero conn branch y)) i)=
    ShrinkStage.Halves.edgeNumber ((M).next branch).order
      (ShrinkStage.Halves.sourceHalf ((M).next branch).graph (((M).next branch).chart.symm y) i) := by
  rw [refresh_half_edge T A hm hh sym rows zero conn branch y i]
  rfl

theorem refresh_half_width (branch : Fin (M).rules.count) (y : ((M).next branch).Site) (i : Fin (2*d)) :
    refreshNumericWidths T A hm hh sym rows zero conn branch
      (ShrinkStage.Halves.sourceHalf (CompressorRefresh.graph G E hm pad)
        (Records.siteOrder.symm (refreshFinalOrder T A hm hh sym rows zero conn branch y)) i)=
    ((M).next branch).width (ShrinkStage.Halves.sourceHalf ((M).next branch).graph (((M).next branch).chart.symm y) i) := by
  rw [refresh_half_edge T A hm hh sym rows zero conn branch y i]
  exact refreshBinary_width_numeric T A rows hm hh sym zero conn branch _

theorem refresh_half_prefix (branch : Fin (M).rules.count) (y : ((M).next branch).Site) (i : Fin (2*d)) :
    ShrinkStage.Halves.prefixValue (CompressorRefresh.graph G E hm pad)
      (refreshNumericWidths T A hm hh sym rows zero conn branch)
      (Records.siteOrder.symm (refreshFinalOrder T A hm hh sym rows zero conn branch y)) i=
    ShrinkStage.Halves.prefixValue ((M).next branch).graph ((M).next branch).width (((M).next branch).chart.symm y) i := by
  unfold ShrinkStage.Halves.prefixValue
  exact Finset.sum_congr rfl fun j _=>by rw [refresh_half_width T A hm hh sym rows zero conn branch y j]

/-- The stored widths in one refresh node are exactly its incoming and outgoing widths. -/
theorem refresh_half_sum (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) (prepared : Memory W)
    (y : ((M).next branch).Site) :
    ((refreshOutputData T A hm hh sym rows zero conn K csr branch prepared).halfWidth
      (refreshFinalOrder T A hm hh sym rows zero conn branch y)).sum=((M).next branch).incidentWidth y := by
  simp only [refreshOutputData,List.sum_ofFn]
  calc
    _ = ∑ j : Fin (2*d),((M).next branch).width
        (ShrinkStage.Halves.sourceHalf ((M).next branch).graph (((M).next branch).chart.symm y) j) :=
      Finset.sum_congr rfl fun j _=>refresh_half_width T A hm hh sym rows zero conn branch y j
    _ = _ := half_total ((M).next branch).graph ((M).next branch).width (((M).next branch).chart.symm y)

/-- Column zero of the earlier choice record supplies the motif's true number
of copies for the base and residual lane corresponding to this site. -/
theorem refresh_copies_sum (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) (prepared : Memory W)
    (copies : ∀ i : Fin (Q).motifs,(prepared (csr.heap+i.val*3)).val=(Q).copies i)
    (y : ((M).next branch).Site) :
    ((refreshOutputData T A hm hh sym rows zero conn K csr branch prepared).motifCopies
      (refreshFinalOrder T A hm hh sym rows zero conn branch y)).sum =
      refreshCopies T A (splitWord s rem) (tagOrdinal s).symm
        (show (A.Base×BitWord rem)×Fin m from y).1 := by
  let u := (show (A.Base×BitWord rem)×Fin m from y).1
  let p := (show (A.Base×BitWord rem)×Fin m from y).2
  let b : Records.Site v m rem := ((A.order u.1,p),u.2)
  have site : Records.siteOrder.symm (refreshFinalOrder T A hm hh sym rows zero conn branch y)=b :=
    Records.siteOrder.symm_apply_apply _
  have raw := copies (refreshBlockOrder A u)
  change (prepared (csr.heap+((refreshBlockOrder A) u).val*3)).val =
    refreshBinaryCopies T A ((refreshBlockOrder A).symm ((refreshBlockOrder A) u)) at raw
  rw [(refreshBlockOrder A).symm_apply_apply u,blockOrder_numeric A u] at raw
  change [(prepared ((allocate K csr (.refresh v m (2^rem) h pad)).words 2+
    blockId ((Records.siteOrder.symm _).1.1,(Records.siteOrder.symm _).2)*3)).val].sum=_
  rw [site]
  have bank : (allocate K csr (.refresh v m (2^rem) h pad)).words 2 = csr.heap := rfl
  have address : (b.1.1,b.2) = numBlock A u := rfl
  have count : refreshBinaryCopies T A u =
      refreshCopies T A (splitWord s rem) (tagOrdinal s).symm
        (show (A.Base×BitWord rem)×Fin m from y).1 := rfl
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,bank,address]
  exact raw.trans count

theorem refresh_archive_charge (K : ℕ) (csr : Cursor) (branch : Fin (M).rules.count) (prepared : Memory W)
    (copies : ∀ i : Fin (Q).motifs,(prepared (csr.heap+i.val*3)).val=(Q).copies i)
    (y : ((M).next branch).Site) :
    let data := refreshOutputData T A hm hh sym rows zero conn K csr branch prepared
    let i := refreshFinalOrder T A hm hh sym rows zero conn branch y
    1+(data.halfWidth i).sum+(data.motifCopies i).sum=refreshBinaryCharge T A hm hh sym rows zero conn branch y := by
  dsimp only
  simp only [refresh_half_sum T A hm hh sym rows zero conn,
    refresh_copies_sum T A hm hh sym rows zero conn _ _ _ _ copies,refreshBinaryCharge]



end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
