import OAI.Hierarchy.DescentOrdinaryRoleControl

namespace OAI
/-! # Issue the real per-donor populations and desired host label at each packed receiver -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (L : RoleControl.Layout) {D w : ℕ}

private theorem earlier_bank {A : Bank} {a b} (h : A.Fits w a) (le : a≤b) : A.Fits w b :=
  ⟨h.1,h.2.1,h.2.2.trans le⟩

theorem accessible_after {P : Ports D} {b : Bank} {H G M e e'} (acc : Accessible P b H G M w e) (le : e≤e') :
    Accessible P b H G M w e' :=
  ⟨fun i=>earlier_bank (acc.ids i) le,acc.idsRoom,earlier_bank acc.roster le,acc.rosterRoom,
    earlier_bank acc.offsets le,acc.offRoom,earlier_bank acc.chunks le,acc.chunkRoom,earlier_bank acc.source le,acc.srcRoom⟩

private theorem below {A : Bank} {i s} (fit : A.Fits w s) (small : i<A.size) : A.base+i<s :=
  (Nat.add_lt_add_left small _).trans_le fit.2.2

theorem previous_mounted {P : Ports D} {s : Bank} {G H M h} (acc : Accessible P s H G M w h)
    (order : Fin H→Fin D→Option (Fin H)) {m z : Memory w} (same : ∀j,j<h→z j=m j)
    (seen : Mounted P order m G M) : Mounted P order z G M := by
  refine ⟨?_,?_,?_,?_⟩
  · intro p i
    exact (same _ (below (acc.ids i) ((row H G M p).isLt.trans_le (acc.idsRoom i)))).trans (seen.ids p i)
  · intro v i
    have small : v.val*D+i.val<H*D:=calc
      _ < (v.val+1)*D := by rw [Nat.add_mul,one_mul]; exact Nat.add_lt_add_left i.isLt _
      _ ≤ _ := Nat.mul_le_mul_right _ v.isLt
    exact (same _ (below acc.roster (small.trans_le acc.rosterRoom))).trans (seen.roster v i)
  · intro v
    exact (same _ (below acc.offsets (v.isLt.trans_le acc.offRoom))).trans (seen.offsets v)
  · intro p
    exact (same _ (below acc.chunks ((row H G M p).isLt.trans_le acc.chunkRoom))).trans (seen.chunks p)

theorem previous_reads {P : Ports D} {s : Bank} {G H M h b} (acc : Accessible P s H G M w h)
    (v : Fin H→Fin G→Cell b) {m z : Memory w} (same : ∀j,j<h→z j=m j)
    (seen : Reads s v M m) : Reads s v M z := fun p=>
  (same _ (below acc.source ((row H G M p).isLt.trans_le acc.srcRoom))).trans (seen p)

private theorem page_read {N : ℕ} (pg : Fin N→ROM.Page) (width base : ℕ) (m : Memory w)
    (j : Fin N) (bound : (pg j).bits≤width) (actual : ROM.Page) (same : pg j=actual)
    (x : Cell actual.bits) :
    ROM.after pg width base m ((ROM.bank pg width base j).base+x.val)=(actual.number x:Word w) := by
  subst actual
  exact ROM.read pg width base m j bound x

private theorem dictionary_read (m : Memory w) (x : Cell ((L.roleBits*L.nodes)*L.lanes)) :
    L.staticMem m (L.dictionary.base+x.val)=
      ((DescentSIMDLookup.table (M:=L.lanes) (RoleCounts.count (a:=L.roleBits) (K:=L.nodes) L.countBits) x).val:Word w) :=
  page_read L.pages L.width L.base m L.dictIndex (L.page_bound _) _ L.dict_page x

def dataCount (order : Fin L.hosts→Fin L.walks→Option (Fin L.hosts))
    (old : Fin L.blocks→Fin L.hosts→Fin L.groups→Cell (L.roleBits*L.nodes)) (h : Fin L.hosts) (g : Fin L.groups) :=
  encode L.countBits L.donors (RoleCounts.value order old L.countBits h g)

theorem issued (P : Ports L.walks) (old : Fin L.blocks→Bank) (someBlock : Fin L.blocks) (m : Memory w)
    (order : Fin L.hosts→Fin L.walks→Option (Fin L.hosts))
    (roles : Fin L.blocks→Fin L.hosts→Fin L.groups→Cell (L.roleBits*L.nodes))
    (access : ∀b,Accessible P (old b) L.hosts L.groups L.lanes w L.base)
    (ports : Mounted P (DescentSortedRoster.indexed order) m L.groups L.lanes)
    (held : ∀b,Reads (old b) (roles b) L.lanes m) (limit : L.endAddress<2^w) :
    let dst:=L.output P old m
    Reads L.result (L.dataCount order roles) L.lanes dst ∧
    Source L.counts (L.dataCount order roles) L.lanes dst ∧
    ∀l,Source (L.want P l) (fun (_:Fin L.hosts) (_:Fin L.groups)=>DescentSharedCableNames.Packed.token (some l)) L.lanes dst := by
  intro dst
  have early : L.base≤L.outBase:=Nat.le_add_right ..
  have keep : ∀j,j<L.base→L.staticMem m j=m j:=fun j h=>ROM.frame _ _ _ _ _ (.inl h)
  have acc (b : Fin L.blocks) : Accessible P (old b) L.hosts L.groups L.lanes w L.outBase :=
    accessible_after (access b) early
  have read:=RoleCounts.counts P old L.dictionary L.tables L.outBase (L.staticMem m) order roles
    (previous_mounted (access someBlock) _ keep ports)
    (fun b=>previous_reads (access b) _ keep (held b)) acc (L.bank_fits limit L.dictIndex)
    (congrArg ROM.Page.bits L.dict_page) (L.dictionary_read m)
    (L.field_room P old acc limit) (fun j=>ROM.binary_mounted (Gather.setField (d:=L.countBits) j) L.lanes
      L.pages L.width L.base m L.page_bound (L.pair j) (L.pair_page j))
  have got : Reads L.result (L.dataCount order roles) L.lanes dst:=fun p=>
    (ProtocolRAMGeneratedWrite.read_image L.outBase L.rows (L.gather P old) (L.staticMem m) (row _ _ _ p)).trans (read p)
  refine ⟨got,source_column L.result L.endAddress (L.result_fit limit le_rfl) dst _ L.result_size got,?_⟩
  intro l p
  let q:=p.2
  have alive : q.val<2^L.chunkBits :=q.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
  have size : (L.ask l).bits=L.chunkBits:=congrArg ROM.Page.bits (L.ask_page l)
  have keepDst:= (L.any P old m acc limit).2.2.2
  have retained (a : ℕ) (h : a<L.base) : dst a=m a := keepDst a (.inl h)
  have ch := (previous_mounted (access someBlock) _ retained ports).chunks p
  change (L.ask l).read dst (P.chunks.read dst ((row L.hosts L.groups L.lanes p).val : Word w)) = _
  rw [bank_read P.chunks dst ((row _ _ _ p).isLt.trans_le (access someBlock).chunkRoom) (access someBlock).chunks,ch]
  have small : q.val<(L.ask l).size:=by change _<2^_;rw [size];exact alive
  rw [bank_read _ dst small (L.bank_fits limit (L.askIndex l))]
  have shelf : (L.ask l).base+q.val<L.outBase:=below (L.bank_fits limit (L.askIndex l)) small
  rw [show dst ((L.ask l).base+q.val)=L.staticMem m _ from
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl shelf)]
  have printed:=page_read L.pages L.width L.base m (L.askIndex l) (L.page_bound _) _
    (L.ask_page l) (⟨q.val,alive⟩ : Cell L.chunkBits)
  refine printed.trans ?_
  change ((L.askWord l q.val).val:Word w)=_
  have eqn : L.askWord l q.val=data
      (fun (_:Fin L.hosts) (_:Fin L.groups)=>DescentSharedCableNames.Packed.token (some l)) p := by
    unfold askWord data
    congr 1
  exact congrArg (fun v : Cell (L.nameBits*L.lanes)=>(v.val:Word w)) eqn


end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout

end OAI
