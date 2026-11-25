import OAI.Hierarchy.DescentReachedCountPages
import OAI.Hierarchy.DescentOrdinaryRoleControlRead

namespace OAI
/-! Every scalar population comes from a dated atom field, including zero at each unused old host. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Layout
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedColony DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (L : RoleCounts.Layout) {w : ℕ}

private theorem book_access (P : Ports L.paths) (witness : Bank) (i : Fin L.blocks)
    (acc : Accessible P witness L.hosts L.groups L.lanes w L.base) (room : L.roof < 2^w) :
    Accessible P (L.book i) L.hosts L.groups L.lanes w L.outBase := by
  have before : L.base ≤ L.romBase := Nat.le_add_right ..
  have after_ : L.romBase ≤ L.outBase := Nat.le_add_right ..
  have late : L.outBase ≤ L.roof := Nat.le_add_right ..
  have end_ : (L.book i).base+(L.book i).size ≤ L.romBase := by
    change L.base+i.val*L.span+L.span ≤ L.base+L.blocks*L.span
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _
  have both:=RoleControl.Layout.accessible_after acc (before.trans after_)
  exact ⟨both.ids,both.idsRoom,both.roster,both.rosterRoom,both.offsets,both.offRoom,both.chunks,
    both.chunkRoom,⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt
      ((end_.trans (after_.trans late)).trans_lt room),end_.trans after_⟩,L.span_room⟩

private theorem field_room (P : Ports L.paths) (witness : Bank)
    (acc : Accessible P witness L.hosts L.groups L.lanes w L.base) (room : L.roof<2^w) :
    Gather.Bounds (w:=w) (d:=L.bits) (M:=L.lanes) L.table (direct P L.book L.hosts) L.outBase := by
  intro j
  let p : Fin L.paths × Fin L.blocks := finProdFinEquiv.symm j
  have a:=L.book_access P witness p.2 acc room
  have t (s : Fin 2) := ROM.bank_room L.pages L.romBits L.romBase L.outBase (finProdFinEquiv (j,s))
    (L.page_bound _) le_rfl ((Nat.le_add_right L.outBase L.span).trans_lt room)
  exact ⟨peer_fits P (L.book p.2) L.outBase a p.1,t 0,t 1,
    congrArg ROM.Page.bits (L.page_eq j 0),congrArg ROM.Page.bits (L.page_eq j 1)⟩

theorem any (P : Ports L.paths) (witness : Bank) (operand : ℕ→Expr) (m : Memory w)
    (early : ∀j<L.blocks,(operand j).Fits w L.base)
    (acc : Accessible P witness L.hosts L.groups L.lanes w L.base) (room : L.roof<2^w) :
    (L.program w P operand).Exec m (L.output P operand m) (L.ticks P operand) ∧
    CheapCode (L.program w P operand) ∧ ∀a,a<L.base ∨ L.roof≤a → L.output P operand m a=m a := by
  have lo : L.base≤L.romBase := Nat.le_add_right ..
  have hi : L.romBase≤L.outBase := Nat.le_add_right ..
  have top : L.outBase≤L.roof := Nat.le_add_right ..
  have snapshot:=DescentPackedFlowBatch.execute L.base L.rows L.span L.blocks operand m early
    ((hi.trans top).trans_lt room) L.span_room
  have rom:=ROM.run L.pages L.romBits L.romBase (L.snap operand m) (top.trans_lt room)
  have fit:=L.field_room P witness acc room
  have small:=Nat.add_le_add_left L.span_room L.outBase
  let copyCode := ProtocolRAM.program w (L.copies operand)
  let tableCode := ROM.mount L.pages L.romBits w L.romBase
  let outputCode := scan w L.outBase L.rows (L.gather P)
  have installed : (copyCode.seq tableCode).Exec m (L.installed operand m)
      (ProtocolRAM.clock (L.copies operand) + (4+10*L.tableWords)) :=
    @Procedure.Exec.then w copyCode tableCode m (L.snap operand m) (L.installed operand m)
      _ _ snapshot.1 rom.1
  have pass : outputCode.Exec (L.installed operand m) (L.output P operand m)
      (4+L.rows*(2*(L.gather P).work+4)) :=
    @scan_exec w L.outBase L.rows (L.gather P) (L.installed operand m)
      (Gather.fits L.table _ _ fit (List.finRange L.donors)) (small.trans_lt room)
  refine ⟨@Procedure.Exec.then w (copyCode.seq tableCode) outputCode m (L.installed operand m)
      (L.output P operand m) _ _ (@installed) (@pass),
    @cheap_seq w (copyCode.seq tableCode) outputCode
      (@cheap_seq w copyCode tableCode (@ProtocolRAM.program_cheap w (L.copies operand))
        (ROM.cheap L.pages L.romBits w L.romBase)) (@scan_cheap w L.outBase L.rows (L.gather P)),?_⟩
  rintro a (low|high)
  · exact (ProtocolRAMGeneratedWrite.frame_image L.outBase L.rows (L.gather P) (L.installed operand m) a
      (.inl (low.trans_le (lo.trans hi)))).trans
      ((ROM.frame L.pages L.romBits L.romBase (L.snap operand m) a (.inl (low.trans_le lo))).trans
        (snapshot.2.2 a low))
  · have old:=DescentPackedFlowBatch.above L.base L.rows L.span operand m 0 L.blocks a L.span_room
      (by
        rw [Nat.zero_add]
        change L.romBase ≤ a
        exact Nat.le_trans hi (Nat.le_trans top high))
    exact (ProtocolRAMGeneratedWrite.frame_image L.outBase L.rows (L.gather P) (L.installed operand m) a
      (.inr (small.trans high))).trans
      ((ROM.frame L.pages L.romBits L.romBase (L.snap operand m) a (.inr (top.trans high))).trans old)

theorem run (P : Ports L.paths) (witness : Bank) (operand : ℕ→Expr) (m : Memory w)
    (walks : Fin L.hosts→Fin L.paths→Option (Fin L.hosts))
    (prior : Fin L.blocks→Fin L.hosts→Fin L.groups→Cell L.bits)
    (early : ∀j<L.blocks,(operand j).Fits w L.base)
    (reads : ∀x : Fin L.blocks, Source (operand x.val) (prior x) L.lanes m)
    (acc : Accessible P witness L.hosts L.groups L.lanes w L.base)
    (mounted : Mounted P (DescentSortedRoster.indexed walks) m L.groups L.lanes)
    (room : L.roof < 2^w) :
    let dst:=L.output P operand m
    (L.program w P operand).Exec m dst (L.ticks P operand) ∧ CheapCode (L.program w P operand) ∧
    Source L.expr (fun h g=>encode L.bits L.donors (priorValue walks prior h g)) L.lanes dst ∧
    ∀ a, a<L.base ∨ L.roof≤a → dst a=m a := by
  intro dst
  have lo : L.base≤L.romBase := Nat.le_add_right ..
  have hi : L.romBase≤L.outBase := Nat.le_add_right ..
  have top : L.outBase≤L.roof := Nat.le_add_right ..
  have snapshot:=DescentPackedFlowBatch.execute L.base L.rows L.span L.blocks operand m early
    ((hi.trans top).trans_lt room) L.span_room
  have fit:=L.field_room P witness acc room
  have below (a : ℕ) (ha : a<L.base) : L.installed operand m a=m a :=
    (ROM.frame L.pages L.romBits L.romBase _ a (.inl (ha.trans_le lo))).trans (snapshot.2.2 a ha)
  have stored (x : Fin L.blocks) : Reads (L.book x) (prior x) L.lanes (L.installed operand m) := by
    intro p
    have idx:=(row L.hosts L.groups L.lanes p).isLt.trans_le L.span_room
    have up:=Nat.mul_le_mul_right L.span x.isLt
    rw [Nat.succ_mul] at up
    have before : (L.book x).base+(row L.hosts L.groups L.lanes p).val<L.romBase := by
      change L.base+x.val*L.span+_ < L.base+L.blocks*L.span
      omega
    exact (ROM.frame L.pages L.romBits L.romBase _ _ (.inl before)).trans
      ((snapshot.2.1 x (row _ _ _ p)).trans (reads x p))
  have ordered:=RoleControl.Layout.previous_mounted acc _ below mounted
  have counts:=fromCounts P L.book L.table L.outBase (L.installed operand m) walks prior ordered stored
    (fun x=>L.book_access P witness x acc room) fit (fun j=>ROM.binary_mounted
      (Gather.setField (d:=L.bits) j) L.lanes L.pages L.romBits L.romBase (L.snap operand m) L.page_bound
      (fun s=>finProdFinEquiv (j,s)) (L.page_eq j))
  have outputWords : Reads L.result (fun h g=>encode L.bits L.donors (priorValue walks prior h g)) L.lanes dst :=
    fun p=>(ProtocolRAMGeneratedWrite.read_image L.outBase L.rows _ _ (row _ _ _ p)).trans (counts p)
  have hw:=L.any P witness operand m early acc room
  exact ⟨hw.1,hw.2.1,source_column L.result L.roof (L.result_fits room le_rfl) dst _ L.span_room outputWords,hw.2.2⟩

theorem ticks_bound (P : Ports L.paths) (operand : ℕ→Expr) (unit : ℕ)
    (cost : ∀j<L.blocks,(operand j).work≤unit) : L.ticks P operand ≤
      (4+L.blocks*(4+L.rows*(2*unit+4)))+(4+10*L.tableWords)+
        (4+L.rows*(2*(1+56*L.donors)+4)) := by
  have snap:=DescentPackedFlowBatch.tariff L.base L.rows L.span L.blocks operand unit cost
  have gather:=L.gather_work P
  have factor:=Nat.mul_le_mul_left L.rows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 gather) 4)
  unfold ticks copies
  simpa only [Nat.mul_comm 56] using
    Nat.add_le_add (Nat.add_le_add_right snap _) (Nat.add_le_add_left factor 4)

theorem text_bound (P : Ports L.paths) (operand : ℕ→Expr) (unit : ℕ)
    (cost : ∀j<L.blocks,(operand j).work≤unit) :
    DescentStaticWordColumn.names (L.program w P operand) ≤
      15+L.blocks*(11+4*unit)+15*(L.tableWords+1)+(11+4*(1+56*L.donors)) := by
  have snap:=DescentOperandVectorArena.names_passes L.base L.rows L.span w unit operand 0 L.blocks
    (fun j _ hj=>cost j (by simpa only [Nat.zero_add] using hj))
  have gathered : (L.gather P).work ≤ 1+56*L.donors := by
    rw [Nat.mul_comm 56 L.donors]
    simpa only [show (45+11 : ℕ)=56 by decide] using L.gather_work P
  rw [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,
    DescentStaticWordColumn.names_scan,ROM.mount,DescentStaticWordColumn.names_mount]
  change _+15*(L.tableWords+1)+(11+4*(L.gather P).work) ≤ _
  unfold copies
  exact Nat.add_le_add (Nat.add_le_add_right snap (15*(L.tableWords+1)))
    (Nat.add_le_add_left (Nat.mul_le_mul_left 4 gathered) 11)

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Layout

end OAI
