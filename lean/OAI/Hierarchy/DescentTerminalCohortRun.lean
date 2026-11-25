import OAI.Hierarchy.DescentTerminalCohortArena

namespace OAI
/-! # The emitted roster, stable relative ranks and counts share one native sorting pass -/
namespace Hierarchy.DescentTerminalCohortArena
open DescentCensusRAM DescentTerminalFrozenRoster DescentTerminalPacketSlotRAM DescentTerminalExteriorPackets
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure Computability.BorderVNP.FragmentBucket
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ} (base f k n H : ℕ) (room : stop base f k n H<2^w) (source : Bank)
local notation "ord" => order base f k n H
local notation "bins_" => shelf base f k n H room
local notation "L" => roster base f k n H
local notation "sortCost" => (4+n*(2*(guard source H).work+4))+ProtocolRAMEndpointSort.cost n H+(4+n*80)
local notation "sort_" => DescentTerminalPacketSlotRAM.program source ord w n H
local notation "publish_" => DescentTerminalFrozenRoster.program bins_ L

def machine : Procedure w :=
  ((ROM.setup base f k w).seq (DescentTerminalPacketSlotRAM.program source (order base f k n H) w n H)).seq
    (DescentTerminalFrozenRoster.program (shelf base f k n H room) (roster base f k n H))
def ticks := ((4+10*ROM.size f k)+sortCost)+tallyCost bins_ (tag L (bins_).bins H) (value L)

theorem ticks_le : ticks base f k n H room source ≤ 10*ROM.size f k+704*(n+H+1) := by
  have sorting:=DescentTerminalPacketSlotRAM.fee (n:=n) (H:=H) source
  have census:=DescentTerminalFrozenRoster.clocks bins_ L
  unfold ticks
  omega

theorem names_le : DescentStaticWordColumn.names (machine base f k n H room source) ≤ 15*(ROM.size f k+1)+4096 := by
  have endpoint (s : ProtocolRAMEndpointSort.Layout) :
      DescentStaticWordColumn.names (ProtocolRAMEndpointSort.program s w n H) = 101 := by
    simp only [ProtocolRAMEndpointSort.program,ProtocolRAMSiteCounts.program,
      ProtocolRAMEndpointPrefix.exclusive,DescentStaticWordColumn.names_seq]
    rfl
  have sorting (s : ProtocolRAMEndpointSort.Layout) :
      DescentStaticWordColumn.names (DescentTerminalPacketSlotRAM.program source s w n H) = 343 := by
    have guardWork : (DescentTerminalExteriorPackets.guard source H).work = 17 := rfl
    simp only [DescentTerminalPacketSlotRAM.program,sortedProgram,DescentStaticWordColumn.names_seq,
      DescentStaticWordColumn.names_scan,endpoint,guardWork,DescentTerminalPacketSlotRAM.expr,Expr.work]
  have indexed (addresses words rows : ℕ) :
      DescentStaticWordColumn.names (ProtocolRAMIndexedWrite.scatter w addresses words rows) = 20 := rfl
  have weighted (src rows : ℕ) :
      DescentStaticWordColumn.names (ProtocolRAMWeightedScatter.program w src rows) = 22 := rfl
  have publishing (s : Banks w n (H+1)) (r : Shelf) :
      DescentStaticWordColumn.names (DescentTerminalFrozenRoster.program s r) = 413 := by
    have valueWork : (DescentTerminalFrozenRoster.value r).work = 30 := rfl
    simp only [DescentTerminalFrozenRoster.program,tally,add,issue,ProtocolRAMGeneratedWrite.program,
      DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,indexed,weighted,
      DescentCensusRAM.slot,tag,DescentTerminalFrozenRoster.owner,valueWork,Expr.work]
  rw [machine,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,
    ROM.setup,DescentStaticWordColumn.names_mount,sorting,publishing]
  omega

theorem any (m : Memory w) (alive : 0<H) (src : source.Fits w base) :
    ∃o : Memory w,(machine base f k n H room source).Exec m o (ticks base f k n H room source) ∧
      CheapCode (machine base f k n H room source) := by
  obtain ⟨sr,range,rom,_,safe,paid⟩:=layout base f k n H room source src
  have mounted:=ROM.run base f k m rom
  let installed:=ROM.mounted base f k m
  let ranked:=after ord n H (sorted source ord H n alive installed)
  have sorter:=DescentTerminalPacketSlotRAM.run source ord installed alive sr range
  obtain ⟨o,wrote,cheap⟩:=DescentTerminalFrozenRoster.any bins_ L ranked safe paid
  refine ⟨o,Procedure.Exec.then (Procedure.Exec.then mounted.1 sorter.1) wrote,?_⟩
  exact @cheap_seq w ((ROM.setup base f k w).seq sort_) publish_
    (@cheap_seq w (ROM.setup base f k w) sort_ mounted.2.1 sorter.2) @cheap

theorem produced (m : Memory w) (alive : 0<H) (src : source.Fits w base)
    (home : Fin n→Fin H) (keys : ∀u,source.read m (u.val:Word w)=((home u).val:Word w))
    (cap : ∀s,count home s ≤ 2^k) :
    let frozen:=fun u : Fin n=>(u.val : Fin (2^f))
    ∃o : Memory w,(machine base f k n H room source).Exec m o (ticks base f k n H room source) ∧
      CheapCode (machine base f k n H room source) ∧
      (∀s : Fin H,o ((bins_).bins+s.val)=((book home frozen s).val:Word w) ∧ o ((ord).counts+s.val)=(count home s:Word w)) ∧
      (∀i:Fin n,let u:=(dest home).symm i
        o (indexBase base f k n H+i.val)=(prior home u.val (home u):Word w)) ∧ ∀a< base,o a=m a := by
  intro frozen
  obtain ⟨sr,range,rom,countLow,safe,paid⟩:=layout base f k n H room source src
  let stage₁:=ROM.mounted base f k m
  let stage₂:=sorted source ord H n alive stage₁
  let stage₃:=after ord n H stage₂
  have mounted:=ROM.run base f k m rom
  have sorter:=DescentTerminalPacketSlotRAM.run source ord stage₁ alive sr range
  have sourceKeys (u : Fin n) : source.read stage₁ (u.val:Word w)=((home u).val:Word w) := by
    have lo:=Nat.add_lt_add_left (Nat.mod_lt (u.val:Word w).val src.1) source.base
    exact (mounted.2.2.2 _ (.inl (lo.trans_le src.2.2))).trans (keys u)
  have retained_ {a : ℕ} (ha : a < base+ROM.size f k) : stage₃ a=stage₁ a := by
    have first : a < (ord).src:=ha
    have old:=sr.fits.src_safe;have mid:=sr.fits.count_safe;have hi:=sr.fits.prefix_safe
    apply (retained ord n H stage₂ a (.inl (by unfold out;omega))).trans
    exact sort_before source ord H n stage₁ alive sr first
  have bank_ (bank : Bank) (lo : bank.base+bank.size≤ base+ROM.size f k) (i : Word w) :
      bank.read stage₃ i=bank.read stage₁ i :=
    retained_ (a:=bank.base+i.val%bank.size)
      ((Nat.add_lt_add_left (Nat.mod_lt i.val (Nat.two_pow_pos bank.bits)) bank.base).trans_le lo)
  have lowF : (ROM.frozen base f).base+(ROM.frozen base f).size ≤ base+ROM.size f k := by
    change base+2^f ≤ base+(2^f+2^k+2^k*2^f)
    exact Nat.add_le_add_left ((Nat.le_add_right (2^f) (2^k)).trans
      (Nat.le_add_right _ (2^k*2^f))) base
  have lowOff : (ROM.offsets base f k).base+(ROM.offsets base f k).size ≤ base+ROM.size f k := by
    change base+2^f+2^k≤ base+(2^f+2^k+2^k*2^f);omega
  have lowProd : (ROM.product base f k).base+(ROM.product base f k).size ≤ base+ROM.size f k := by
    change base+2^f+2^k+2^(f+k)≤ base+(2^f+2^k+2^k*2^f)
    rw [pow_add,Nat.mul_comm (2^f) (2^k)];omega
  have lit:=ROM.reads base f k m rom (L).sorted (L).homes (L).rank
  have lives : Literals f (2^k) L stage₃ :=
    ⟨fun j hj=>(bank_ _ lowOff _).trans (lit.1.offset j hj),
      fun j hj u=>(bank_ _ lowProd _).trans (lit.1.product j hj u)⟩
  have digits (i : Fin n) : (ROM.frozen base f).read stage₃ (i.val:Word w)=((frozen i).val:Word w) := by
    exact (bank_ _ lowF _).trans
      (lit.2 i.val (i.isLt.trans_le ((Nat.le_add_left n (out ord n H)).trans range.le)))
  obtain ⟨o,q,books,low⟩:=published_counts source ord stage₁ alive sr range home frozen sourceKeys bins_ (2^k) cap
    (ROM.frozen base f) (ROM.offsets base f k) (ROM.product base f k) digits
    ((Nat.add_le_add_left (Nat.le_pow_clog (by decide : 1<2) H) _).trans countLow) lives safe paid
  obtain ⟨_,_,admissible⟩:=any base f k n H room source m alive src
  refine ⟨o,Procedure.Exec.then (Procedure.Exec.then mounted.1 sorter.1) q,@admissible,books,?_,?_⟩
  · intro i
    have hi := i.isLt.trans_le (Nat.le_pow_clog (by decide : 1<2) n)
    have below : indexBase base f k n H+i.val<(bins_).first:=Nat.add_lt_add_left hi _
    exact (low _ below).trans (truthful_slot source ord stage₁ alive sr home sourceKeys i).1
  · intro a ha
    have h : base ≤ (ord).counts :=
      (Nat.le_add_right base (ROM.size f k)).trans (Nat.le_add_right _ (2^Nat.clog 2 n))
    exact (low a (ha.trans_le (h.trans ((Nat.le_add_right ..).trans countLow)))).trans
      ((retained_ (ha.trans_le (Nat.le_add_right ..))).trans (mounted.2.2.2 a (.inl ha)))


end
end Hierarchy.DescentTerminalCohortArena

end OAI
