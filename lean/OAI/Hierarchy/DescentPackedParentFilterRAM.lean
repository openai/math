import OAI.Hierarchy.DescentPackedParentFilter
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Eleven numeric short fields to an actual filtered native receiver bank -/
namespace Hierarchy.DescentParallelBase.ParentFilter.Machine
open DescentSIMDLookup DescentSharedCableNames DescentHaloWalkRAM DescentPackedColony DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D H K L Q b w M G : ℕ}
local notation "P" => breadth D
local notation "bound" => P*P*Q
local notation "wd" => PackedBase.width bound K L

/-- The two wide physical addresses are absent. Each field is a local rank,
padded path, normalized short key, donor ticket, orientation bit or grain count. -/
def fields (R : Fin H→Fin D→Option (Fin H)) (v : Fin H×Fin Q) (p : Fin P) (old : Fin H) (r : Source P Q K L) : Fin 11→ℕ:=
  ![Rebase.value R .rank v.1 p,r.src.low.val,(localRank R old r.src.path).val,r.dst.low.val,(localRank R old r.dst.path).val,v.2.val,
    (peer R v.1 p r.src).val,(peer R v.1 p r.dst).val,r.upper.toNat,r.ticket.val,r.weight.val]

def scalar (D Q K L b : ℕ) (s : Cell (b*11)) : Cell (PackedBase.width (breadth D*breadth D*Q) K L):=
  let f:=(encode b 11).symm s
  if someTicket : (f 9).val<K then if someWeight : (f 10).val<L+1 then
    PackedBase.word (chip (f 0).val (f 1).val (f 2).val (f 3).val (f 4).val (f 5).val (f 6).val (f 7).val (decide ((f 8).val=1))
      ⟨(f 9).val,someTicket⟩ ⟨(f 10).val,someWeight⟩ (breadth D*breadth D*Q))
  else 0 else 0

def source (f : Fin 11→ℕ) (room : ∀j,f j<2^b) :=encode b 11 (fun i=>⟨f i,room i⟩)

theorem at_cell (R : Fin H→Fin D→Option (Fin H)) (v : Fin H×Fin Q) (p : Fin P) (old : Fin H) (r : Source P Q K L)
    (small : ∀j,fields R v p old r j<2^b) : scalar D Q K L b (source _ small)=PackedBase.word (filter R v p old r) :=by
  simp only [scalar,source,Equiv.symm_apply_apply,fields]
  change (if ht : r.ticket.val<K then if hw : r.weight.val<L+1 then PackedBase.word (chip _ _ _ _ _ _ _ _ (decide (r.upper.toNat=1)) ⟨r.ticket.val,ht⟩ ⟨r.weight.val,hw⟩ _) else 0 else 0)=_
  rw [dite_eq_left r.ticket.isLt,dite_eq_left r.weight.isLt]
  have side : decide (r.upper.toNat=1)=r.upper:=by cases r.upper <;> rfl
  rw [side]
  exact congrArg PackedBase.word (chip_filter R v p old r)

theorem absent (D Q K L b : ℕ) : scalar D Q K L b 0=0:=by
  have all0:(encode b 11).symm 0=(fun _=>0):=by
    apply (encode b 11).symm_apply_eq.mpr;apply Fin.ext;change 0=(finFunctionFinEquiv (fun _:Fin 11=>(0:Cell b))).val;simp []
  simp only [scalar,all0,Fin.val_zero]
  by_cases yes:0<K <;> simp [yes,chip,show PackedBase.word (none:Option (Entry (breadth D*breadth D*Q) K L))=0 by apply Fin.ext;rfl]

local notation "Gather" => DescentPacking.PackedMatch.Local.Gather.assembly

/-- All eleven sources can be derived independently from the same genuine
previous state. The real program assembles their packed lanes and changes
their format using a single common dictionary. -/
theorem run (tables : Fin 11→Tables) (field : Fin 11→Expr) (lut : Tables) (out : Bank) (m : Memory w)
    (bounds : DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w) tables field out.base)
    (fixed : ∀i,Static (tables i) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) i) M m)
    (words : Fin H→Fin G→Fin 11→Cell b) (actual : ∀i,DescentPackedZip.Source (field i) (fun v g=>words v g i) M m)
    (final : DescentPackedZip.Fits lut (Gather tables field) (.lit 0) (b*11) 0 M out.base w)
    (table : Static lut (fun s (_:Cell 0)=>scalar D Q K L b s) M m) (room : out.base+H*chunks G M<2^w) :
    let f:=lut.read (Gather tables field) (.lit 0)
    let result:=image out.base (H*chunks G M) f m
    (scan w out.base (H*chunks G M) f).Exec m result (4+H*chunks G M*(2*f.work+4)) ∧
    DescentPackedColony.Reads out (fun h g=>scalar D Q K L b (encode b 11 (words h g))) M result ∧ CheapCode (scan w out.base (H*chunks G M) f) :=by
  intro f result
  have assembled:=DescentPacking.PackedMatch.Local.Gather.collected tables field out.base bounds m fixed words actual (List.finRange 11)
  have a : DescentPackedZip.Source (Gather tables field) (fun h g=>encode b 11 (words h g)) M m:=by simpa [DescentPacking.PackedMatch.Local.Gather.assembly] using assembled
  have zero : DescentPackedZip.Source (.lit 0) (fun _:Fin H=>fun _:Fin G=>(0:Cell 0)) M m:=by
    intro p;change 0=(((finFunctionFinEquiv (fun i:Fin M=>if _:p.2.val*M+i.val<G then (0:Cell 0) else 0)).val:ℕ):Word w);simp []
  have done:=read_data lut (Gather tables field) (.lit 0) out.base final (fun s (_:Cell 0)=>scalar D Q K L b s) (absent ..) m table _ _ a zero
  have fits:f.Fits w out.base:=by simp [f,Tables.read,Expr.Fits,final.apply,final.shift,final.left]
  exact ⟨scan_exec _ _ _ _ fits room,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (DescentSIMDLookup.row H G M p)).trans (done p),@scan_cheap _ _ _ _⟩

end
end Hierarchy.DescentParallelBase.ParentFilter.Machine

end OAI
