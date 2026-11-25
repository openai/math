import OAI.Hierarchy.DescentOrdinarySignedParents

namespace OAI
/-! One literal table shared by all queries turns the original eleven local
donor fields into the five input digits of the three weighted rank scans. -/
namespace Hierarchy.DescentOrdinarySignedParents.ROM
open DescentHaloWalkRAM DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {base D Q K L b M H G w oldH : ℕ}
def tables (D Q K L b M:ℕ):Fin 2→Page:=binary (fun x (_:Cell 0)=>code D Q K L b x) M
def width (b M:ℕ):=b*11*M
def endAddress (base D Q K L b M:ℕ):=base+Fused.TablesROM.length D Q K L b M+2*2^width b M
def joins:=Fused.TablesROM.joins
def formatter (base D Q K L b M:ℕ):=
  joined (tables D Q K L b M) (width b M) (base+Fused.TablesROM.length D Q K L b M) id
def program (base D Q K L b M w:ℕ):=
  (Fused.TablesROM.program D Q K L b M base w).seq
    (mount (tables D Q K L b M) (width b M) w (base+Fused.TablesROM.length D Q K L b M))
def memory (base D Q K L b M:ℕ) (m:Memory w):=
  after (tables D Q K L b M) (width b M) (base+Fused.TablesROM.length D Q K L b M)
    (Fused.TablesROM.installed D Q K L b M base m)
def time (D Q K L b M:ℕ):=8+10*(Fused.TablesROM.length D Q K L b M+2*2^width b M)
local notation "joins₀" base => joins D Q K L b M base
local notation "lut" base => formatter base D Q K L b M
variable (base D Q K L b M) in
def expression (f:Fin 11→Expr):=
  (lut base).read (DescentPacking.PackedMatch.Local.Gather.assembly (joins₀ base) f) (.lit 0)

variable (base D Q K L b M) in
theorem setup (m:Memory w)
    (space:endAddress base D Q K L b M<2^w):
    let done:=memory base D Q K L b M m
    (program base D Q K L b M w).Exec m done (time D Q K L b M) ∧
    (∀j,Static ((joins₀ base) j) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j) M done) ∧
    Static (lut base) (fun x (_:Cell 0)=>code D Q K L b x) M done ∧
    (∀i,i<base ∨ endAddress base D Q K L b M≤ i→done i=m i) ∧ CheapCode (program base D Q K L b M w):=by
  intro done
  let fee:=Fused.TablesROM.length D Q K L b M
  have top:base+fee≤endAddress base D Q K L b M:=Nat.le_add_right ..
  have first:=Fused.TablesROM.setup D Q K L b M base w m (top.trans_lt space)
  let prior:=Fused.TablesROM.installed D Q K L b M base m
  have second:=DescentOrdinaryAtomFieldRAM.ROM.run (tables D Q K L b M) (width b M) (base+fee) prior space
  have fits (s:Fin 2):(tables D Q K L b M s).bits≤width b M:=by fin_cases s <;> simp [tables,binary,width]
  have frozen:=frame (tables D Q K L b M) (width b M) (base+fee) prior
  have stored:=binary_mounted (fun x (_:Cell 0)=>code D Q K L b x) M (tables D Q K L b M) (width b M) (base+fee) prior fits id (fun _=>rfl)
  have ticks:time D Q K L b M=(4+10*fee)+(4+10*(2*2^(width b M))):=by dsimp [time,fee];omega
  refine ⟨ticks ▸ Procedure.Exec.then first.1 second.1,?_,stored,?_,cheap_seq first.2.2.2.2.2.2 (cheap _ _ _ _)⟩
  · intro j
    have layout:=Fused.TablesROM.layout (base:=base) (w:=w) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j)
      (j.castAdd 2) (Fused.TablesROM.insert_page j) (le_refl _) (top.trans_lt space) (.lit 0) (.lit 0) trivial trivial
    constructor
    · intro s
      have bound:s.val<((joins₀ base) j).shift.size:=by
        have bits : ((joins₀ base) j).shift.bits = (b*11)*M := layout.shiftBits
        rw [Bank.size, bits]
        exact s.isLt
      exact (frozen _ (.inl ((Nat.add_lt_add_left bound _).trans_le layout.shift.2.2))).trans ((first.2.1 j).1 s)
    · intro s
      have bound:s.val<((joins₀ base) j).apply.size:=by
        have bits : ((joins₀ base) j).apply.bits = (b*11+b)*M := layout.applyBits
        rw [Bank.size, bits]
        exact s.isLt
      exact (frozen _ (.inl ((Nat.add_lt_add_left bound _).trans_le layout.apply.2.2))).trans ((first.2.1 j).2 s)
  · intro i out;rcases out with low|high
    · exact (frozen _ (.inl (low.trans_le (Nat.le_add_right ..)))).trans (first.2.2.2.2.1 _ (.inl low))
    · exact (frozen _ (.inr high)).trans (first.2.2.2.2.1 _ (.inr (top.trans high)))

theorem fits (base:ℕ) (field:Fin 11→Expr) (early:∀j,(field j).Fits w base)
    (room:endAddress base D Q K L b M<2^w):
    (expression base D Q K L b M field).Fits w (endAddress base D Q K L b M):=by
  let upper:=endAddress base D Q K L b M
  have grow:base≤upper:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have separate:base+Fused.TablesROM.length D Q K L b M≤upper:=Nat.le_add_right ..
  have bounds:DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w) (joins₀ base) field upper:=by
    intro j
    have at_:=Fused.TablesROM.layout (base:=base) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j)
      (j.castAdd 2) (Fused.TablesROM.insert_page j) separate room (.lit 0) (field j) trivial (ProtocolRAMGeneratedWrite.fits_mono _ grow (early j))
    exact ⟨at_.right,at_.shift,at_.apply,at_.shiftBits,at_.applyBits⟩
  have sized (s:Fin 2):(tables D Q K L b M s).bits≤width b M:=by fin_cases s <;> simp [tables,binary,width]
  have l: (lut base).shift.Fits w upper:=bank_room _ _ _ _ _ (sized 0) le_rfl room
  have r: (lut base).apply.Fits w upper:=bank_room _ _ _ _ _ (sized 1) le_rfl room
  exact ⟨r,trivial,l,DescentPacking.PackedMatch.Local.Gather.fits _ _ _ bounds _⟩

theorem work (base:ℕ) (field:Fin 11→Expr) (limit:ℕ) (size:∀j,(field j).work≤limit):
    (expression base D Q K L b M field).work≤13+11*(limit+11):=
  Fused.expression_work (joins₀ base) field (lut base) limit size

theorem source (base:ℕ) (f:Fin 11→Expr) (old:Memory w) (R:Fin oldH→Fin D→Option (Fin oldH))
    (r:Fin H→Fin G→Option (Fused.Raw R Q K L b))
    (early:∀i,(f i).Fits w base) (rd:∀i,DescentPackedZip.Source (f i) (fun h g=>Fused.columns (r h g) i) M old)
    (room:endAddress base D Q K L b M<2^w):
    let done:=memory base D Q K L b M old
    let upper:=endAddress base D Q K L b M
    (expression base D Q K L b M f).Fits w upper ∧
    DescentPackedZip.Source (expression base D Q K L b M f)
      (fun h g=>encode b 5 (DescentResetSignedScan.literal b (actual (r h g)))) M done :=by
  intro done upper
  have init:=setup base D Q K L b M old room
  have grow:base≤upper:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have separate:base+Fused.TablesROM.length D Q K L b M≤upper:=Nat.le_add_right ..
  have layout:DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w) (joins₀ base) f upper:=by
    intro j
    have at_:=Fused.TablesROM.layout (base:=base) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j)
      (j.castAdd 2) (Fused.TablesROM.insert_page j) separate room (.lit 0) (f j) trivial (ProtocolRAMGeneratedWrite.fits_mono _ grow (early j))
    exact ⟨at_.right,at_.shift,at_.apply,at_.shiftBits,at_.applyBits⟩
  have earlier (j):DescentPackedZip.Source (f j) (fun h g=>Fused.columns (r h g) j) M done:=
    fun p=>(ProtocolRAM.eval_below (f j) _ old done (early j) (fun addr small=>init.2.2.2.1 addr (.inl small))).trans (rd j p)
  let left:=DescentPacking.PackedMatch.Local.Gather.assembly (joins₀ base) f
  have full:DescentPackedZip.Source left (fun h g=>encode b 11 (Fused.columns (r h g))) M done:=by
    simpa only [left,DescentPacking.PackedMatch.Local.Gather.assembly,List.mem_finRange,ite_true] using
      DescentPacking.PackedMatch.Local.Gather.collected (joins₀ base) f upper layout done init.2.1
        (fun h g=>Fused.columns (r h g)) earlier (List.finRange 11)
  have sized (s:Fin 2):(tables D Q K L b M s).bits≤width b M:=by fin_cases s <;> simp [tables,binary,width]
  have lf:DescentPackedZip.Fits (lut base) left (.lit 0) (b*11) 0 M upper w :=
    ⟨DescentPacking.PackedMatch.Local.Gather.fits _ _ _ layout _,trivial,
     bank_room _ _ _ _ _ (sized 0) le_rfl room,bank_room _ _ _ _ _ (sized 1) le_rfl room,rfl,rfl⟩
  have zero:DescentPackedZip.Source (.lit 0) (fun _:Fin H=>fun _:Fin G=>(0:Cell 0)) M done:=by
    intro p;change 0=(((finFunctionFinEquiv (fun i:Fin M=>if _:p.2.val*M+i.val<G then (0:Cell 0) else 0)).val:ℕ):Word w);simp []
  refine ⟨by simp [expression,Tables.read,Expr.Fits,lf.apply,lf.shift,lf.left,left],?_⟩
  simpa only [expression,left,decoded] using read_data (lut base) left (.lit 0) upper lf (fun x (_:Cell 0)=>code D Q K L b x)
    (code_zero ..) done init.2.2.1 _ _ full zero

end
end Hierarchy.DescentOrdinarySignedParents.ROM

end OAI
