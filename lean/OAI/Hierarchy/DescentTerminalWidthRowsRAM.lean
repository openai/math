import OAI.Hierarchy.DescentTerminalWidthRowsAny
import OAI.Hierarchy.DescentTerminalWidthRowsScatter
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Emit the actual concatenation of all reached width rows in a fixed purchased bank -/
namespace Hierarchy.DescentTerminalWidthRowsRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalHeaderGroups DescentTerminalDenseHeader
open ThreeFlat.RAM PhysicalProcedure ThreeFlat.Routing
open DescentTerminalPrimitiveArena (covered)
open scoped Fin.CommRing
noncomputable section

variable {w : ℕ} (L : Layout) (q p : ℕ) (c : Fin L.groups → ℕ)
local notation "K" => L.ceil.size
local notation "flat" => tape q p c
local notation "st" => fun k : ℕ => (List.length (passed q p c k) : Word w)
local notation "filling" => L.fill q p
local notation "addr" => target q p c L.output.base L.sink
local notation "datum" => patch (w:=w) q p c

def mounted (m : Memory w) := DescentStaticWordColumn.image L.origin (L.literal q p) m L.entries
def prefixed (m : Memory w) := fillSegment L.prefix.base L.groups
  (DescentTerminalHeaderPrefixRAM.file L.prefix.base st) (mounted L q p m)
def cleared (m : Memory w) := ProtocolRAM.image L.output.base L.rows filling (prefixed L q p c m)
def final (m : Memory w) := ProtocolRAMGeneratedWrite.image L.addresses L.words L.dest L.datum addr datum (cleared L q p c m)

variable (m : Memory w) (cap : ∀i,c i≤L.cap) (roomRows : (tape q p c).length≤L.rows)
    (source : L.source.Fits w L.origin) (sourceRows : L.groups ≤ L.source.size) (space : L.stop < 2^w)
    (given : ∀i : Fin L.groups, m (L.source.base+i.val)=(c i:Word w))
local notation "warm" => mounted L q p m
local notation "pre" => prefixed L q p c m
local notation "init" => cleared L q p c m
local notation "done" => final L q p c m

include cap source sourceRows space roomRows given in
/-- The cumulative row count follows the actual stream. Each source group issues exactly
one tail store; a group with zero output rows writes the sink. -/
theorem run :
    (L.program q p w).Exec m (L.finalMem q p w m) (L.clocks q p) ∧ CheapCode (L.program q p w) ∧
    (∀i : Fin L.rows,L.output.read (L.finalMem q p w m) (i.val:Word w)=((encode q p (padded flat i)).val:Word w)) ∧
    (∀i : Fin L.groups, L.finalMem q p w m (L.prefix.base+i.val)=st (i.val+1)) ∧
    (∀j,j<L.origin → L.finalMem q p w m j=m j) := by
  have ok := L.fits q p w source space
  have b0 : L.origin ≤ L.prefix.base := Nat.le_add_right ..
  have b1 : L.prefix.base+L.prefix.size=L.output.base := rfl
  have b2 : L.output.base+L.output.size=L.sink := rfl
  have b3 : L.sink+1=L.addresses := rfl
  have wbound : L.addresses<2^w := by change L.addresses+L.groups+L.groups<2^w at space;omega
  have gCover : L.groups≤L.prefix.size := covered _
  have rCover : L.rows≤L.output.size := covered _
  have kCover : L.cap+1≤K := covered _
  have retained (j : ℕ) (small : j<L.origin) : warm j=m j :=
    DescentStaticWordColumn.frame L.origin L.entries (L.literal q p) m j (.inl small)
  have src (i : Fin L.groups) : L.source.read warm (i.val:Word w)=(c i:Word w) := by
    have iz:=i.isLt.trans_le sourceRows
    rw [DescentPackedZip.bank_read L.source warm iz source,retained _ ((Nat.add_lt_add_left iz _).trans_le source.2.2),given]
  have rankAt (i:Fin L.groups) : L.rank.eval warm (i.val:Word w)=(poolBatchCount (c i) q:Word w) := by
    have idx : c i<K := (Nat.lt_succ_of_le (cap i)).trans_le kCover
    change L.ceil.read warm (L.source.read warm (i.val:Word w))=_
    rw [src,DescentPackedZip.bank_read L.ceil warm idx ok.ceil]
    change warm (L.origin+c i)=_
    rw [mounted,DescentStaticWordColumn.read L.origin L.entries (L.literal q p) m
      (by change c i<2*K;omega : c i<L.entries)]
    simp [Layout.literal,idx]
  have lastAt (i:Fin L.groups) : L.datum.eval warm (i.val:Word w) = datum i := by
    have idx : c i<K := (Nat.lt_succ_of_le (cap i)).trans_le kCover
    change L.last.read warm (L.source.read warm (i.val:Word w))=_
    rw [src,DescentPackedZip.bank_read L.last warm idx ok.last]
    change warm (L.origin+K+c i)=_
    rw [mounted,Nat.add_assoc,DescentStaticWordColumn.read L.origin L.entries (L.literal q p) m
      (by change K+c i<2*K;omega : K+c i<L.entries)]
    simp [Layout.literal,patch,show ¬K+c i<K by omega]
  have start : st 0 = 0 := by simp [passed]
  have prefixAt (i:Fin L.groups) : L.prefix.read pre (i.val:Word w)=st (i.val+1) := by
    rw [DescentPackedZip.bank_read L.prefix pre (i.isLt.trans_le gCover) ok.prefix]
    exact DescentTerminalHeaderPrefixRAM.at_row L.prefix.base st warm i
  have keepPre (j : ℕ) (low:j<L.prefix.base) : pre j=warm j := by
    simp [prefixed,fillSegment,not_le.mpr low]
  have total (i : Word w) : L.total.eval pre i=((flat).length:Word w) := by
    by_cases h:L.groups=0
    · have nil:List.ofFn c=[] := List.length_eq_zero_iff.mp (by simpa using h)
      simp [Layout.total,h,Expr.eval,tape]
    · let z:Fin L.groups:=⟨L.groups-1,by omega⟩
      have last : z.val+1=L.groups := by dsimp [z];omega
      simp only [Layout.total,ite_eq_right h,Expr.eval]
      change L.prefix.read pre (z.val:Word w)=((tape q p c).length:Word w)
      rw [prefixAt z,last]
      change ((passed q p c L.groups).length:Word w)=((tape q p c).length:Word w)
      rw [passed_all q p c]
  have initAt (i:Fin L.rows) : init (L.output.base+i.val)=(value q p c 0 i.val:Word w) := by
    rw [show init (L.output.base+i.val)=(filling).eval pre (i.val:Word w) from
      ProtocolRAMGeneratedWrite.read_image _ _ _ _ i,initial]
    have iFit : i.val<2^w := i.isLt.trans_le (by omega)
    have lenFit : (flat).length<2^w :=roomRows.trans_lt (by omega)
    have less : ((i.val:Word w)<((flat).length:Word w)) ↔ i.val<(flat).length := by
      change (i.val:Word w).val < ((flat).length:Word w).val ↔ _
      rw [Fin.val_cast_of_lt iFit,Fin.val_cast_of_lt lenFit]
    by_cases yes:i.val<(flat).length <;>
      simp [Layout.fill,Expr.eval,total,DescriptorExpr.Comparison.test,less,yes]
  have keepInit (j : ℕ) (low:j<L.output.base) : init j=pre j :=
    ProtocolRAMGeneratedWrite.frame_image L.output.base L.rows filling pre j (.inl low)
  have both (j:ℕ) (low:j<L.prefix.base) : init j=warm j :=
    (keepInit j (by omega)).trans (keepPre j low)
  have later (i:Fin L.groups) : L.prefix.read init (i.val:Word w)=st (i.val+1) := by
    have pf:=i.isLt.trans_le gCover
    rw [DescentPackedZip.bank_read L.prefix init pf ok.prefix,keepInit _ (by omega),
      ←DescentPackedZip.bank_read L.prefix pre pf ok.prefix,prefixAt]
  have addrAt (i:Fin L.groups) : L.dest.eval init (i.val:Word w)=(addr i:Word w) := by
    have rk := (eval_below L.rank (i.val:Word w) warm init ok.rank both).trans (rankAt i)
    have next := passed_len q p c i
    have lim := (within q p c (i.val+1)).trans roomRows
    have nb : poolBatchCount (c i) q<2^w := by have:=ok.outputEnd;omega
    have chk : ((poolBatchCount (c i) q:ℕ):Word w)=0 ↔ poolBatchCount (c i) q=0 := by
      constructor
      · intro h
        simpa [Fin.val_cast_of_lt nb] using congrArg Fin.val h
      · intro h;simp [h]
    change (if L.rank.eval init (i.val:Word w) == (0:Word w) then (L.sink:Word w)
      else (DescentTerminalHeaderScatter.bounded L.output L.rawDest).eval init (i.val:Word w))=_
    rw [rk]
    by_cases inactive:poolBatchCount (c i) q=0
    · simp [inactive,target]
    · have pos : 1≤(passed q p c (i.val+1)).length := by omega
      let off := (passed q p c (i.val+1)).length-1
      have lt : off<L.output.size := by dsimp [off];omega
      have raw : L.rawDest.eval init (i.val:Word w)=((L.output.base+off:ℕ):Word w) := by
        change (L.output.base:Word w)+L.prefix.read init (i.val:Word w)-1=_
        rw [later,Nat.cast_add,show (off:Word w)=st (i.val+1)-1 by
          simpa [off] using (Nat.cast_sub (R:=Word w) pos)]
        abel
      have exact_ := DescentTerminalHeaderScatter.bounded_exact L.output L.rawDest init (i.val:Word w)
        ok.output wbound lt raw
      have nz : ((poolBatchCount (c i) q:ℕ):Word w)≠0 := fun e=>inactive (chk.mp e)
      simpa [nz,target,inactive,off] using exact_.trans raw
  have valAt (i:Fin L.groups) : L.datum.eval init (i.val:Word w)=datum i := by
    have fit:L.datum.Fits w L.prefix.base := ⟨ok.last,ok.rank.2⟩
    exact (eval_below L.datum _ warm init fit both).trans (lastAt i)
  have span := target_range q p c L.output.base L.sink roomRows (by omega : L.output.base+L.rows≤L.sink)
  let temp := ProtocolRAM.image L.words L.groups L.datum (ProtocolRAM.image L.addresses L.groups L.dest init)
  have tempFrame (j:ℕ) (low:j<L.addresses) : temp j=init j :=
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by have:=ok.columns;omega))).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl low))
  have preserved (j:ℕ) (low:j<L.output.base) : done j=pre j :=
    ((ProtocolRAMIndexedWrite.frame addr datum temp L.groups j
      (fun i=>by have:=(span i).1;omega)).trans (tempFrame j (by omega))).trans (keepInit j low)
  have stateEq (k : ℕ) (le_ : k≤L.groups) :
      DescentTerminalHeaderPrefixRAM.stateOn .add L.rank warm k=st k := by
    induction k with
    | zero => exact start.symm
    | succ k ih =>
      let i : Fin L.groups := ⟨k,by omega⟩
      change DescentTerminalHeaderPrefixRAM.stateOn .add L.rank warm k+
        L.rank.eval warm (i.val:Word w)=st (i.val+1)
      rw [ih (by omega),rankAt i]
      change ((passed q p c i.val).length:Word w)+(poolBatchCount (c i) q:Word w) =
        ((passed q p c (i.val+1)).length:Word w)
      rw [passed_len q p c i,Nat.cast_add]
  have sumsEq : L.sums q p w m=pre := by
    funext a
    by_cases hit : L.prefix.base≤a ∧ a<L.prefix.base+L.groups
    · simp only [Layout.sums,DescentTerminalHeaderPrefixRAM.result,prefixed,fillSegment,ite_eq_left hit,
        DescentTerminalHeaderPrefixRAM.file]
      exact stateEq _ (by omega)
    · simp only [Layout.sums,DescentTerminalHeaderPrefixRAM.result,prefixed,fillSegment,ite_eq_right hit]; rfl
  have filledEq : L.filled q p w m=init :=
    congrArg (ProtocolRAM.image L.output.base L.rows filling) sumsEq
  have addrEq : L.actualAddr q p w m=addr := by
    funext i
    change (L.dest.eval (L.filled q p w m) (i.val:Word w)).val=_
    rw [filledEq,addrAt,Fin.val_cast_of_lt ((span i).2.trans_lt (by omega))]
  have dataEq : L.actualData q p w m=datum := by
    funext i
    change L.datum.eval (L.filled q p w m) (i.val:Word w)=_
    rw [filledEq,valAt]
  have same : L.finalMem q p w m=done := by
    unfold Layout.finalMem final
    rw [filledEq,addrEq,dataEq]
  obtain ⟨executed,cheap⟩ := L.exec_any q p w m source space
  refine ⟨executed,cheap,?_,?_,?_⟩ <;> rw [same]
  · intro i
    rw [DescentPackedZip.bank_read L.output done (i.isLt.trans_le rCover) ok.output]
    exact scattered q p c L.output.base L.sink temp roomRows (by omega) (fun j=>
      (tempFrame (L.output.base+j.val) (by have:=j.isLt;omega)).trans (initAt j)) i
  · intro i
    rw [preserved _ (by have:=i.isLt;omega),←DescentPackedZip.bank_read L.prefix pre (i.isLt.trans_le gCover) ok.prefix,prefixAt]
  · intro j low
    exact (preserved j (by omega)).trans ((keepPre j (low.trans_le b0)).trans (retained j low))


end
end Hierarchy.DescentTerminalWidthRowsRAM

end OAI
