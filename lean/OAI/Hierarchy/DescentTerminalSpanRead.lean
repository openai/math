import OAI.Hierarchy.DescentTerminalSpanCursor

namespace OAI
/-! # Native owner and offset on every bounded row, including the holes between bins -/
namespace Hierarchy.DescentTerminalSpanBook.Cursors
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRecipeRows DescentTerminalBinPack
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w n q W S : ℕ} (L : Cursors) (m : Memory w) (f : L.Fits w n)
def Facts (sites : Fin S→Site) (p : Fin n) (fit : ∀i,(sites i).rows q≤W) (mem : Memory w) :=
  let whereAt:=resolve sites fit p.val
  (L.active.read mem (p.val:Word w)=(if whereAt.isSome then 1 else 0)) ∧
    ∀(i:Fin S) (s:Fin W),whereAt=some (i,s) →
      L.owner.read mem (p.val:Word w)=(i.val:Word w) ∧ L.localRow.read mem (p.val:Word w)=(s.val:Word w)

include f in
theorem read (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W) (p : Fin n)
    (siteRoom:S<2^w) (localRoom:n≤L.localRow.size) (_positive:0<w)
    (markers : ∀i:Fin n,L.marker.read m (i.val:Word w)=((mark (W:=W) (q:=q) sites i.val):Word w))
    (startRead : ∀i:Fin S,L.first.read m (i.val:Word w)=((DescentTerminalBinPack.first W (counts (q:=q) sites) i):Word w))
    (endRead : ∀i:Fin S,L.last.read m (i.val:Word w)=((DescentTerminalBinPack.last W (counts (q:=q) sites) i):Word w))
    (past : ∀i:Fin S,DescentTerminalBinPack.last W (counts (q:=q) sites) i<2^w) :
    Facts (q:=q) L sites p fit (L.final n m) := by
  let C:=counts (q:=q) sites
  let r:=count (W:=W) (q:=q) sites (p.val+1)
  have num:=f.number.2.2;have act:=f.active.2.2;have own:=f.owner.2.2
  have ranges:=f.ranges;have endAt:=f.endAt
  have pi:p.val<2^w:=by omega
  have rc : r≤S:=by simpa [r,count,prior] using
    (Finset.card_le_card (Finset.filter_subset (fun i:Fin S=>DescentTerminalBinPack.first W C i<p.val+1) Finset.univ))
  have countAt:=printed_count L m f sites markers p
  have rawRead: L.raw.eval (L.state n m) (p.val:Word w)=(r:Word w):=by
    simpa [raw,Expr.eval,Bank.read,Fin.val_cast_of_lt pi,Nat.mod_eq_of_lt (p.isLt.trans_le ranges.1),r] using countAt
  have base (b:Bank) (bf:b.Fits w L.number.base) (x:Word w) :
      b.read (L.state n m) x=b.read m x := by
    have low:=bf.2.2;have hg:=Nat.mod_lt x.val bf.1
    simp [Bank.read,state,DescentTerminalHeaderPrefixRAM.result,fillSegment,
      not_le.mpr (show b.base+x.val%b.size<L.number.base by omega)]
  have beforeActive {a:ℕ} (h:a<L.active.base) : L.activated n m a=L.state n m a:=
    DescentTerminalChipRuntime.image_low _ _ _ _ h
  have beforeOwner {a:ℕ} (h:a<L.active.base) : L.located n m a=L.state n m a:=
    (DescentTerminalChipRuntime.image_low _ _ _ _ (by omega)).trans (beforeActive h)
  have rd (b : Bank) (lo:b.Fits w L.active.base) (x:Word w) :
      b.read (L.activated n m) x=b.read (L.state n m) x ∧ b.read (L.located n m) x=b.read (L.state n m) x := by
    have bounded:=Nat.mod_lt x.val lo.1;have e:=lo.2.2
    have below : b.base+x.val%b.size<L.active.base := by omega
    exact ⟨beforeActive below,beforeOwner below⟩
  have y : L.number.read (L.state n m) (p.val:Word w)=(r:Word w):=rawRead
  have yes : L.active.read (L.final n m) (p.val:Word w)=L.covered.eval (L.state n m) (p.val:Word w):=by
    unfold Bank.read
    rw [Fin.val_cast_of_lt pi,Nat.mod_eq_of_lt (p.isLt.trans_le ranges.2.1),final,
      DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),located,DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),
      activated,DescentTerminalChipRuntime.image_at _ _ _ _ p]
  have who : L.owner.read (L.final n m) (p.val:Word w)=(r:Word w)-1:=by
    unfold Bank.read
    rw [Fin.val_cast_of_lt pi,Nat.mod_eq_of_lt (p.isLt.trans_le ranges.2.2),final,
      DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),located,DescentTerminalChipRuntime.image_at _ _ _ _ p]
    change L.number.read (L.activated n m) (p.val:Word w)-1=(r:Word w)-1
    rw [(rd _ f.number _).1,y]
  have off : L.localRow.read (L.final n m) (p.val:Word w)=(p.val:Word w)-L.first.read m ((r:Word w)-1):=by
    unfold Bank.read
    rw [Fin.val_cast_of_lt pi,Nat.mod_eq_of_lt (p.isLt.trans_le localRoom),final,
      DescentTerminalChipRuntime.image_at _ _ _ _ p]
    change (p.val:Word w)-L.first.read (L.located n m) (L.number.read (L.located n m) (p.val:Word w)-1)=
      (p.val:Word w)-L.first.read m ((r:Word w)-1)
    rw [(rd _ f.number _).2,(rd _ (DescentTerminalChipRuntime.bankMono f.first (by omega)) _).2,y,base _ f.first]
  have control : L.covered.eval (L.state n m) (p.val:Word w) =
      (if (r:Word w)=0 then 0
       else if (p.val:Word w)<L.first.read (L.state n m) ((r:Word w)-1) then 0
       else if L.last.read (L.state n m) ((r:Word w)-1)<(p.val:Word w) then 0 else 1) := by
    simp only [covered,site,raw,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,
      beq_iff_eq,decide_eq_true_eq,y,Nat.cast_zero,Nat.cast_one]
  unfold Facts
  dsimp only
  rw [yes,control]
  by_cases zero:r=0
  · have empty : resolve sites fit p.val=none := by
      unfold resolve
      change (if h : 0<r ∧ r-1<S then _ else none)=none
      rw [dite_eq_right (by omega)]
    simp [empty,zero]
  · let i : Fin S:=⟨r-1,by omega⟩
    have small:=rc.trans_lt siteRoom
    have diff : (r:Word w)-1=(i.val:Word w):=by change _=(((r-1):ℕ):Word w);rw [Nat.cast_sub (by omega : 1≤r)];simp
    have live : 0<r ∧ r-1<S:=by omega
    let lo:=DescentTerminalBinPack.first W C i;let hi:=DescentTerminalBinPack.last W C i
    have sz:0<C i:=by simp [C,Site.rows]
    have eqhi:hi=lo+C i-1:=rfl
    have ls:lo<2^w:=by have:=past i;change hi<2^w at this;omega
    have keep : resolve sites fit p.val =
        if hit : lo≤p.val ∧ p.val-lo<C i then some (i,⟨p.val-lo,hit.2.trans_le (fit i)⟩) else none := by
      unfold resolve
      dsimp only
      rw [dite_eq_left live]
    have rz:(r:Word w)≠0 := by
      intro eqn
      apply zero
      simpa only [Fin.val_cast_of_lt small,Fin.val_zero] using congrArg Fin.val eqn
    have bounds : (lo:Word w) ≤ (p.val:Word w) ↔ lo≤p.val :=by simp [Fin.le_iff_val_le_val,Fin.val_cast_of_lt ls,Fin.val_cast_of_lt pi]
    have hs : hi < 2^w := past i
    have tops : (p.val:Word w) ≤ (hi:Word w) ↔ p.val≤hi :=by simp [Fin.le_iff_val_le_val,Fin.val_cast_of_lt pi,Fin.val_cast_of_lt hs]
    have lval : L.first.read (L.state n m) (i.val:Word w)=(lo:Word w):=(base _ f.first _).trans (startRead i)
    have hval : L.last.read (L.state n m) (i.val:Word w)=(hi:Word w):=(base _ f.last _).trans (endRead i)
    by_cases hit : lo≤p.val ∧ p.val-lo<C i
    · rw [keep, dite_eq_left hit]
      have top:p.val≤hi:=by omega
      constructor
      · simp [rz,diff,lval,hval,not_lt.mpr (bounds.mpr hit.1),not_lt.mpr (tops.mpr top)]
      · intro v s same;obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj same)
        refine ⟨who.trans diff,?_⟩
        rw [off,diff,startRead]
        exact (Nat.cast_sub hit.1).symm
    · rw [keep, dite_eq_right hit]
      constructor
      · by_cases less:lo≤p.val
        · have short:hi<p.val:=by omega
          have hiWord:(hi:Word w)<(p.val:Word w):=lt_of_not_ge (fun h=>by have:=tops.mp h;omega)
          simp [rz,diff,lval,hval,not_lt.mpr (bounds.mpr less),hiWord]
        · have loWord:(p.val:Word w)<(lo:Word w):=lt_of_not_ge (fun h=>less (bounds.mp h))
          simp [rz,diff,lval,loWord]
      · simp

end
end Hierarchy.DescentTerminalSpanBook.Cursors

end OAI
