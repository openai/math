import OAI.Hierarchy.DescentPackedProfileRepackWords

namespace OAI
/-! # Native transfer from the original compact proposal to a dated matcher raw bank -/
namespace Hierarchy.DescentPackedProfileRepack
open DescentSIMDLookup DescentTerminalEpochChart DescentTerminalEpochBits DescentPackedProfileTape
open DescentPackedProfileArchive DescentPackedProfileWindow DescentPackedProfileWide
open DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable (base A B d : ℕ) (source raw : Bank)

/-- Every destination cell is derived from the original private proposal, including
the final partially filled row, the two window guards and all remaining dyadic padding. -/
theorem issued {P : Type} {w : ℕ} (entry : Source P) (z : P→Bool) (extend : width entry.C≤d)
    (m : Memory w) (oldPos : 0<A) (newPos : 0<B)
    (prior : source.Fits w base) (cap : slots entry.seats A≤ source.size)
    (observed : ∀j : Fin (slots entry.seats A),m (source.base+j.val)=((packed entry.pin z A j.val).val:Word w))
    (apart : workEnd base entry.seats A B (width entry.C)≤raw.base)
    (room : raw.base+raw.size<2^w) :
    Stored entry d B extend raw z (image base entry.seats A B (width entry.C) d source raw m) := by
  let c:=width entry.C
  let start:=Overlap.endAddress base 1 entry.seats A B c
  let dst:=Overlap.outputBank base 1 entry.seats A B c
  let lut:=book base entry.seats A B c
  let n:=chunks entry.seats B
  let input:=fun (_ : Fin 1) (q : Fin entry.seats)=>cell entry.pin z q.val
  let mid:=Overlap.result base 1 entry.seats A B c source m
  let table:=DescentStaticWordColumn.image start (widen c d B) mid (2^(c*B))
  have endBound : start+2^(c*B)<2^w := apart.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have geom:=Overlap.output_fits base 1 entry.seats A B c w ((Nat.le_add_right ..).trans_lt endBound)
  have oldSize : Overlap.rows 1 entry.seats A≤ source.size := by
    simpa only [Overlap.rows,Nat.one_mul] using (chunk_slots entry.seats A oldPos).trans cap
  have oldRead (p : Row 1 entry.seats A) : m (source.base+(row 1 entry.seats A p).val)=((data input p).val:Word w) := by
    rw [row_one,show data input p=packed entry.pin z A p.2.val from actual_data entry z p]
    exact observed ⟨p.2.val,p.2.isLt.trans_le (chunk_slots entry.seats A oldPos)⟩
  have rowFit : n≤dst.size := by simpa [Overlap.rows,dst,n] using geom.2.1
  have nFit : n<2^w := rowFit.trans_lt geom.1.2.1
  intro j physical
  have jr : j<2^w := physical.trans ((Nat.le_add_left ..).trans_lt room)
  rw [show image base entry.seats A B c d source raw m=ProtocolRAM.image raw.base raw.size (body entry.seats B lut dst) table from rfl,
    ProtocolRAMGeneratedWrite.read_image _ _ _ _ (⟨j,physical⟩ : Fin raw.size)]
  have boundWord : ((chunks entry.seats B : ℕ):Word w).val=chunks entry.seats B:=Fin.val_cast_of_lt nFit
  by_cases useRow : j<chunks entry.seats B
  · let p : Row 1 entry.seats B := (0,⟨j,useRow⟩)
    have addr : (row 1 entry.seats B p).val=j := row_one p
    let v:=packed entry.pin z B j
    have found := Overlap.read base source m input oldPos prior oldSize oldRead
      (geom.2.2.trans_lt ((Nat.le_add_right ..).trans_lt endBound)) p
    have priorRead : mid (dst.base+j)=(v.val:Word w) := by
      rw [addr,show data input p=v from actual_data entry z p] at found
      exact found
    have belowTable : dst.base+j< start :=
      (Nat.add_lt_add_left (useRow.trans_le rowFit) dst.base).trans_le geom.1.2.2
    have valueRead : (Expr.lookup dst .row).eval table (j:Word w)=(v.val:Word w) :=
      (lookup_nat dst table _ .row j rfl (useRow.trans_le rowFit) geom.1.2.1).trans
        ((DescentStaticWordColumn.frame start _ (widen c d B) mid _ (.inl belowTable)).trans priorRead)
    have packedRead : (Expr.lookup lut (.lookup dst .row)).eval table (j:Word w)=
        ((word d B (wideCell entry.pin z d extend) j).val:Word w) := by
      rw [lookup_nat lut table _ _ v.val valueRead v.isLt ((Nat.le_add_left ..).trans_lt endBound)]
      exact (DescentStaticWordColumn.read start _ (widen c d B) mid v.isLt).trans
        (congrArg (fun t : ℕ=>(t:Word w)) (widen_word entry z d B extend j))
    simpa only [body,Expr.eval,DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt jr,boundWord,
      decide_eq_true_eq,ite_eq_left useRow] using packedRead
  · have guard:=wide_guard entry z d B extend newPos j (Nat.le_of_not_gt useRow)
    simp only [body,Expr.eval,DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt jr,boundWord,
      decide_eq_true_eq,ite_eq_right useRow,guard,Fin.val_zero,Nat.cast_zero]

end
end Hierarchy.DescentPackedProfileRepack

end OAI
