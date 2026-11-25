import OAI.Hierarchy.DescentOverlapTables
import OAI.Hierarchy.DescentPackedSumWords

namespace OAI
/-! # Native conversion between arbitrary positive lane counts in successive dates -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ProtocolRAM DescentOrdinaryAtomFieldRAM.ROM DescentPackedZip DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H G A B a w : ℕ}

def term (base H G A B a : ℕ) (src : Bank) (j : Fin (pieces G A B)) : Expr :=
  let ptr:=Expr.lookup (ptrBank base H G A B a j.castSucc) .row
  let shift:=Expr.lookup (ptrBank base H G A B a (Fin.last _)) .row
  .branch .eq ptr (.lit (rows H G A)) (.lit 0)
    (.lookup (lutBank base H G A B a j) (.op .add shift (.lookup src ptr)))

def body (base H G A B a : ℕ) (src : Bank) : Expr :=
  total (term base H G A B a src) (List.finRange _)

def program (base H G A B a w : ℕ) (src : Bank) :=
  (tables base H G A B a w).seq (scan w (dest base H G A B a) (rows H G B) (body base H G A B a src))

def result (base H G A B a : ℕ) (src : Bank) (m : Memory w) :=
  image (dest base H G A B a) (rows H G B) (body base H G A B a src) (seeded base H G A B a m)

def ticks (base H G A B a : ℕ) (src : Bank) :=
  (8+10*(dest base H G A B a-base))+(4+rows H G B*(2*(body base H G A B a src).work+4))

theorem any (base H G A B a : ℕ) (src : Bank) (m : Memory w)
    (prior : src.Fits w base) (space : finish base H G A B a<2^w) :
    (program base H G A B a w src).Exec m (result base H G A B a src m) (ticks base H G A B a src) ∧
      (∀x,x< base ∨ finish base H G A B a≤ x→ result base H G A B a src m x=m x) ∧
      CheapCode (program base H G A B a w src) := by
  let out:=dest base H G A B a
  let tmp:=seeded base H G A B a m
  obtain ⟨init,pf,df,_,_,low⟩:=resident base m space
  have before : base≤ out:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have inputFits : src.Fits w out:=⟨prior.1,prior.2.1,prior.2.2.trans before⟩
  have fits : (body base H G A B a src).Fits w out:=by
    apply fits_total
    intro j
    exact ⟨⟨pf _,trivial⟩,trivial,trivial,df _,⟨pf _,trivial⟩,inputFits,pf _,trivial⟩
  refine ⟨?_,?_,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then init (scan_exec out (rows H G B) _ tmp fits space) machine
  · intro x hx
    have write:=ProtocolRAMGeneratedWrite.frame_image out (rows H G B) (body base H G A B a src) tmp x
      (hx.imp (fun b=>b.trans_le before) id)
    exact write.trans (low _ (hx.imp_right (fun hi=>(Nat.le_add_right ..).trans hi)))
  · apply cheap_seq
    · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply scan_cheap

theorem read (base : ℕ) (src : Bank) (mem : Memory w) (X : Fin H→ Fin G→ Cell a)
    (live : 0< A) (prior : src.Fits w base) (capacity : rows H G A≤ src.size)
    (raw : ∀p : Row H G A,mem (src.base+(row H G A p).val)=((data X p).val:Word w))
    (space : finish base H G A B a<2^w) (p : Row H G B) :
    result base H G A B a src mem (dest base H G A B a+(row H G B p).val)=((data X p).val:Word w) := by
  let tmp:=seeded base H G A B a mem
  let out:=dest base H G A B a
  let ix:=row H G B p
  have outRoom : out<2^w:=(Nat.le_add_right ..).trans_lt space
  obtain ⟨_,pf,df,stored,luts,keep⟩:=resident base mem space
  have mapRoom : ix.val<2^mapBits H G B :=ix.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
  have addresses (j : Fin (pieces G A B+1)) :
      (ptrBank base H G A B a j).read tmp (ix.val:Word w)=
      ((if j.val< pieces G A B then pointer (A:=A) p j.val else phase p.2.val B A*stride a A:ℕ):Word w) :=
    (bank_read _ tmp mapRoom (pf j)).trans (stored j p)
  have correct (j : Fin (pieces G A B)) :
      (term base H G A B a src j).eval tmp (ix.val:Word w)=(contribution (A:=A) X p j.val:Word w) := by
    have ptr:=addresses j.castSucc
    have sh:=addresses (Fin.last _)
    simp only [Fin.val_castSucc,j.isLt,ite_true] at ptr
    simp only [Fin.val_last,lt_self_iff_false,ite_false] at sh
    rw [term]
    simp only [Expr.eval,ptr,sh,Comparison.test,RowOp.opcode,BinaryOp.eval]
    cases eqn:source (A:=A) p j.val with
    | none=>simp [pointer,contribution,eqn]
    | some q=>
      let id₀:=row H G A q
      let s : Fin A:=⟨phase p.2.val B A,Nat.mod_lt _ live⟩
      let z:=data X q
      have oldSize : rows H G A<2^w:=capacity.trans_lt prior.2.1
      have diff : (id₀.val:Word w)≠((rows H G A:ℕ):Word w):=by
        intro same
        have both:=congrArg Fin.val same
        rw [Fin.val_cast_of_lt (id₀.isLt.trans oldSize),Fin.val_cast_of_lt oldSize] at both
        exact id₀.isLt.ne both
      have old:=bank_read src tmp (id₀.isLt.trans_le capacity) prior
      have protect : tmp (src.base+id₀.val)=mem (src.base+id₀.val) :=
        keep _ (Or.inl ((Nat.add_lt_add_left (id₀.isLt.trans_le capacity) _).trans_le prior.2.2))
      have oldValue : src.read tmp (id₀.val:Word w)=(z.val:Word w) :=old.trans (protect.trans (raw q))
      have tableVal:=luts j s z
      have sBound : s.val<2^Nat.clog 2 (A+1):=
        s.isLt.trans_le ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
      have fit : s.val*stride a A+z.val<(lutBank base H G A B a j).size:=by
        change _<2^keyBits a A
        rw [keyBits,pow_add]
        exact (Nat.add_lt_add_left z.isLt _).trans_le (by simp only [stride]; rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ sBound)
      have tab:=(bank_read _ tmp fit (df j)).trans tableVal
      simp only [pointer,eqn,Option.elim_some,contribution,beq_iff_eq]
      change (if (id₀.val:Word w)=((rows H G A:ℕ):Word w) then _ else _)=_
      rw [ite_eq_right diff,oldValue,←Nat.cast_add]
      exact tab
  have sum:=DescentPackedSumWords.eval_sum _ (fun j : Fin (pieces G A B)=>contribution (A:=A) X p j.val)
    tmp (ix.val:Word w) correct (List.finRange _)
  rw [←List.ofFn_eq_map,List.sum_ofFn,reconstruct live] at sum
  exact (ProtocolRAMGeneratedWrite.read_image out _ _ tmp ix).trans sum

end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
