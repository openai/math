import OAI.ThreeFlat.Diagonal.RefreshRecordValues
import OAI.ThreeFlat.Diagonal.RefreshWidthFits
import OAI.ThreeFlat.Diagonal.RefreshSplitNative

namespace OAI
/-! # The retained refresh-node formulas execute exactly in native word arithmetic -/

namespace ThreeFlat.Diagonal.RefreshStageNav.Records

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows CompressorPacking.Native
open scoped Fin.CommRing
variable {W m t v : ℕ} (cur : Word W) (mem : Memory W) (vs : Fin 1 → Word W)
private abbrev nativeMemory (mem : Memory W) (i : ℕ) : ℕ := (mem i).val
private abbrev nativeOperands (vs : Fin 1 → Word W) (i : Fin 1) : ℕ := (vs i).val
private abbrev nativeValue (mem : Memory W) (vs : Fin 1 → Word W) (e : Formula 1) : ℕ :=
  Formula.natural W (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) e
private abbrev nativeFits (mem : Memory W) (vs : Fin 1 → Word W) (e : Formula 1) : Prop :=
  Formula.Fits W (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) e

private theorem index_parts (off radix : ℕ) (cap : (mem cur.val).val+off<2^W) (capR : radix<2^W) :
    let ix := index cur off
    nativeFits mem vs (.op .div ix (.lit radix)) ∧ nativeFits mem vs (.op .mod ix (.lit radix)) ∧
      nativeValue mem vs (.op .div ix (.lit radix))<2^W ∧ nativeValue mem vs (.op .mod ix (.lit radix))<2^W := by
  let ix := index cur off
  have fi := index_fit cur mem vs off cap
  have bi : nativeValue mem vs ix<2^W := (Nat.sub_le _ _).trans_lt (vs 0).isLt
  exact ⟨⟨fi,trivial,bi,capR⟩,⟨fi,trivial,bi,capR⟩,
    (Nat.div_le_self ..).trans_lt bi,(Nat.mod_le ..).trans_lt bi⟩

theorem kernel_fit (head : (mem cur.val).val+40<2^W) (small : 6<2^W) : nativeFits mem vs (kernel cur) := by
  have f := index_parts cur mem vs 34 5 (by omega) (by omega)
  have col := field_fit cur mem vs 36 (by omega)
  apply rowAt_fit (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) _ _ f.2.1 f.2.2.2 (by omega)
  intro i
  fin_cases i
  · exact ⟨trivial,cur.isLt⟩
  · exact f.1
  · trivial
  · trivial
  · exact ⟨col,⟨f.1,trivial,trivial⟩,trivial⟩

theorem halfHeader_fit (d : ℕ) (head : (mem cur.val).val+40<2^W) (small : 6<2^W) :
    nativeFits mem vs (halfHeader cur d) := by
  have f := index_parts cur mem vs 38 2 (by omega) (by omega)
  refine ⟨f.2.1,trivial,f.2.2.2,by change 0<2^W; omega,?_⟩
  split
  · trivial
  · exact ⟨field_fit cur mem vs 40 head,⟨f.1,trivial,trivial⟩,trivial⟩

private theorem site_fit (site : Expr) (m : ℕ) (head : (mem cur.val).val+40<2^W)
    (cap : m<2^W) (f : nativeFits mem vs site) (b : nativeValue mem vs site<2^W) :
    nativeFits mem vs (siteOrdinal m cur site).1 ∧ nativeFits mem vs (siteOrdinal m cur site).2 := by
  let lanes := field cur 8
  let vp := Formula.op .div site lanes
  have fl : nativeFits mem vs lanes := field_fit cur mem vs _ (by omega)
  have bl : nativeValue mem vs lanes<2^W := (mem _).isLt
  have fv : nativeFits mem vs vp := ⟨f,fl,b,bl⟩
  have bv : nativeValue mem vs vp<2^W := (Nat.div_le_self ..).trans_lt b
  exact ⟨⟨⟨⟨fv,trivial,bv,cap⟩,fl,trivial⟩,⟨f,fl,b,bl⟩,trivial⟩,⟨fv,trivial,bv,cap⟩⟩

theorem motif_fit (K : ℕ) (z : Block v t) (p : Fin m) (j : Fin 6)
    (head : (mem cur.val).val+40<2^W) (small : 6<2^W) (ports : m<2^W)
    (lanes : info (nativeMemory mem) cur 8=2^t) (addr : (vs 0).val=info (nativeMemory mem) cur 36+siteId z p*6+j.val)
    (room : info (nativeMemory mem) cur 2+blockId z*3+1<2^W) : nativeFits mem vs (motif cur m K) := by
  let site := Formula.op .div (index cur 36) (.lit 6)
  let block := (siteOrdinal m cur site).1
  let party := (siteOrdinal m cur site).2
  let choice := plus (field cur 2) (.op .mul block (.lit 3))
  have f := index_parts cur mem vs 36 6 (by omega) small
  have sf := site_fit cur mem vs site m head ports f.1 f.2.2.1
  have values := siteOrdinal_read cur (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) site z p lanes
    (splitIndex cur (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) 36 (siteId z p) j addr).1
  have cp : nativeFits mem vs choice := ⟨field_fit cur mem vs 2 (by omega),⟨sf.1,trivial,trivial⟩,trivial⟩
  have cv : nativeValue mem vs choice=info (nativeMemory mem) cur 2+blockId z*3 := congrArg (fun n=>info (nativeMemory mem) cur 2+n*3) values.1
  have mask : nativeFits mem vs (rowAt m (fun j=>.lit (2^j.val)) party) :=
    rowAt_fit (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) _ _ sf.2 (lt_of_eq_of_lt values.2 (p.isLt.trans ports))
      ports.le (fun _=>trivial)
  apply rowAt_fit (fun _ : Param => 0) (nativeMemory mem) (nativeOperands vs) _ _ f.2.1 f.2.2.2 small.le
  intro i
  fin_cases i
  · exact sf.1
  · exact ⟨field_fit cur mem vs 1 (by omega),⟨sf.1,trivial,trivial⟩,trivial⟩
  · exact ⟨⟨cp,trivial,trivial⟩,by change nativeValue mem vs choice+1<2^W; rwa [cv]⟩
  · have choiceFit : nativeValue mem vs choice < 2^W := by rw [cv]; omega
    exact ⟨cp, choiceFit⟩
  · trivial
  · exact mask


end ThreeFlat.Diagonal.RefreshStageNav.Records

end OAI
