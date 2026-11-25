import OAI.Hierarchy.DescentPackedMatchedGather
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.DescentPackedMaskedData

namespace OAI
/-! # All dyadic source leaves in one key-major packed matching descriptor bank -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {d N K H G M w r D p : ℕ}

def allExprs (tables : Fin N→Tables) (field : Fin N→Expr) (dict : Fin K→Bank) (mask : Bank) :=
  List.ofFn fun key=>lookup (dict key) mask (assembly tables field)

def passes (tables : Fin N→Tables) (field : Fin N→Expr) (dict : Fin K→Bank) (mask : Bank) (base H G M : ℕ) :=
  ProbeStage.Native.columns (H*chunks G M) base (allExprs tables field dict mask)

def all (w : ℕ) (tables : Fin N→Tables) (field : Fin N→Expr) (dict : Fin K→Bank) (mask : Bank) (base H G M : ℕ) :=
  ProtocolRAM.program w (passes tables field dict mask base H G M)

def ptr (base H G M key : ℕ) := base+key*(H*chunks G M)

theorem collect_work (tables : Fin N→Tables) (field : Fin N→Expr) (is : List (Fin N)) (L : ℕ)
    (h : ∀i,(field i).work≤L) : (collect tables field is).work≤1+is.length*(L+11) := by
  induction is with
  | nil => simp [collect,Expr.work]
  | cons i is ih =>
    have bound := h i
    simp only [collect,Tables.read,Expr.work,List.length_cons,Nat.succ_mul]
    omega

theorem clock_le (tables : Fin N→Tables) (field : Fin N→Expr) (dict : Fin K→Bank) (mask : Bank) (base H G M L : ℕ)
    (h : ∀i,(field i).work≤L) :
    clock (passes tables field dict mask base H G M)≤4+K*(4+H*chunks G M*(2*(14+N*(L+11))+4)) := by
  have c := collect_work tables field (List.finRange N) L h
  rw [List.length_finRange] at c
  unfold passes
  have bound := ProbeStage.Native.columns_clock (H*chunks G M) base (14+N*(L+11)) (allExprs tables field dict mask) (by
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    simp only [lookup,Expr.work,assembly]
    omega)
  simpa only [allExprs,List.length_ofFn] using bound

theorem terrain_work (winner : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports D) (H : ℕ)
    (i : Fin (fields r D p)) : (expr winner marked P H i).work≤45 := by
  induction i using Fin.addCases with
  | left x => simp only [expr,Fin.addCases_left,Expr.work];decide
  | right t =>
    induction t using Fin.addCases with
    | left s => simp only [expr,Fin.addCases_right,Fin.addCases_left,Expr.work];decide
    | right t => simp only [expr,Fin.addCases_right,DescentPackedColony.peerExpr,DescentPackedColony.neighborID,Expr.work];decide

theorem all_run (tables : Fin (fields r D p)→Tables) (field : Fin (fields r D p)→Expr) (base : ℕ)
    (s : Shape) (B : ℕ) (dict : Fin K→Bank) (mask : Bank) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field base) (static : ∀i,Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,Source (field i) (fun h g=>terrain u h g i) M m) (df : ∀key,(dict key).Fits w base) (mf : mask.Fits w base)
    (bits : ∀key,(dict key).bits=(d*fields r D p)*M) (span : H*chunks G M≤ mask.size) (wide : base+K*(H*chunks G M)<2^w)
    (size : s.inputBits*M≤w) (fixed : ∀key : Fin K,∀i : Cell ((d*fields r D p)*M),m ((dict key).base+i.val)=
      ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key.val) i).val:Word w))
    (maskWord : ∀t : Row H G M,m (mask.base+(row H G M t).val)=(DescentSIMDLookup.maskWord s.inputBits M G t.2.val:Word w)) :
    let ps := passes tables field dict mask base H G M
    let end_ := result ps m
    (all w tables field dict mask base H G M).Exec m end_ (clock ps) ∧
    (∀key : Fin K,∀h : Fin H,∀g : Fin G,∀hm : 0<M,digit s.inputBits (lane g hm).val
      ((end_ (ptr base H G M key.val+(row H G M (position h g hm)).val)).val)=
        (encodeInput (inputs s B key.val (u h g) (fun _=>0))).val) ∧
    (∀a<base,end_ a=m a) ∧ CheapCode (all w tables field dict mask base H G M) := by
  let es := allExprs tables field dict mask
  have len : es.length=K := List.length_ofFn
  have fit (e) (he : e∈es) : e.Fits w base := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    simp [lookup,Expr.Fits,mf,df,assembly,fits tables field base bounds]
  refine ⟨ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es le_rfl fit (by simpa only [len] using wide)),?_,
    (fun _ h=>ProbeStage.Native.columns_frame es m (Or.inl h)),@ProtocolRAM.program_cheap _ _⟩
  intro key h g hm
  let i := row H G M (position h g hm)
  have kpos : 0<K := Nat.zero_lt_of_lt key.isLt
  have inside : base+H*chunks G M<2^w := (Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right (H*chunks G M) kpos) _).trans_lt wide
  have physical := (run tables field base s B key.val (dict key) mask u m bounds static source (df key) mf (bits key)
    span inside size (fixed key) maskWord).2.1 h g hm
  have same := ProbeStage.Native.columns_read es m le_rfl fit key.val (key.isLt.trans_eq len.symm) i
  have single := ProtocolRAMGeneratedWrite.read_image base (H*chunks G M) (lookup (dict key) mask (assembly tables field)) m i
  simp only [es,allExprs,List.getElem_ofFn] at same
  exact (congrArg (fun t : Word w=>digit s.inputBits (lane g hm).val t.val) (same.trans single.symm)).trans physical

theorem all_words (tables : Fin (fields r D p)→Tables) (field : Fin (fields r D p)→Expr) (base : ℕ)
    (s : Shape) (B : ℕ) (dict : Fin K→Bank) (mask : Bank) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field base) (static : ∀i,Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,Source (field i) (fun h g=>terrain u h g i) M m) (df : ∀key,(dict key).Fits w base) (mf : mask.Fits w base)
    (bits : ∀key,(dict key).bits=(d*fields r D p)*M) (span : H*chunks G M≤ mask.size) (wide : base+K*(H*chunks G M)<2^w)
    (size : s.inputBits*M≤w) (fixed : ∀key : Fin K,∀i : Cell ((d*fields r D p)*M),m ((dict key).base+i.val)=
      ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key.val) i).val:Word w))
    (maskWord : ∀t : Row H G M,m (mask.base+(row H G M t).val)=(DescentSIMDLookup.maskWord s.inputBits M G t.2.val:Word w)) (key : Fin K) (t : Row H G M) :
    result (passes tables field dict mask base H G M) m (ptr base H G M key.val+(row H G M t).val)=
      ((data (fun h g=>encodeInput (inputs s B key.val (u h g) (fun _=>0))) t).val:Word w) := by
  let es := allExprs tables field dict mask
  have len : es.length=K := List.length_ofFn
  have fit (e) (he : e∈es) : e.Fits w base := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    simp [lookup,Expr.Fits,mf,df,assembly,fits tables field base bounds]
  have kpos : 1 ≤ K := Nat.zero_lt_of_lt key.isLt
  have firstColumn : H*chunks G M ≤ K*(H*chunks G M) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (H*chunks G M) kpos
  have inside : base+H*chunks G M<2^w := (Nat.add_le_add_left firstColumn base).trans_lt wide
  have same := ProbeStage.Native.columns_read es m le_rfl fit key.val (key.isLt.trans_eq len.symm) (row H G M t)
  simp only [es,allExprs,List.getElem_ofFn] at same
  have output := eval_word tables field base s B key.val (dict key) mask u m bounds static source (df key) mf
    (bits key) span inside size (fixed key) maskWord t
  exact same.trans (by simpa only [masked_eq_data,descriptor,decode_encode_panel] using output)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
