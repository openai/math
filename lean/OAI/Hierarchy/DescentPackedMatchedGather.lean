import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedMatchedInput
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Native packing of the source and all corresponding neighbor winner fields -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {d N H G M w r D p : ℕ}


/-- First two field families read the source host. The third family gathers the
corresponding group lane from each immutable neighbor host in runtime memory. -/
def terrain (u : Fin H→Fin G→Panel r D p d) (h : Fin H) (g : Fin G) (i : Fin (fields r D p)) : Cell d :=
  (encode d (fields r D p)).symm (encodePanel (u h g)) i

def expr (winner : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports D) (H : ℕ) :
    Fin (fields r D p)→Expr := Fin.addCases (fun x=>.lookup (winner x) .row) (Fin.addCases
    (fun s : Fin (r*p)=>.lookup (marked (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2) .row)
    (fun t : Fin (D*r)=>DescentPackedColony.peerExpr P (winner (finProdFinEquiv.symm t).2) H (finProdFinEquiv.symm t).1))

def fromPeers (winner : Fin H→Fin G→Fin r→Cell d) (marked : Fin H→Fin G→Fin r→Fin p→Cell d)
    (roster : Fin H→Fin D→Option (Fin H)) (h : Fin H) (g : Fin G) : Panel r D p d :=
  ⟨winner h g,marked h g,fun i x=>(roster h i).elim 0 (fun v=>winner v g x)⟩

theorem real_fields (winner : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports D)
    (a : Fin H→Fin G→Fin r→Cell d) (b : Fin H→Fin G→Fin r→Fin p→Cell d) (roster : Fin H→Fin D→Option (Fin H))
    (out : ℕ) (m : Memory w) (real : DescentPackedColony.Mounted P roster m G M)
    (access : ∀x,DescentPackedColony.Accessible P (winner x) H G M w out)
    (markFit : ∀x i,(marked x i).Fits w out) (markRoom : ∀x i,H*chunks G M≤(marked x i).size)
    (own : ∀x,DescentPackedColony.Reads (winner x) (fun h g=>a h g x) M m)
    (marks : ∀x i,DescentPackedColony.Reads (marked x i) (fun h g=>b h g x i) M m) (i : Fin (fields r D p)) :
    Source (expr winner marked P H i) (fun h g=>terrain (fromPeers a b roster) h g i) M m := by
  induction i using Fin.addCases with
  | left x =>
    have readWinner (h : Fin H) (g : Fin G) :
        terrain (fromPeers a b roster) h g (Fin.castAdd (r*p+D*r) x) = a h g x :=
      congrArg (fun u : Panel r D p d => u.winner x) (decode_encode_panel (fromPeers a b roster h g))
    simpa only [expr,Fin.addCases_left,readWinner] using
      source_column (winner x) out (access x).source m (fun h g=>a h g x) (access x).srcRoom (own x)
  | right i =>
    induction i using Fin.addCases with
    | left s =>
      obtain ⟨⟨x,j⟩,rfl⟩ := finProdFinEquiv.surjective s
      have readMarked (h : Fin H) (g : Fin G) :
          terrain (fromPeers a b roster) h g (Fin.natAdd r (Fin.castAdd (D*r) (finProdFinEquiv (x,j)))) =
            b h g x j :=
        congrArg (fun u : Panel r D p d => u.neighbor x j) (decode_encode_panel (fromPeers a b roster h g))
      simpa only [expr,Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply,readMarked] using
        source_column (marked x j) out (markFit x j) m (fun h g=>b h g x j) (markRoom x j) (marks x j)
    | right t =>
      obtain ⟨⟨v,x⟩,rfl⟩ := finProdFinEquiv.surjective t
      have readPeer (h : Fin H) (g : Fin G) :
          terrain (fromPeers a b roster) h g (Fin.natAdd r (Fin.natAdd (r*p) (finProdFinEquiv (v,x)))) =
            (roster h v).elim 0 (fun other => a other g x) :=
        congrArg (fun u : Panel r D p d => u.peerWinner v x) (decode_encode_panel (fromPeers a b roster h g))
      simpa only [expr,Fin.addCases_right,Equiv.symm_apply_apply,readPeer] using
        DescentPackedColony.peerSource P (winner x) out (access x) roster m real (fun h g=>a h g x) (own x) v

theorem assembled (tables : Fin (fields r D p)→Tables) (field : Fin (fields r D p)→Expr) (out : ℕ)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field out) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (static : ∀i,Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,Source (field i) (fun h g=>terrain u h g i) M m) :
    Source (assembly tables field) (fun h g=>encodePanel (u h g)) M m := by
  have got := collected tables field out bounds m static (terrain u) source (List.finRange (fields r D p))
  simpa only [assembly,List.mem_finRange,ite_true,terrain,Equiv.apply_symm_apply] using got

def lookup (dict mask : Bank) (src : Expr) := Expr.op .mask (.lookup dict src) (.lookup mask .row)

def program (tables : Fin N→Tables) (field : Fin N→Expr) (dict mask : Bank) (out H G M w : ℕ) :=
  scan w out (H*chunks G M) (lookup dict mask (assembly tables field))

theorem eval_word (tables : Fin (fields r D p)→Tables) (field : Fin (fields r D p)→Expr) (out : ℕ)
    (s : Shape) (B key : ℕ) (dict mask : Bank) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field out)
    (static : ∀i,Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,Source (field i) (fun h g=>terrain u h g i) M m)
    (df : dict.Fits w out) (mf : mask.Fits w out) (bits : dict.bits=(d*fields r D p)*M)
    (span : H*chunks G M≤ mask.size) (_wide : out+H*chunks G M<2^w) (size : s.inputBits*M≤w)
    (fixed : ∀i : Cell ((d*fields r D p)*M),m (dict.base+i.val)=
      ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key) i).val:Word w))
    (maskWord : ∀t : Row H G M,m (mask.base+(row H G M t).val)=(DescentSIMDLookup.maskWord s.inputBits M G t.2.val:Word w)) (t : Row H G M) :
    (lookup dict mask (assembly tables field)).eval m ((row H G M t).val:Word w)=
      (masked (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key) (fun h g=>encodePanel (u h g)) t:Word w) := by
  let f := descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key
  let x := fun h g=>encodePanel (u h g)
  let i := row H G M t
  let e := lookup dict mask (assembly tables field)
  have rows := assembled tables field out bounds u m static source
  change e.eval m (i.val:Word w)=((masked f x t:ℕ):Word w)
  let src := data x t
  have within : src.val<dict.size := by simp [Bank.size,bits]
  have gathered : (assembly tables field).eval m (i.val:Word w)=(src.val:Word w) := rows t
  have tableRead : dict.read m (src.val:Word w)=((DescentSIMDLookup.table f src).val:Word w) :=
    (DescentPackedZip.bank_read dict m within df).trans (fixed src)
  have maskRead : mask.read m (i.val:Word w)=(DescentSIMDLookup.maskWord s.inputBits M G t.2.val:Word w) :=
    (DescentPackedZip.bank_read mask m (i.isLt.trans_le span) mf).trans (maskWord t)
  change RowOp.mask.opcode.eval (dict.read m ((assembly tables field).eval m (i.val:Word w)))
    (mask.read m (i.val:Word w))=_
  rw [gathered,tableRead,maskRead]
  have valueFits : (DescentSIMDLookup.table f src).val<2^w :=
    (DescentSIMDLookup.table f src).isLt.trans_le (Nat.pow_le_pow_right (by decide) size)
  have available := (Nat.mul_le_mul_left s.inputBits (min_le_left M (G-t.2.val*M))).trans size
  have maskFits : DescentSIMDLookup.maskWord s.inputBits M G t.2.val<2^w := by
    have cmp : 2^(s.inputBits*used G M t.2.val)≤2^w := Nat.pow_le_pow_right (by decide) available
    have pos : 0<2^(s.inputBits*used G M t.2.val) := by positivity
    unfold DescentSIMDLookup.maskWord
    omega
  have maskedEq : (DescentSIMDLookup.table f src).val &&& ((DescentSIMDLookup.maskWord s.inputBits M G t.2.val:Word w)).val=masked f x t := by
    rw [Fin.val_cast_of_lt maskFits]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  simp only [RowOp.opcode,Computability.VPVNP.BurstRAM.PrivateRAM.BinaryOp.eval,Fin.val_cast_of_lt valueFits,maskedEq]; rfl

theorem run (tables : Fin (fields r D p)→Tables) (field : Fin (fields r D p)→Expr) (out : ℕ)
    (s : Shape) (B key : ℕ) (dict mask : Bank) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field out)
    (static : ∀i,Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,Source (field i) (fun h g=>terrain u h g i) M m)
    (df : dict.Fits w out) (mf : mask.Fits w out) (bits : dict.bits=(d*fields r D p)*M)
    (span : H*chunks G M≤ mask.size) (wide : out+H*chunks G M<2^w) (size : s.inputBits*M≤w)
    (fixed : ∀i : Cell ((d*fields r D p)*M),m (dict.base+i.val)=
      ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key) i).val:Word w))
    (maskWord : ∀t : Row H G M,m (mask.base+(row H G M t).val)=(DescentSIMDLookup.maskWord s.inputBits M G t.2.val:Word w)) :
    let e := lookup dict mask (assembly tables field)
    let end_ := image out (H*chunks G M) e m
    (program tables field dict mask out H G M w).Exec m end_ (4+H*chunks G M*(2*e.work+4)) ∧
    (∀h : Fin H,∀g : Fin G,∀hm : 0<M,digit s.inputBits (lane g hm).val
      ((end_ (out+(row H G M (position h g hm)).val)).val)=(encodeInput (inputs s B key (u h g) (fun _=>0))).val) ∧
    (∀a<out,end_ a=m a) ∧ CheapCode (program tables field dict mask out H G M w) := by
  let e := lookup dict mask (assembly tables field)
  let end_ := image out (H*chunks G M) e m
  let f := descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key
  let x := fun h g=>encodePanel (u h g)
  have fitE : e.Fits w out := by simp [e,lookup,Expr.Fits,df,mf,assembly,fits tables field out bounds]
  have rows := assembled tables field out bounds u m static source
  refine ⟨scan_exec _ _ e m fitE wide,?_,fun _ h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h),@scan_cheap _ _ _ _⟩
  intro h g hm
  let t := position h g hm
  let i := row H G M t
  have form : end_ (out+i.val)=((masked f x t:ℕ):Word w) :=
    (ProtocolRAMGeneratedWrite.read_image out (H*chunks G M) e m i).trans
      (eval_word tables field out s B key dict mask u m bounds static source df mf bits span wide size fixed maskWord t)
  have short : masked f x t<2^w := by
    have n := min_le_left M (G-t.2.val*M)
    exact (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_left s.inputBits n).trans size))
  have loc : t.2.val*M+(lane g hm).val=g.val := Nat.div_add_mod' ..
  have got := active_read f x t (lane g hm) (loc.trans_lt g.isLt)
  have named : (⟨t.2.val*M+(lane g hm).val,loc.trans_lt g.isLt⟩ : Fin G)=g := Fin.ext loc
  rw [named] at got
  change digit s.inputBits _ ((end_ (out+i.val)).val)=_
  rw [form,Fin.val_cast_of_lt short]
  simpa only [f,x,t,position,descriptor,decode_encode_panel] using got


end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
