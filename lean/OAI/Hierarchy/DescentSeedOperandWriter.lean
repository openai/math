import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentSeedOperandStamp
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! # Initial packed argument pages in the physical order read by the first reached date -/
namespace Hierarchy.DescentOperandStateBanks.Seed.Physical
open DescentPackedSeed DescentInitialHost DescentSeedRoot DescentColonies DescentSIMDLookup
open DescentDyadicSpan DescentPackedColony DescentOperandStateBanks.Seed.Columns
open Computability.BorderVNP.Crossing ThreeFlat Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F J : Type} [_root_.Field F] [Fintype J] [DecidableEq J] {k n G d R w H M s : ℕ}
  (X : Approximation F k n) (host : Vertex X↪Fin H) (name : J≃Fin G) (digits : Fin R≃J×Block d)

def site (N nodes : ℕ) (j : ℕ) (h : Fin H) : Option (Vertex X×(Fin 3×Fin N)) :=
  if hit:j<3*N ∧ 0<nodes then (DescentSeedInitialTable.rack X host h).map
    (fun v=>(v,finProdFinEquiv.symm ⟨j,hit.1⟩)) else none

def fixed (N nodes : ℕ) (j : ℕ) (f : Field) (h : Fin H) : Bool×ℕ :=
  (site X host N nodes j h).elim (false,0) fun p=>
    (varies X p.1 p.2.1 f,scalar X p.1 p.2.1 p.2.2.val 0 f)

def value (N b nodes : ℕ) (j : ℕ) (f : Field) (x : Block d) (h : Fin H) (g : Fin G) : Cell (b*nodes) :=
  (site X host N nodes j h).elim 0 fun p=>
    (scalar X p.1 p.2.1 p.2.2.val (digits.symm (name.symm g,x)).val f : Cell (b*nodes))

omit [_root_.Field F] [Fintype J] [DecidableEq J] in
theorem fixed_value (N b nodes : ℕ) (j : ℕ) (f : Field) (x : Block d) (h : Fin H) (g : Fin G) :
    (if (fixed X host N nodes j f h).1 then CopyOrdinal.field (b:=b*nodes) name digits x g
      else ((fixed X host N nodes j f h).2:Cell (b*nodes)))=value X host name digits N b nodes j f x h g := by
  unfold fixed value
  cases e:site X host N nodes j h with
  | none=>rfl
  | some p=>
    let copy := (digits.symm (name.symm g,x)).val
    change (if varies X p.1 p.2.1 f then (copy : Cell (b*nodes))
      else (scalar X p.1 p.2.1 p.2.2.val 0 f : Cell (b*nodes))) =
      (scalar X p.1 p.2.1 p.2.2.val copy f : Cell (b*nodes))
    rw [Columns.split X p.1 p.2.1 p.2.2.val copy f]
    cases varies X p.1 p.2.1 f <;> rfl

def offsetSource (d G M copy masks : ℕ) (x : Block d) (vary : Bool) (v : Cell s) : Expr :=
  let rows:=CopyOrdinal.words d G M
  let index:Expr:=.op .add (.lit (x.val*chunks G M)) .row
  if vary then .lookup (column copy rows 0) index else
    .op .mask (.lit (DescentSeedSignedBroadcast.wide M v).val) (.lookup (column masks rows 0) index)

theorem eval_offset (copy mask : ℕ) (x : Block d) (vary : Bool) (v : Cell s)
    (m : Memory w) (j : Fin (chunks G M)) :
    (offsetSource d G M copy mask x vary v).eval m (j.val:Word w)=
      (sources d G M copy mask vary v).eval m ((row (2^d) G M (x,j)).val:Word w) := by
  have idx:(x.val*chunks G M+j.val)=(row (2^d) G M (x,j)).val := by
    simp [row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have word : ((x.val*chunks G M:ℕ):Word w)+(j.val:Word w)=((row _ G M (x,j)).val:Word w):=by
    rw [←Nat.cast_add,idx]
  cases vary <;> simp only [offsetSource,sources,wordAt,Bool.false_eq_true,ite_false,ite_true,Expr.eval,RowOp.opcode,BinaryOp.eval,word]

def order (slots d H : ℕ) : ((Pages slots×Block d)×Fin H) ≃ Fin ((7*slots*2^d)*H) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def item (base N slots nodes b d M : ℕ) (i : ℕ) : Expr :=
  if hit:i<7*slots*2^d*H then
    let j:=(order slots d H).symm ⟨i,hit⟩
    let key:=(finProdFinEquiv.symm j.1.1 : Field×Fin slots)
    let v:=fixed X host N nodes key.2.val key.1 j.2
    let copy:=stampStart X base
    offsetSource d G M copy (maskBase copy d G M) j.1.2 v.1 (v.2:Cell (b*nodes))
  else .lit 0

def sweep (base N slots nodes b d G M : ℕ) :=
  let copy:=stampStart X base
  DescentPackedFlowBatch.passes (first copy d G M) (chunks G M) (chunks G M)
    (item (G:=G) X host base N slots nodes b d M) 0 (7*slots*2^d*H)


def program (w base N slots nodes b M : ℕ) :=
  let copy:=stampStart X base
  let rows:=CopyOrdinal.words d G M
  (stampProgram X name digits w base M (b*nodes)).seq
    ((DescentStaticWordColumn.program w (maskBase copy d G M) (maskValue d G M (b*nodes)) rows).seq
      (ProtocolRAM.program w (sweep X host base N slots nodes b d G M)))

def memory (base N slots nodes b M : ℕ) (m : Memory w) :=
  let copy:=stampStart X base
  result (sweep X host base N slots nodes b d G M)
    (DescentStaticWordColumn.image (maskBase copy d G M) (maskValue d G M (b*nodes))
      (stampImage X name digits base M (b*nodes) m) (CopyOrdinal.words d G M))

def ticks (base N slots nodes b d G M : ℕ) :=
  let r:=CopyOrdinal.words d G M
  (4+10*Signed.size X+(4+10*count X)+(4+10*r))+
    (4+10*r+clock (sweep X host base N slots nodes b d G M))

omit [_root_.Field F] in
private theorem item_work (base N slots nodes b d G M i : ℕ) :
    (item (G:=G) X host base N slots nodes b d M i).work≤15 := by
  have bounded (copy masks : ℕ) (x : Block d) (vary : Bool) (v : Cell (b*nodes)) :
      (offsetSource d G M copy masks x vary v).work ≤ 15 := by
    cases vary <;> norm_num [offsetSource, Expr.work]
  unfold item
  split
  · exact bounded _ _ _ _ _
  · norm_num [Expr.work]

omit [Fintype J] [DecidableEq J] [_root_.Field F] in
theorem price (w base N slots nodes b M : ℕ) :
    let cpu:=program X host name digits w base N slots nodes b M
    let r:=CopyOrdinal.words d G M
    let jobs:=7*slots*2^d*H
    CheapCode cpu ∧ DescentStaticWordColumn.names cpu≤
      15*(Signed.size X+1)+15*(count X+1)+2*(15*(r+1))+15+jobs*71 ∧
      ticks X host base N slots nodes b d G M ≤
        (4+10*Signed.size X+(4+10*count X)+(4+10*r))+(4+10*r+(4+jobs*(4+34*chunks G M))) := by
  intro cpu r jobs
  let I:=CopyOrdinal.shelf name digits w (stampStart X base) (b*nodes) M
  have len : I.length=r:=by simp [I,CopyOrdinal.shelf,DescentPackedColony.Phase.Arena.Image.length,r]
  have limit:=item_work X host base N slots nodes b d G M
  refine ⟨cheap_seq (cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _)) I.hardware.1)
      (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)),?_,?_⟩
  · have prog : DescentStaticWordColumn.names
        (ProtocolRAM.program w (sweep X host base N slots nodes b d G M)) ≤ 15 + jobs * 71 :=
      DescentPackedFlowBatch.program_bound (w:=w) (base:=bankStart X base d G M)
        (chunks G M) (chunks G M) 0 jobs _ 15 (fun j _ _=>limit j)
    unfold cpu program stampProgram issue
    simp only [DescentStaticWordColumn.names_seq,Signed.program_names,DescentStaticWordColumn.names_mount]
    change 15*(Signed.size X+1)+15*(count X+1)+DescentStaticWordColumn.names I.program+
      (15*(r+1)+DescentStaticWordColumn.names (ProtocolRAM.program w (sweep X host base N slots nodes b d G M)))≤_
    rw [I.hardware.2,len]
    omega
  · have fee:=DescentPackedFlowBatch.tariff (bankStart X base d G M) (chunks G M) (chunks G M) jobs _ 15
      (fun j _=>limit j)
    dsimp only [ticks,sweep]
    rw [Nat.mul_comm 34]
    exact Nat.add_le_add_left (Nat.add_le_add_left fee _) _


omit [Fintype J] [DecidableEq J] [_root_.Field F] in
/-- All old page and block projections, in exactly the physical order of
DatedPriorOperand.previousBank. The final dyadic read guard is left untouched. -/
theorem issued (base N slots nodes b M : ℕ) (m : Memory w) (wide : b*nodes*M≤w)
    (room : endAddress X base slots d H G M<2^w) :
    let l:DescentDatedPriorOperand.Layout:=⟨2^d,nodes,slots,H,G,M,b⟩
    let out:=bankStart X base d G M
    let done:=memory X host name digits base N slots nodes b M m
    (program X host name digits w base N slots nodes b M).Exec m done (ticks X host base N slots nodes b d G M) ∧
    (∀(f : Field) (a : Fin slots) (x : Block d) (p : Row H G M),
      done ((DescentDatedPriorOperand.previousBank l out x (page f a)).base+(row _ _ _ p).val)=
        ((DescentSIMDLookup.data (value X host name digits N b nodes a.val f x) p).val:Word w)) ∧
    ∀j, j<base ∨ endAddress X base slots d H G M≤j → done j=m j := by
  intro l out done
  let copy:=stampStart X base
  let rows:=CopyOrdinal.words d G M
  let r:=chunks G M
  let jobs:=7*slots*2^d*H
  let mask:=maskBase copy d G M
  let image₁:=stampImage X name digits base M (b*nodes) m
  let image₂:=DescentStaticWordColumn.image mask (maskValue d G M (b*nodes)) image₁ rows
  have before : base≤copy:=by dsimp [copy,stampStart];omega
  have copyEnd : copy+rows≤ mask:=Nat.add_le_add_left (span_ge _) _
  have maskEnd : mask+rows≤out:=Nat.add_le_add_left (span_ge _) _
  have tall : out+jobs*r≤endAddress X base slots d H G M:=by
    change out+7*slots*2^d*H*r≤out+(7*slots)*(2^d*(H*r))+_
    rw [Nat.mul_assoc (7*slots*2^d) H r,Nat.mul_assoc (7*slots) (2^d) (H*r)]
    exact Nat.le_add_right ..
  have top:=tall.trans_lt room
  have low : out<2^w:=(Nat.le_add_right ..).trans_lt top
  have cx : copy≤ mask:=(Nat.le_add_right ..).trans copyEnd
  have mx : mask≤out:=(Nat.le_add_right ..).trans maskEnd
  have started:=stamp_run (M:=M) (b:=b*nodes) X name digits base m (copyEnd.trans_lt (mx.trans_lt low))
  obtain ⟨_,_,copyAt,_⟩:=CopyOrdinal.issued (M:=M) (b:=b*nodes) name digits copy (Seed.image X base m)
    (copyEnd.trans_lt (mx.trans_lt low))
  have copyRead (p : Row (2^d) G M) : image₂ (copy+(row _ _ _ p).val)=
      ((DescentSIMDLookup.data (CopyOrdinal.field (b:=b*nodes) name digits) p).val:Word w) :=
    (DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left (row _ _ _ p).isLt _).trans_le copyEnd))).trans (copyAt p)
  have maskRead (p : Row (2^d) G M) : image₂ (mask+(row _ _ _ p).val)=(DescentSIMDLookup.maskWord (b*nodes) M G p.2.val:Word w) := by
    have read := DescentStaticWordColumn.read mask rows (maskValue d G M (b*nodes)) image₁
      (j:=(row (2^d) G M p).val) (row (2^d) G M p).isLt
    refine read.trans ?_
    have within : (row (2^d) G M p).val<CopyOrdinal.words d G M := (row (2^d) G M p).isLt
    unfold maskValue
    rw [dite_eq_left within]
    change (maskWord (b*nodes) M G (((row (2^d) G M).symm ((row (2^d) G M) p)).2.val):Word w)=_
    rw [Equiv.symm_apply_apply]
  have fits (start : ℕ) (ok : start+span rows≤out) : (column start rows 0).Fits w out := by
    change 0<span rows ∧ span rows<2^w ∧ start+0*rows+span rows≤out
    simp only [Nat.zero_mul,Nat.add_zero]
    exact ⟨span_pos _,(Nat.le_add_left ..).trans_lt (ok.trans_lt low),ok⟩
  have fc:=fits copy (show copy+span rows≤out from mx)
  have fm:=fits mask (show mask+span rows≤out from le_rfl)
  let op:=item (G:=G) X host base N slots nodes b d M
  have valid (j : ℕ) (hj : j<jobs) : (op j).Fits w out := by
    have live : j<7*slots*2^d*H := hj
    change (item (G:=G) X host base N slots nodes b d M j).Fits w out
    unfold item
    rw [dite_eq_left live]
    dsimp only [offsetSource]
    split
    · exact ⟨fc,trivial,trivial⟩
    · exact ⟨trivial,fm,trivial,trivial⟩
  obtain ⟨run,read,lowFrame⟩:=DescentPackedFlowBatch.execute out r r jobs op image₂ valid top le_rfl
  refine ⟨?_,?_,?_⟩
  · let printMask := DescentStaticWordColumn.program w mask (maskValue d G M (b*nodes)) rows
    let writes := ProtocolRAM.program w (DescentPackedFlowBatch.passes out r r op 0 jobs)
    have mounted : printMask.Exec image₁ image₂ (4+10*rows) :=
      DescentStaticWordColumn.mount mask rows (maskValue d G M (b*nodes)) image₁ (maskEnd.trans_lt low)
    have afterStamp : (printMask.seq writes).Exec image₁ done
        ((4+10*rows)+clock (DescentPackedFlowBatch.passes out r r op 0 jobs)) := by
      intro labels regs keys machine
      exact Procedure.Exec.then (A:=printMask) (B:=writes) (a:=image₁) (b:=image₂) (c:=done) mounted run machine
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=stampProgram X name digits w base M (b*nodes)) (B:=printMask.seq writes)
      (a:=m) (b:=image₁) (c:=done) started.1 afterStamp machine
  · intro f a x p
    let job:=order slots d H ((page f a,x),p.1)
    have actual:=read job p.2
    have idx : (DescentDatedPriorOperand.previousBank l out x (page f a)).base+(row H G M p).val=
        out+job.val*r+p.2.val := by
      have indexed : job.val=p.1.val+H*(x.val+2^d*(page f a).val) := by
        change (finProdFinEquiv (finProdFinEquiv (page f a,x),p.1)).val=_
        simp only [finProdFinEquiv_apply_val]
      rw [indexed]
      simp only [DescentDatedPriorOperand.previousBank,DescentDatedPriorOperand.Layout.rows,l,row,
        finProdFinEquiv_apply_val,r]
      ring
    rw [idx]
    change result (DescentPackedFlowBatch.passes out r r op 0 jobs) image₂ _=_
    refine actual.trans ?_
    let pair:=fixed X host N nodes a.val f p.1
    have instr : op job.val=offsetSource d G M copy mask x pair.1 (pair.2:Cell (b*nodes)) := by
      change item (G:=G) X host base N slots nodes b d M job.val=_
      have hit : (order slots d H).symm job=((page f a,x),p.1) :=
        (order slots d H).symm_apply_apply _
      unfold item
      rw [dite_eq_left job.isLt]
      simp only [hit,page,Equiv.symm_apply_apply,pair,copy,mask]
    rw [instr,eval_offset copy mask x pair.1 (pair.2:Cell (b*nodes)) image₂ p.2]
    have rowRoom : rows≤2^w := ((Nat.le_add_left ..).trans (copyEnd.trans mx)).trans low.le
    rw [eval_source name digits copy mask image₂ pair.1 (pair.2:Cell (b*nodes)) wide rowRoom copyRead maskRead (x,p.2)]
    apply congrArg (fun c : Cell ((b*nodes)*M) => (c.val : Word w))
    apply congrArg (encode (b*nodes) M)
    funext t
    dsimp only
    split
    · exact fixed_value X host name digits N b nodes a.val f x p.1 _
    · rfl
  · intro j hj
    have damage : j<out ∨ out+jobs*r≤j := hj.imp (fun h=>h.trans_le (before.trans (cx.trans mx))) (fun h=>tall.trans h)
    have clean : image₂ j=image₁ j := DescentStaticWordColumn.frame _ _ _ _ _
      (hj.imp (fun h=>h.trans_le (before.trans cx)) (fun h=>maskEnd.trans ((Nat.le_add_right ..).trans (tall.trans h))))
    have orig:=started.2 j (hj.imp id (fun h=>(copyEnd.trans mx).trans ((Nat.le_add_right ..).trans (tall.trans h))))
    rcases damage with lo|hi
    · exact (lowFrame j lo).trans (clean.trans orig)
    · exact (DescentPackedFlowBatch.above out r r op image₂ 0 jobs j le_rfl (by simpa using hi)).trans (clean.trans orig)

omit [_root_.Field F] [Fintype J] [DecidableEq J] in
theorem value_live (N nodes b : ℕ) (positive : 0<nodes) (_slots : ℕ) (x : Block d)
    (v : Vertex X) (leg : Fin 3) (chunk : Fin N) (j : Fin G) (f : Field) :
    value X host name digits N b nodes (finProdFinEquiv (leg,chunk)).val f x (host v) j=
      (scalar X v leg chunk.val (digits.symm (name.symm j,x)).val f:Cell (b*nodes)) := by
  let q : Fin (3*N) := finProdFinEquiv (leg,chunk)
  have atSite : site X host N nodes q.val (host v)=some (v,(leg,chunk)) := by
    unfold site
    rw [dite_eq_left ⟨q.isLt,positive⟩,DescentSeedInitialTable.rack_real]
    exact congrArg (fun a=>some (v,a)) (finProdFinEquiv.symm_apply_apply (leg,chunk))
  unfold value
  rw [atSite]
  rfl

omit [_root_.Field F] [Fintype J] [DecidableEq J] in
theorem value_ghost (N nodes b arg : ℕ) (f : Field) (x : Block d) (h : Fin H) (j : Fin G)
    (ghost : DescentSeedInitialTable.rack X host h=none ∨ 3*N≤arg ∨ nodes=0) :
    value X host name digits N b nodes arg f x h j=0 := by
  unfold value site
  split <;> try rfl
  rename_i hit
  rcases ghost with e|e|e
  · simp [e]
  · omega
  · omega

end
end Hierarchy.DescentOperandStateBanks.Seed.Physical

end OAI
