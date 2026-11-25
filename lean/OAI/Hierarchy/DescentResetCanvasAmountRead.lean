import OAI.Hierarchy.DescentResetCanvasAmount

namespace OAI
namespace Hierarchy.DescentResetCanvasAmount.Layout
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (s : DescentResetCanvasAmount.Layout)
variable (hub : Fin s.hosts→Cell 1) (history : Fin s.blocks→Fin s.hosts→Fin s.groups→Cell s.oldBits)
    (signed : s.Slot→Fin s.hosts→Fin s.groups→Cell s.wireBits)

def gated (p : s.Slot) (h : Fin s.hosts) (g : Fin s.groups) :=
  if (hub h).val=0 then (0:Cell s.wireBits) else signed p h g

def operand : (j:s.Key)→Fin s.hosts→Fin s.groups→Cell (s.field j)
  | .inl x=>history x
  | .inr (p,i)=>if i=0 then signed p else s.gated hub signed p

def fee (x : Fin s.blocks) (h : Fin s.hosts) (g : Fin s.groups) :=
  s.hist*(history x h g).val + s.unitFee*(if (hub h).val=0 then 1 else 256)*
    (∑j,s.alive (signed (x,j) h g))

theorem alive_eq (z : Cell s.wireBits) :
    s.alive z=(if DescentSignedCableCodec.census (D:=s.degree) (cap:=s.cap) z=0 then 0 else 1) := by
  have empty : DescentSignedCableCodec.census (D:=s.degree) (cap:=s.cap) 0=0 := by
    rw [← DescentSignedCableCodec.empty,DescentSignedCableCodec.census_at]
    rfl
  by_cases hz:z=0
  · subst z
    simp [alive]; exact empty
  · simp [alive,hz]

theorem key_sum (h : Fin s.hosts) (g : Fin s.groups) :
    (∑j:Fin s.number,s.contribution (s.order.symm j) (s.operand hub history signed (s.order.symm j) h g))=
    ∑x,s.fee hub history signed x h g*(2^s.bits)^x.val := by
  let term := fun j:s.Key=>s.contribution j (s.operand hub history signed j h g)
  change (∑j,term (s.order.symm j))=_
  rw [s.order.symm.sum_comp term,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Fintype.sum_prod_type,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [term,contribution,operand,fee]
  by_cases off : (hub h).val=0
  · simp [gated,off,alive,Finset.sum_mul,Finset.mul_sum,add_mul,mul_assoc]
  · have second : (1:Fin 2)≠0:=by decide
    simp only [off,ite_false,ite_true,second,Nat.mul_one,Finset.mul_sum,Finset.sum_mul,add_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [gated,off]; ring

private theorem source_key {base w : ℕ} (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank)
    (m : Memory w) (hf : hubs.Fits w base) (hc : s.hosts≤hubs.size)
    (hr : ∀h,m (hubs.base+h.val)=((hub h).val:Word w))
    (af : ∀x,(atom x).Fits w base) (ac : ∀x,s.rows≤(atom x).size)
    (ar : ∀x,Reads (atom x) (history x) s.lanes m)
    (wf : ∀p,(wire p).Fits w base) (wc : ∀p,s.rows≤(wire p).size)
    (wr : ∀p,Reads (wire p) (signed p) s.lanes m) (space : s.endAddress base<2^w) (j : s.Key) :
    Source (s.input base hubs atom wire j) (s.operand hub history signed j) s.lanes ((s.directory base w).image m) := by
  let post:=(s.directory base w).image m
  obtain ⟨idFits,_,idSize⟩:=s.bounds space
  have idsCap : s.rows≤(s.ids base).size:=idSize
  have lower (a:ℕ) (ha:a<base) : post a=m a := DescentStaticWordColumn.frame base s.rows s.hostId m a (.inl ha)
  have staged {b : ℕ} (B : Bank) (x : Fin s.hosts→Fin s.groups→Cell b)
      (fit : B.Fits w base) (size : s.rows≤B.size) (read : Reads B x s.lanes m) :
      Source (.lookup B .row) x s.lanes post := by
    apply source_column B base fit post x size
    intro p
    exact (lower _ ((Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le size) _).trans_le fit.2.2)).trans (read p)
  cases j with
  | inl x=>exact staged _ _ (af x) (ac x) (ar x)
  | inr pair=>
    rcases pair with ⟨p,i⟩
    have raw:=staged _ _ (wf p) (wc p) (wr p)
    by_cases normal:i=0
    · simpa [input,operand,normal,field,post] using raw
    simp only [input,operand,normal,ite_false,field,Sum.elim_inr]
    intro row_
    let a:=row s.hosts s.groups s.lanes row_
    have idRead : post ((s.ids base).base+a.val)=(row_.1.val:Word w) := by
      change DescentStaticWordColumn.image base _ m _ (base+a.val)=_
      have present : a.val<s.rows:=a.isLt
      rw [DescentStaticWordColumn.read base s.rows s.hostId m present]
      simp only [hostId,dite_eq_left present]
      change (((row s.hosts s.groups s.lanes).symm ((row s.hosts s.groups s.lanes) row_)).1.val:Word w)=_
      rw [Equiv.symm_apply_apply]
    have hostRead := (lower (hubs.base+row_.1.val)
      ((Nat.add_lt_add_left (row_.1.isLt.trans_le hc) _).trans_le hf.2.2)).trans (hr row_.1)
    have oneFits : 1<2^w := by
      have positive:=Nat.two_pow_pos (Nat.clog 2 s.rows)
      have top:=(s.bounds space).1.2.1
      change 2^Nat.clog 2 s.rows<2^w at top
      omega
    have isSmall : (hub row_.1).val<2^w := (hub row_.1).isLt.trans_le (by omega)
    change (s.recorded hubs base (.lookup (wire p) .row)).eval post (a.val:Word w)=_
    simp only [recorded,Expr.eval,bank_read (s.ids base) post (a.isLt.trans_le idsCap) idFits,idRead,
      bank_read hubs post (row_.1.isLt.trans_le hc) hf,hostRead]
    by_cases off:(hub row_.1).val=0
    · have blank : data (s.gated hub signed p) row_=0 := by
        apply Fin.ext
        change (finFunctionFinEquiv (fun j:Fin s.lanes => if live : row_.2.val*s.lanes+j.val<s.groups
          then s.gated hub signed p row_.1 ⟨_,live⟩ else 0)).val=0
        rw [finFunctionFinEquiv_apply]
        apply Finset.sum_eq_zero
        intro j _
        split <;> simp [gated,off]
      simp [off,DescriptorExpr.Comparison.test,blank]
    · have nz : (((hub row_.1).val:ℕ):Word w)≠0 := by
        intro eqn
        exact off (by simpa only [Fin.val_cast_of_lt isSmall,Fin.val_zero] using congrArg Fin.val eqn)
      have selected := raw row_
      simpa [DescriptorExpr.Comparison.test,nz,off,gated,data,a,Expr.eval,field] using selected

theorem issued {w : ℕ} (base : ℕ) (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank)
    (m : Memory w) (hf : hubs.Fits w base) (hc : s.hosts≤hubs.size)
    (hr : ∀h,m (hubs.base+h.val)=((hub h).val:Word w))
    (af : ∀x,(atom x).Fits w base) (ac : ∀x,s.rows≤(atom x).size)
    (ar : ∀x,Reads (atom x) (history x) s.lanes m)
    (wf : ∀p,(wire p).Fits w base) (wc : ∀p,s.rows≤(wire p).size)
    (wr : ∀p,Reads (wire p) (signed p) s.lanes m)
    (y : Fin s.blocks→Fin s.hosts→Fin s.groups→Cell s.bits)
    (value : ∀x h g,s.fee hub history signed x h g=(y x h g).val)
    (space : s.endAddress base<2^w) :
    Reads (s.amount base) (fun h g=>encode s.bits s.blocks (fun x=>y x h g)) s.lanes
      ((s.phase base w hubs atom wire).image m) := by
  let vals := fun j=>s.operand hub history signed (s.order.symm j)
  have atZero (j : s.Key) : s.contribution j 0=0 := by
    rcases j with x|⟨p,i⟩
    · change s.hist*0*(2^s.bits)^x.val=0
      simp
    · change s.unitFee*(if i=0 then 1 else 255)*s.alive (0:Cell s.wireBits)*(2^s.bits)^p.1.val=0
      simp [alive]
  have zero (j : Fin s.number) : s.contribution (s.order.symm j) 0=0 :=atZero _
  have eqn (h : Fin s.hosts) (g : Fin s.groups) :
      (∑j,s.contribution (s.order.symm j) (vals j h g))=
      (encode s.bits s.blocks (fun x=>y x h g)).val := by
    calc
      _ = ∑x,s.fee hub history signed x h g*(2^s.bits)^x.val := s.key_sum hub history signed h g
      _ = ∑x,(y x h g).val*(2^s.bits)^x.val := by simp only [value]
      _ = _ := (finFunctionFinEquiv_apply (fun x=>y x h g)).symm
  exact (DescentPackedColumnSum.run (s.table base) (s.amount base).base s.unitBits s.lanes
    (s.bits*s.blocks) s.hosts s.groups (s.field ∘ s.order.symm) (fun j=>s.contribution (s.order.symm j))
    (s.input base hubs atom wire ∘ s.order.symm) vals _ ((s.directory base w).image m) zero eqn
    (fun _=>s.small _) (fun _=>s.input_fits hf af wf space _) (fun j=>s.source_key hub history signed
      hubs atom wire m hf hc hr af ac ar wf wc wr space _) le_rfl ((s.positions base).2.2.trans_lt space)).2.1


end
end Hierarchy.DescentResetCanvasAmount.Layout

end OAI
