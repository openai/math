import OAI.Hierarchy.DescentResetSourceTicketBank
import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # Six shared pages join measured parent metadata to its compact original word -/
namespace Hierarchy.DescentResetSourceTicketPair
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open DescentResetSignedScan DescentResetFieldAssembler ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing
noncomputable section
variable {a b M w base X K H G : ℕ}

def quad (m : Meta) (ord : Cell b) : Fin 4→Cell b :=
  ![(m.src:Cell b),(m.dst:Cell b),ord,((if m.live then m.units else 0:ℕ):Cell b)]

def fields (ms : Fin K→Meta) (ord : Fin K→Cell b) (i : Fin (K*4)) : Cell b :=
  let t:=finProdFinEquiv.symm i;quad (ms t.1) (ord t.1) t.2

theorem component (ms : Fin K→Meta) (ord : Fin K→Cell b) (j : Fin K) (i : Fin 4) :
    DescentResetSourceTicketRAM.field (fields ms ord) j i=(quad (ms j) (ord j) i).val:=by
  simp only [DescentResetSourceTicketRAM.field,fields,Equiv.symm_apply_apply]

def parent (r : Fin 3) (q : Fin 4→Cell b) : Option Parent :=
  if (q 3).val=0 then none else
  if r=0 then some ⟨(q 0).val,0,(q 2).val,0⟩ else
  if r=1 then some ⟨(q 0).val,0,(q 2).val,(q 3).val⟩ else
  if (q 0).val=(q 1).val then none else some ⟨(q 1).val,0,(q 2).val,(q 3).val⟩

def emit (a b : ℕ) (r : Fin 3) (m : Cell (a*7)) (ord : Cell b) :=
  encode b 5 (literal b (parent r (quad (decode a m) ord)))

theorem live_parent (ms : Fin K→Meta) (ord : Fin K→Cell b) (j : Fin K) :
    parent 0 (quad (ms j) (ord j))=DescentResetSourceTicketCompare.asked (fields ms ord) j ∧
    parent 1 (quad (ms j) (ord j))=DescentResetSourceTicketCompare.located (fields ms ord) j false ∧
    parent 2 (quad (ms j) (ord j))=DescentResetSourceTicketCompare.located (fields ms ord) j true := by
  simp [parent,DescentResetSourceTicketCompare.asked,DescentResetSourceTicketCompare.located,
    DescentResetSourceTicketRAM.query,DescentResetSourceTicketRAM.face,component]

theorem emit_blank (a b : ℕ) (r : Fin 3) : emit a b r 0 0=0:=by
  have zero : (encode a 7).symm 0=fun _=>0:=by
    apply (encode a 7).injective;rw [Equiv.apply_symm_apply];exact (DescentPacking.PackedMatch.Local.Gather.encode_zero a 7).symm
  simpa [emit,decode,zero,quad,parent,literal] using DescentPacking.PackedMatch.Local.Gather.encode_zero b 5

def width (a b M : ℕ) := (a*7+b)*M
def endAt (base a b M : ℕ) := base+6*2^(width a b M)
def idPair : Fin 3×Fin 2 ≃ Fin 6 := finProdFinEquiv
def pages (a b M : ℕ) (i : Fin 6) : Page :=
  let p:=idPair.symm i;binary (emit a b p.1) M p.2
def table (base a b M : ℕ) (r : Fin 3) := joined (pages a b M) (width a b M) base (fun j=>idPair (r,j))
def expression (base a b M : ℕ) (r : Fin 3) («meta» code : Expr) := (table base a b M r).read «meta» code
def queries (base a b M : ℕ) (me op : Fin X→Fin K→Expr) (x : Fin X) (j : Fin K) :=
  expression base a b M 0 (me x j) (op x j)
def items (base a b M : ℕ) (me op : Fin X→Fin K→Expr) (x : Fin X) : Fin (K+K)→Expr :=
  Fin.addCases (fun j=>expression base a b M 1 (me x j) (op x j))
    (fun j=>expression base a b M 2 (me x j) (op x j))

private theorem page_read (a b M : ℕ) (r : Fin 3) (z : Fin 2) : pages a b M (idPair (r,z))=binary (emit a b r) M z:=by simp [pages]
private theorem page_fit (a b M : ℕ) (i : Fin 6) : ((pages a b M) i).bits≤width a b M:=by
  obtain ⟨⟨r,z⟩,rfl⟩:=idPair.surjective i
  rw [page_read]
  fin_cases z
  · exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  · rfl

theorem fits (ms os : Fin X→Fin K→Expr) (mf : ∀x j,(ms x j).Fits w base)
    (ofit : ∀x j,(os x j).Fits w base) (room : endAt base a b M<2^w) :
    (∀x j,(queries base a b M ms os x j).Fits w (endAt base a b M)) ∧
    ∀x i,(items base a b M ms os x i).Fits w (endAt base a b M) := by
  have early : base≤endAt base a b M:=Nat.le_add_right ..
  have fit (r : Fin 3) (x : Fin X) (j : Fin K) :
      (expression base a b M r (ms x j) (os x j)).Fits w (endAt base a b M):=by
    exact ⟨bank_room _ _ _ _ _ (page_fit a b M _) le_rfl room,
      ProtocolRAMGeneratedWrite.fits_mono _ early (ofit x j),bank_room _ _ _ _ _ (page_fit a b M _) le_rfl room,
      ProtocolRAMGeneratedWrite.fits_mono _ early (mf x j)⟩
  refine ⟨fit 0,?_⟩
  intro x i
  refine Fin.addCases ?_ ?_ i
  · intro j;simpa only [items,Fin.addCases_left] using fit 1 x j
  · intro j;simpa only [items,Fin.addCases_right] using fit 2 x j

theorem any (base a b M w : ℕ) (m : Memory w) (room : endAt base a b M<2^w) :
    let p:=pages a b M;let program:=mount p (width a b M) w base;let dst:=after p (width a b M) base m
    program.Exec m dst (4+10*(6*2^width a b M)) ∧ CheapCode program ∧
    DescentStaticWordColumn.names program=15*(6*2^width a b M+1) ∧
    ∀z,z<base ∨ endAt base a b M≤z→dst z=m z := by
  intro p prog dst
  have hold:=DescentOrdinaryAtomFieldRAM.ROM.run p (width a b M) base m room
  exact ⟨hold.1,cheap p _ _ _,hold.2,DescentOrdinaryAtomFieldRAM.ROM.frame p _ _ _⟩

theorem sources (ms os : Fin X→Fin K→Expr) (mv : Fin X→Fin H→Fin G→Fin K→Meta)
    (ov : Fin X→Fin H→Fin G→Fin K→Cell b) (m : Memory w)
    (mf : ∀x j,(ms x j).Fits w base) (ofit : ∀x j,(os x j).Fits w base)
    (room : endAt base a b M<2^w) (small : ∀x h g j i,digits (mv x h g j) i<2^a)
    («meta» : ∀x j,Source (ms x j) (fun h g=>raw a (mv x h g j)) M m)
    (word : ∀x j,Source (os x j) (fun h g=>ov x h g j) M m) :
    DescentResetSourceTicketBank.Sources (queries base a b M ms os) (items base a b M ms os)
      (fun x h g=>fields (mv x h g) (ov x h g)) M (after (pages a b M) (width a b M) base m) := by
  let dst:=after (pages a b M) (width a b M) base m
  have frame:=DescentOrdinaryAtomFieldRAM.ROM.frame (pages a b M) (width a b M) base m
  have early : base≤endAt base a b M:=Nat.le_add_right ..
  have held {d : ℕ} (e : Expr) (v : Fin H→Fin G→Cell d) (fit : e.Fits w base) (source : Source e v M m) :
      Source e v M dst:=fun i=>(ProtocolRAM.eval_below e _ m dst fit (fun z hz=>frame z (.inl hz))).trans (source i)
  have one (r : Fin 3) (x : Fin X) (j : Fin K) :
      Source (expression base a b M r (ms x j) (os x j))
        (fun h g=>encode b 5 (literal b (parent r (quad (mv x h g j) (ov x h g j))))) M dst:=by
    have fit : DescentPackedZip.Fits (table base a b M r) (ms x j) (os x j) (a*7) b M (endAt base a b M) w:=
      ⟨ProtocolRAMGeneratedWrite.fits_mono _ early (mf x j),ProtocolRAMGeneratedWrite.fits_mono _ early (ofit x j),
      bank_room _ _ _ _ _ (page_fit a b M _) le_rfl room,bank_room _ _ _ _ _ (page_fit a b M _) le_rfl room,
      by simp [table,joined,bank,page_read,binary],by simp [table,joined,bank,page_read,binary]⟩
    have st:=binary_mounted (emit a b r) M (pages a b M) (width a b M) base m (page_fit a b M)
      (fun i=>idPair (r,i)) (page_read a b M r)
    have genuine:=read_data (table base a b M r) (ms x j) (os x j) _ fit (emit a b r) (emit_blank a b r)
      dst st _ _ (held _ _ (mf x j) («meta» x j)) (held _ _ (ofit x j) (word x j))
    have dec (h₀ : Fin H) (g₀ : Fin G) : decode a (raw a (mv x h₀ g₀ j))=mv x h₀ g₀ j:=
      decode_raw _ (small x h₀ g₀ j)
    simpa only [expression,emit,dec] using genuine
  constructor
  · intro x j;simpa only [queries,dst,(live_parent _ _ _).1] using one 0 x j
  · intro x i
    refine Fin.addCases ?_ ?_ i
    · intro j;simpa only [items,dst,Fin.addCases_left,DescentResetSourceTicketCompare.operands,(live_parent _ _ _).2.1] using one 1 x j
    · intro j;simpa only [items,dst,Fin.addCases_right,DescentResetSourceTicketCompare.operands,(live_parent _ _ _).2.2] using one 2 x j

theorem work (base a b M : ℕ) (r : Fin 3) (m o : Expr) :
    (expression base a b M r m o).work=o.work+(m.work+5)+1+5:=rfl

end
end Hierarchy.DescentResetSourceTicketPair

end OAI
