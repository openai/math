import OAI.Hierarchy.DescentIssuedGoodHeaders
import OAI.Hierarchy.DescentSignedCableCodec
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Reading a measured payload at the other end of the same previous grain -/
namespace Hierarchy.DescentResetOppositePayload
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open DescentIssuedGoodHeaders DescentPackedZip DescentPackedColony DescentSharedCableNames.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

abbrev Slot (D cap : ℕ) := Fin D × Fin (2*cap)

def «matches» {D cap : ℕ} (wanted : Live D cap) (remote : Fin D) (chip : Option (Live D cap)) : Prop :=
  remote=wanted.neighbor ∧ ∃x,chip=some x ∧ x.target=false ∧ x.sourceWire=wanted.sourceWire ∧ x.within=wanted.within

def select {D cap b : ℕ} (query : Option (Live D cap)) (send : Slot D cap→Option (Live D cap)) (data : Slot D cap→Cell b) : Cell b :=
  match query with
  | none=>0
  | some q=>if q.target then
      if has : ∃s : Slot D cap,«matches» q s.1 (send s) then data has.choose else 0
    else 0

theorem selected {D cap b : ℕ} (q : Live D cap) (send : Slot D cap→Option (Live D cap)) (data : Slot D cap→Cell b)
    (target_ : q.target=true) (s : Slot D cap) (found : «matches» q s.1 (send s)) (only : ∀u,«matches» q u.1 (send u)→u=s) :
    select (some q) send data=data s:=by
  have some_ : ∃s : Slot D cap,«matches» q s.1 (send s):=⟨s,found⟩
  simp only [select,target_,ite_true,dite_eq_left some_,only _ some_.choose_spec]

/-- A single recipient chip, followed by the donor chip and its measured
payload at every signed position behind every possible old neighbor. -/
def index (D cap : ℕ) : Fin 1 ⊕ (Slot D cap×Fin 2) ≃ Fin (1+(D*(2*cap))*2) :=
  ((Equiv.refl _).sumCongr ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv)).trans finSumFinEquiv

def inputs {D cap b : ℕ} (q : Cell b) (cable pay : Slot D cap→Cell b) (i : Fin (1+(D*(2*cap))*2)) : Cell b :=
  match (index D cap).symm i with
  | .inl _=>q
  | .inr (j,s)=>if s.val=0 then cable j else pay j

def chip {b : ℕ} (D cap : ℕ) (v : Cell b) :=DescentSignedCableCodec.decode D cap (v.val:Cell (DescentSignedCableCodec.width D cap))

def kernel (D cap b : ℕ) (v : Fin (1+(D*(2*cap))*2)→Cell b) : Cell b :=
  select (chip D cap (v (index D cap (.inl 0))))
    (fun j=>chip D cap (v (index D cap (.inr (j,0))))) (fun j=>v (index D cap (.inr (j,1))))

theorem kernel_at {D cap b : ℕ} (q : Cell b) (cable pay : Slot D cap→Cell b) :
    kernel D cap b (inputs q cable pay)=select (chip D cap q) (fun j=>chip D cap (cable j)) pay:=by
  simp [kernel,inputs]

theorem chip_at {D cap b : ℕ} (row : Option (Live D cap)) (v : Cell b)
    (saved : v.val=(DescentSignedCableCodec.encode row).val) : chip D cap v=row:=by
  simp [chip,saved,DescentSignedCableCodec.decode_encode]

variable {D cap b H G M w : ℕ}
local notation "K"=>1+(D*(2*cap))*2

/-- Every candidate in the lookup has moved from the corresponding real old
neighbor bank. The original old port roster is shared across all group lanes. -/
theorem received (P : Ports D) (roster : Fin H→Fin D→Option (Fin H)) (cable pay : Fin (2*cap)→Bank)
    (query : Expr) (q : Fin H→Fin G→Cell b) (signed cargo : Fin (2*cap)→Fin H→Fin G→Cell b)
    (tables : Fin K→Tables) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (pos : 0<M) (mem : Memory w) (mounted : Mounted P roster mem G M)
    (src : Source query q M mem) (previous : ∀j,Reads (cable j) (signed j) M mem ∧ Reads (pay j) (cargo j) M mem)
    (ports : ∀j,Accessible P (cable j) H G M w mid ∧ Accessible P (pay j) H G M w mid)
    (fits : query.Fits w mid)
    (constants : ∀j,Static (tables j) (setField (d:=b) j) M mem)
    (tablesRoom : ∀j,(tables j).shift.Fits w mid ∧ (tables j).apply.Fits w mid ∧
      (tables j).shift.bits=b*K*M ∧ (tables j).apply.bits=(b*K+b)*M)
    (room : mid+H*chunks G M<2^w) (fit : DescentSIMDLookup.Fits menu (b*K) b M H G w out.base)
    (rom : resident (kernel D cap b ∘ (encode b K).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((b*K)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let reads : Fin K→Expr:=fun i=>match (index D cap).symm i with
      | .inl _=>query
      | .inr (j,s)=>peerExpr P (if s.val=0 then cable j.2 else pay j.2) H j.1
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀p : Row H G M,dst (out.base+(row H G M p).val)=((data (fun h g=>
      select (chip D cap (q h g)) (fun j=>chip D cap ((roster h j.1).elim 0 (fun v=>signed j.2 v g)))
        (fun j=>(roster h j.1).elim 0 (fun v=>cargo j.2 v g))) p).val:Word w)) ∧
    ∀a,(a< mid ∨ mid+rows≤a)→(a<out.base ∨ out.base+rows≤a)→dst a=mem a:=by
  intro reads act rows dst
  let value:=fun (h : Fin H) (g : Fin G)=>inputs (D:=D) (cap:=cap) (q h g)
    (fun j=>(roster h j.1).elim 0 (fun v=>signed j.2 v g)) (fun j=>(roster h j.1).elim 0 (fun v=>cargo j.2 v g))
  have safe (j : Fin K) : (reads j).Fits w mid:=by
    obtain ⟨s,rfl⟩:=(index D cap).surjective j
    rcases s with x|⟨⟨peer,i⟩,tag⟩
    · simpa only [reads,Equiv.symm_apply_apply] using fits
    · fin_cases tag
      · simpa [reads] using peer_fits P (cable i) mid (ports i).1 peer
      · simpa [reads] using peer_fits P (pay i) mid (ports i).2 peer
  have bound : Bounds (w:=w) (d:=b) (M:=M) tables reads mid:=fun j=>⟨safe j,tablesRoom j⟩
  have use (j : Fin K) : Source (reads j) (fun h g=>value h g j) M mem:=by
    obtain ⟨s,rfl⟩:=(index D cap).surjective j
    rcases s with x|⟨⟨peer,i⟩,tag⟩
    · simpa only [reads,value,inputs,Equiv.symm_apply_apply] using src
    · fin_cases tag
      · simpa [reads,value,inputs] using peerSource P (cable i) mid (ports i).1 roster mem mounted (signed i) (previous i).1 peer
      · simpa [reads,value,inputs] using peerSource P (pay i) mid (ports i).2 roster mem mounted (cargo i) (previous i).2 peer
  obtain ⟨run,whole,_,frame⟩:=gathered_words (kernel D cap b) tables reads menu mid out.base value pos mem bound constants use room fit rom dictLow maskLow wire
  exact ⟨run,fun p=>by simpa only [value,kernel_at] using whole p,frame⟩

end
end Hierarchy.DescentResetOppositePayload

end OAI
