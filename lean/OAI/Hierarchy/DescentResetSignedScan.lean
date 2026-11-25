import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Streaming the true reset parent counts through two mounted short comparison pages -/
namespace Hierarchy.DescentResetSignedScan
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open DescentPackedSumWords DescentColonies.SplitRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing BigOperators
noncomputable section

/-- Each field is local to one receiver. Ticket is measured in its source's real
old signed shelf and class is the source cell's local ordinal. Flags mark
genuine positive rows, including self-loops, which are read only once. -/
structure Parent where
  peer : ℕ
  group : ℕ
  ticket : ℕ
  units : ℕ

def precedes (a b : Parent) : Prop := a.group<b.group ∨ a.group=b.group ∧ a.ticket<b.ticket

def contribution (samePeer : Bool) (query item : Option Parent) : ℕ :=
  match query,item with
  | some q,some a=>if precedes a q ∧ (samePeer=true→a.peer=q.peer) then a.units else 0
  | _,_=>0

/-- The five upstream lanes carry active, relative neighbor, source class,
native source ticket, and the raw width divided by the reset grain. -/
def unpack (b : ℕ) (word : Cell (b*5)) : Option Parent :=
  let f:=(encode b 5).symm word
  if (f 0).val=0 then none else some ⟨(f 1).val,(f 2).val,(f 3).val,(f 4).val⟩

def literal (b : ℕ) : Option Parent→Fin 5→Cell b
  | none=>fun _=>0
  | some a=>![1,(a.peer:Cell b),(a.group:Cell b),(a.ticket:Cell b),(a.units:Cell b)]

def Fits (b : ℕ) : Option Parent→Prop
  | none=>True
  | some a=>1<2^b ∧ a.peer<2^b ∧ a.group<2^b ∧ a.ticket<2^b ∧ a.units<2^b

theorem unpack_literal (b : ℕ) (a : Option Parent) (fits : Fits b a) :
    unpack b (encode b 5 (literal b a))=a := by
  cases a with
  | none=>simp [unpack,literal]
  | some a=>
    obtain ⟨pos,peer,group,ticket,units⟩:=fits
    simp [unpack,literal,Fin.val_natCast,Nat.mod_eq_of_lt peer,
      Nat.mod_eq_of_lt group,Nat.mod_eq_of_lt ticket,Nat.mod_eq_of_lt units,Nat.mod_eq_of_lt pos]

def kernel (b paid : ℕ) (peer : Bool) (q a : Cell (b*5)) : Cell paid :=
  ((contribution peer (unpack b q) (unpack b a):ℕ):Cell paid)

theorem blank (b paid : ℕ) (peer : Bool) : kernel b paid peer 0 0=0 := by
  have same:encode b 5 (literal b none)=0:=DescentPacking.PackedMatch.Local.Gather.encode_zero b 5
  have empty:=unpack_literal b none (by trivial)
  rw [same] at empty
  simp [kernel,empty,contribution]

variable {b paid M w base H G n : ℕ} (peer : Bool)
local notation "law" => kernel b paid peer
local notation "span" => ((b*5+b*5)*M)
local notation "pages" => binary law M
local notation "table" => joined pages span base id

def sumWord (q : Fin H→Fin G→Option Parent) (items : Fin n→Fin H→Fin G→Option Parent)
    (fits : ∀h g,(∑j,contribution peer (q h g) (items j h g))<2^paid) (h : Fin H) (g : Fin G) : Cell paid :=
  ⟨_,fits h g⟩

/-- Sum at one physical host/group word. Empty residents and ghost lanes
contribute exactly zero and the proven per-lane bound prevents cross-lane carries. -/
theorem packed_sum (q : Fin H→Fin G→Option Parent) (rows : Fin n→Fin H→Fin G→Option Parent)
    (fit : ∀h g,(∑j,contribution peer (q h g) (rows j h g))<2^paid) (r : Row H G M) :
    (∑j,(data (fun h g=>((contribution peer (q h g) (rows j h g):ℕ):Cell paid)) r).val)=
      (data (sumWord peer q rows fit) r).val := by
  simp_rw [lanes_val]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases live : r.2.val*M+i.val<G
  · simp only [dite_eq_left live,sumWord,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have on:=Finset.single_le_sum (fun i _=>Nat.zero_le (contribution peer (q r.1 ⟨_,live⟩) (rows i r.1 ⟨_,live⟩))) (Finset.mem_univ j)
    rw [Fin.val_cast_of_lt (on.trans_lt (fit _ _))]
  · simp [live]

theorem fresh (q : Expr) (a : Fin n→Expr) (out : Bank) (mem : Memory w)
    (query : Fin H→Fin G→Option Parent) (items : Fin n→Fin H→Fin G→Option Parent)
    (qFit : q.Fits w base) (aFit : ∀i,(a i).Fits w base)
    (qRoom : ∀h g,Fits b (query h g)) (aRoom : ∀i h g,Fits b (items i h g))
    (qSource : Source q (fun h g=>encode b 5 (literal b (query h g))) M mem)
    (aSource : ∀i,Source (a i) (fun h g=>encode b 5 (literal b (items i h g))) M mem)
    (bounded : ∀h g,(∑i,contribution peer (query h g) (items i h g))<2^paid)
    (apart : base+2*2^span≤out.base) (fits : out.base+H*chunks G M<2^w) :
    let op:=total (fun i=>DescentPackedZip.Tables.read table q (a i)) (List.finRange n)
    let N:=H*chunks G M
    let mounted:=after pages span base mem
    let done:=image out.base N op mounted
    let prog:=(mount pages span w base).seq (scan w out.base N op)
    prog.Exec mem done ((4+10*(2*2^span))+(4+N*(2*op.work+4))) ∧
      Reads out (sumWord peer query items bounded) M done ∧
      (∀x,x<base ∨ out.base+N≤x→done x=mem x) ∧
      DescentStaticWordColumn.names prog=15*(2*2^span+1)+(11+4*op.work) ∧ CheapCode prog := by
  intro op N mounted done prog
  have endOut : out.base<2^w:=(Nat.le_add_right ..).trans_lt fits
  have early : base≤out.base:=(Nat.le_add_right ..).trans apart
  have started:=DescentOrdinaryAtomFieldRAM.ROM.run pages span base mem (apart.trans_lt endOut)
  have budget (j : Fin 2) : (pages j).bits≤ span := by
    fin_cases j
    · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
    · rfl
  have tables:=binary_mounted law M pages span base mem budget id (fun _=>rfl)
  have stable:=DescentOrdinaryAtomFieldRAM.ROM.frame pages span base mem
  have keep {d : ℕ} (expr : Expr) (ef : expr.Fits w base) (v : Fin H→Fin G→Cell d) (held : Source expr v M mem) :
      Source expr v M mounted := fun j=>(ProtocolRAM.eval_below expr _ mem mounted ef (fun z hz=>stable z (.inl hz))).trans (held j)
  have fit (i : Fin n) : DescentPackedZip.Fits table q (a i) (b*5) (b*5) M out.base w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ early qFit,ProtocolRAMGeneratedWrite.fits_mono _ early (aFit i),
      bank_room pages span base _ _ (budget 0) apart endOut,bank_room pages span base _ _ (budget 1) apart endOut,rfl,rfl⟩
  have fixed (i : Fin n) : (DescentPackedZip.Tables.read table q (a i)).Fits w out.base := by
    have hi:=fit i
    exact ⟨hi.apply,hi.right,hi.shift,hi.left⟩
  have running : (scan w out.base N op).Exec mounted done (4+N*(2*op.work+4)) :=
    @scan_exec w out.base N op mounted (fits_total _ fixed _) fits
  refine ⟨Procedure.Exec.then (A:=mount pages span w base) (B:=scan w out.base N op) started.1 running,?_,?_,?_,cheap_seq (cheap pages span w base) (@scan_cheap _ _ _ _)⟩
  · intro rowId
    change image out.base N op mounted (out.base+(row H G M rowId).val)=_
    rw [ProtocolRAMGeneratedWrite.read_image out.base N op mounted (row H G M rowId)]
    have each (i : Fin n) := read_data table q (a i) out.base (fit i) law (blank ..) mounted tables
      _ _ (keep _ qFit _ qSource) (keep _ (aFit i) _ (aSource i)) rowId
    simp only [kernel,unpack_literal _ _ (qRoom _ _),unpack_literal _ _ (aRoom _ _ _)] at each
    have sum:=eval_sum _ _ mounted _ each (List.finRange n)
    rw [←List.ofFn_eq_map,List.sum_ofFn,packed_sum peer query items bounded] at sum
    exact sum
  · intro x away
    exact (ProtocolRAMGeneratedWrite.frame_image out.base N op mounted x (by rcases away with h|h <;> omega)).trans
      (stable x (by rcases away with h|h <;> omega))
  · rw [DescentStaticWordColumn.names_seq,started.2,DescentStaticWordColumn.names_scan]

end
end Hierarchy.DescentResetSignedScan

end OAI
