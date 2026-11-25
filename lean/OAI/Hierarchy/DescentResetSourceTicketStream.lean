import OAI.Hierarchy.DescentResetSourceFields
import OAI.Hierarchy.DescentResetSignedScan

namespace OAI
/-! # One short immutable comparison page for all incident-parent tickets -/
namespace Hierarchy.DescentResetSourceTicketRAM
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open DescentColonies.SplitRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section


open DescentResetSignedScan
variable {b paid M w base H G K : ℕ}

/-- Incidence at the queried source is tested against both endpoints using
one common native comparison page. The second lane of a loop is empty. -/
def face (x : Fields K b) (j : Fin K) (second : Bool) : Option Parent :=
  if second && decide (field x j 0=field x j 1) then none else
    some ⟨if second then field x j 1 else field x j 0,0,field x j 2,field x j 3⟩

def query (x : Fields K b) (j : Fin K) : Option Parent := some ⟨field x j 0,0,field x j 2,0⟩

def branches (x : Fields K b) : Fin (K+K)→Option Parent :=
  Fin.addCases (fun j=>face x j false) (fun j=>face x j true)

theorem faces (x : Fields K b) (j k : Fin K) :
    contribution true (query x j) (face x k false)+contribution true (query x j) (face x k true)=fee x j k := by
  by_cases loop : field x k 0=field x k 1 <;> by_cases starts : field x k 0=field x j 0 <;>
    by_cases dest : field x k 1=field x j 0 <;> by_cases prior : field x k 2<field x j 2 <;>
    simp_all [query,face,fee,contribution,precedes]

theorem charges (x : Fields K b) (j : Fin K) :
    (∑i,contribution true (query x j) (branches x i))=∑k,fee x j k := by
  rw [Fin.sum_univ_add,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change contribution true (query x j) (branches x (Fin.castAdd K k))+
    contribution true (query x j) (branches x (Fin.natAdd K k))=fee x j k
  simpa only [branches,Fin.addCases_left,Fin.addCases_right] using faces x j k

theorem fields_fit (x : Fields K b) (j : Fin K) (p : 1<2^b) :
    DescentResetSignedScan.Fits b (query x j) ∧ ∀s,DescentResetSignedScan.Fits b (face x j s) := by
  have lim (k : Fin 4) : field x j k<2^b:=(x _).isLt
  constructor
  · exact ⟨p,lim 0,Nat.two_pow_pos _,lim 2,Nat.two_pow_pos _⟩
  · intro side
    cases side <;> simp only [face,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true]
    · exact ⟨p,lim 0,Nat.two_pow_pos _,lim 2,lim 3⟩
    · split
      · trivial
      · exact ⟨p,lim 1,Nat.two_pow_pos _,lim 2,lim 3⟩

local notation "law" => kernel b paid true
local notation "span" => ((b*5+b*5)*M)
local notation "pages" => binary law M
local notation "table" => joined pages span base id

theorem stream (q : Expr) (a : Fin (K+K)→Expr) (out : Bank) (mem : Memory w)
    (target : Fin K) (x : Fin H→Fin G→Fields K b)
    (qFit : q.Fits w base) (aFit : ∀i,(a i).Fits w base)
    (p : 1<2^b)
    (qSource : Source q (fun h g=>encode b 5 (literal b (query (x h g) target))) M mem)
    (aSource : ∀i,Source (a i) (fun h g=>encode b 5 (literal b (branches (x h g) i))) M mem)
    (bounded : ∀h g,(∑j,fee (x h g) target j)<2^paid)
    (apart : base+2*2^span≤out.base) (fits : out.base+H*chunks G M<2^w) :
    let op:=total (fun i=>DescentPackedZip.Tables.read table q (a i)) (List.finRange (K+K))
    let N:=H*chunks G M
    let mounted:=after pages span base mem
    let done:=image out.base N op mounted
    let prog:=(mount pages span w base).seq (scan w out.base N op)
    prog.Exec mem done ((4+10*(2*2^span))+(4+N*(2*op.work+4))) ∧
      Reads out (fun h g=>⟨∑j,fee (x h g) target j,bounded h g⟩ : Fin H→Fin G→Cell paid) M done ∧
      (∀x,x<base ∨ out.base+N≤x→done x=mem x) ∧
      DescentStaticWordColumn.names prog=15*(2*2^span+1)+(11+4*op.work) ∧ CheapCode prog := by
  let qs:=fun h g=>query (x h g) target
  let items:=fun i h g=>branches (x h g) i
  have member (i : Fin (K+K)) (h g) : DescentResetSignedScan.Fits b (items i h g):=by
    refine Fin.addCases (motive:=fun j=>DescentResetSignedScan.Fits b (items j h g)) ?_ ?_ i
    · intro j;simp only [items,branches,Fin.addCases_left];exact (fields_fit (x h g) j p).2 false
    · intro j;simp only [items,branches,Fin.addCases_right];exact (fields_fit (x h g) j p).2 true
  have total (h g) : (∑j,contribution true (qs h g) (items j h g))=∑j,fee (x h g) target j:=charges _ _
  let bound:=fun h g=>(total h g).trans_lt (bounded h g)
  have active:=DescentResetSignedScan.fresh true q a out mem qs items qFit aFit
    (fun h g=>(fields_fit (x h g) target p).1) member qSource aSource bound apart fits
  have exactWord : sumWord true qs items bound=(fun h g=>⟨_,bounded h g⟩ : Fin H→Fin G→Cell paid):=by
    funext h g;exact Fin.ext (total h g)
  rw [exactWord] at active
  exact active

end
end Hierarchy.DescentResetSourceTicketRAM

end OAI
