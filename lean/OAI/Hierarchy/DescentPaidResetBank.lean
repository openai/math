import OAI.Hierarchy.DescentPaidResetTree
import OAI.Hierarchy.DescentPaidResetRotor
import OAI.Hierarchy.DescentPaidResetWindowROM
import OAI.Hierarchy.DescentPackedPrivateInput

namespace OAI
/-! # Reading a mixed-bank funded population from the five installed root fields -/
namespace Hierarchy.DescentPaidResidentCount.Reset.BankIssue
open DescentPackedPrivateMenu DescentPackedFallbackTree DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM.ROM DescentPacking.PackedMatch.Local.Gather
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {n h : ℕ} (graph : NonlinearExpanders.Graph n h)

/-- The role is a public address in one common rotor/tree atlas. -/
inductive Site (graph : NonlinearExpanders.Graph n h) (height : ℕ)
  | rotor (atSite : (DescentCommonPalette.rotor graph).Site)
  | tree (level : Fin (height+1)) (node : DescentContactTree.Node level.val)

def amount {r ht cnt l : ℕ} (C b m : ℕ) (role : Site graph ht) : Key (n:=n) r ht cnt l→ℕ
  | some (.inl (_,layers))=>match role with
    | .rotor atSite=>Rotor.funded graph C b m layers.val atSite
    | .tree _ _=>0
  | some (.inr (_,_,arrivals))=>match role with
    | .rotor _=>0
    | .tree level node=>
      if level.val≤(((encode (ht+2) (cnt+1)).symm arrivals) 0).val then
        DescentPackedFallbackTree.tally arrivals (Tree.window ht node)*m else 0
  | none=>0

theorem tree_amount {r ht cnt l : ℕ} (C b m : ℕ) (label : Cell (r+1))
    (choice : Fin (2^n+1)) (bookDepth : ℕ) (room : bookDepth≤ht)
    (arrivals : Panel ht cnt) (level : Fin (ht+1)) (node : DescentContactTree.Node level.val) (live : level.val≤bookDepth) :
    amount (l:=l) graph C b m (.tree level node)
      (some (.inr (label,choice,DescentPackedFallbackTree.pack ht bookDepth arrivals)))=
      DescentPackedFallbackTree.count arrivals (Tree.window ht node)*m := by
  have small : bookDepth<2^(ht+2):=(Nat.lt_succ_self _).trans_le
    (by have:=Nat.lt_two_pow_self (n:=ht+2);omega)
  rw [amount,ite_eq_left ?_,DescentPackedFallbackTree.tally_pack]
  simpa [DescentPackedFallbackTree.pack,Fin.val_cast_of_lt small] using live

theorem rotor_amount {r ht cnt l : ℕ} (C b m : ℕ) (atSite : (DescentCommonPalette.rotor graph).Site)
    (label : Cell (r+1)) (layers : Cell l) :
    amount (cnt:=cnt) (ht:=ht) graph C b m (.rotor atSite) (some (.inl (label,layers)))=
      Rotor.funded graph C b m layers.val atSite := rfl

variable {r ht cnt l H G M w base : ℕ} (C b m precision : ℕ) (role : Site graph ht)
local notation "bits" => digitBits n r ht cnt l
local notation "ops" => numeral n r ht cnt l
local notation "srcbits" => bits*5
local notation "size" => ((0+srcbits)*M)

def kernel (_ : Cell 0) (word : Cell srcbits) : Cell precision :=
  ((amount graph C b m role (unpack r ht cnt l (ops word)) : ℕ):Cell precision)

theorem kernel_read (x : Key (n:=n) r ht cnt l) :
    kernel graph C b m precision role 0 (encode bits 5 (payload r ht cnt l x))=
      ((amount graph C b m role x:ℕ):Cell precision) := by
  simp only [kernel,numeral_read,DescentPackedPrivateMenu.unpack_pack]

open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather

theorem blank :
    kernel (r:=r) (l:=l) (cnt:=cnt) graph C b m precision role 0 0=0 := by
  have same : encode bits 5 (payload (n:=n) r ht cnt l none)=0:=DescentPacking.PackedMatch.Local.Gather.encode_zero _ _
  rw [←same,kernel_read]
  rfl

local notation "f" => kernel (r:=r) (cnt:=cnt) (l:=l) graph C b m precision role
local notation "pg" => binary f M
local notation "tab" => joined pg size base (fun j=>j)

/-- The input expression comes from the private-header gather itself. The two
fixed pages are written and the entire group-packed bank is scanned once.
The selected row returns zero at absent roots and at roles of the other kind. -/
theorem fresh (field : Expr) (out : Bank) (mem : Memory w) (early : field.Fits w base)
    (keys : Fin H→Fin G→Key (n:=n) r ht cnt l)
    (published : Source field (fun v g=>encode bits 5 (payload r ht cnt l (keys v g))) M mem)
    (apart : base+2*2^size≤out.base) (space : out.base+H*chunks G M<2^w) :
    let mounted:=after pg size base mem
    let read:=(tab).read (.lit 0) field
    let N:=H*chunks G M
    let done:=image out.base N read mounted
    let program:=(mount pg size w base).seq (scan w out.base N read)
    program.Exec mem done ((4+10*(2*2^size))+(4+N*(2*read.work+4))) ∧
      DescentPackedColony.Reads out (fun v g=>((amount graph C b m role (keys v g):ℕ):Cell precision)) M done ∧
      (∀i,i<base ∨ out.base+N≤ i→done i=mem i) ∧
      DescentStaticWordColumn.names program=15*(2*2^size+1)+(11+4*((.lit 0:Expr).work+field.work+11)) ∧ CheapCode program := by
  have empty : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) M mem := by
    intro j
    change 0=(((finFunctionFinEquiv (fun i : Fin M=>if _ : j.2.val*M+i.val<G then (0:Cell 0) else 0)).val:ℕ):Word w)
    simp []
  simpa only [kernel_read] using WindowRAM.binaryFresh f (blank ..) (.lit 0) field out mem
    (by trivial) early _ _ empty published apart space

end
end Hierarchy.DescentPaidResidentCount.Reset.BankIssue

end OAI
