import OAI.Hierarchy.DescentTerminalRoleWords

namespace OAI
/-! # Native role and slice columns from an authentic scalar birth header -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentEpochTagKeys DescentBundleHistory DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {U : Type} {n A G p R : ℕ}

def literal (b m:ℕ) (f : Fin m→ℕ) := (encode b m (fun j=>(f j:Word b))).val

theorem literal_lanes (b m:ℕ) (f : Fin m→ℕ) (i:Fin m) :
    digit b i.val (literal b m f)=f i%2^b := by simp [literal,digit_encode,Fin.val_natCast]

def rawWords (x:Fields A G) : Arrays n A G p R := fun f=>
  let fields : Fin 6→ℕ:=![x.primitive,x.arity,literal (Nat.clog 2 (G+1)) A x.groups,
    literal (Nat.clog 2 (p+1)) G (fun j=>(x.triple j).start),
    literal (Nat.clog 2 (R+2)) G (fun j=>(x.triple j).stride),
    literal (Nat.clog 2 (R+2)) G (fun j=>(x.triple j).count)]
  (fields f:Word (width n A G p R f))

theorem literal_fit (b m : ℕ) (f : Fin m→ℕ) : literal b m f<2^(m*b) := by
  rw [Nat.mul_comm];exact (encode b m (fun j=>(f j:Word b))).isLt

private theorem same_triple {s t : SliceCode} (a : s.start=t.start) (b : s.stride=t.stride) (c : s.count=t.count) : s=t := by
  cases s; cases t; simp_all

theorem raw_emits (old : Codec U n) (u:U) (xs:List (List SliceCode)) (x:Fields A G)
    (cols : Printed old x u xs) (fit : DescentBundleTagKeys.Fits old A G p R (u,xs)) :
    Printed old (fields (rawWords (n:=n) (p:=p) (R:=R) x)) u xs := by
  obtain ⟨_,_,_,sliceFits⟩:=fit
  have lift (z b : ℕ) (lim : z<b) : z<2^(Nat.clog 2 b) := lim.trans_le (Nat.le_pow_clog (by decide) _)
  have primitive : x.primitive<n+1 := by rw [cols.primitive];have:=(old.store u).isLt;omega
  have len : x.arity<A+1 := by have:=cols.arity;have:=cols.operands;omega
  have rowCap (j : Fin xs.length) : xs[j].length≤G := by
    have sub : xs[j].length≤xs.flatten.length := by
      have sublist : List.Sublist xs[j] xs.flatten := List.sublist_flatten_of_mem (List.getElem_mem j.isLt)
      exact sublist.length_le
    exact sub.trans cols.slicesFit
  refine ⟨?_,?_,cols.operands,cols.slicesFit,?_,?_⟩
  · change x.primitive%2^(Nat.clog 2 (n+1))=_;rw [Nat.mod_eq_of_lt (lift _ _ primitive),cols.primitive]
  · change x.arity%2^(Nat.clog 2 (A+1))=_;rw [Nat.mod_eq_of_lt (lift _ _ len),cols.arity]
  · intro j
    change digit _ _ (literal _ _ x.groups%2^(A*Nat.clog 2 (G+1)))=_
    rw [Nat.mod_eq_of_lt (literal_fit ..),literal_lanes,cols.groups,Nat.mod_eq_of_lt (lift _ _ (Nat.lt_succ_of_le (rowCap j)))]
  · intro j
    have lim:=sliceFits xs.flatten[j] (List.getElem_mem j.isLt)
    rcases lim with ⟨start,stride,count⟩
    have read_field (b : ℕ) (proj : SliceCode → ℕ) (bound : proj xs.flatten[j] < 2^b) :
        digit b (j.castLE cols.slicesFit).val
          (literal b G (fun i => proj (x.triple i)) % 2^(G*b)) = proj xs.flatten[j] := by
      rw [Nat.mod_eq_of_lt (literal_fit ..), literal_lanes]
      change proj (x.triple (j.castLE cols.slicesFit)) % 2^b = proj xs.flatten[j]
      rw [cols.triples, Nat.mod_eq_of_lt bound]
    apply same_triple
    · exact read_field (Nat.clog 2 (p+1)) SliceCode.start (lift _ _ (by omega))
    · exact read_field (Nat.clog 2 (R+2)) SliceCode.stride (lift _ _ (by omega))
    · exact read_field (Nat.clog 2 (R+2)) SliceCode.count (lift _ _ (by omega))

def birth (old : Codec U n) (u : U) (xs : List (List SliceCode)) : Fields A G where
  primitive := (old.store u).val+1
  arity := xs.length
  groups j := (xs[j.val]?.getD []).length
  triple j := xs.flatten[j.val]?.getD ⟨0,0,0⟩

theorem birth_printed (old : Codec U n) (u : U) (xs : List (List SliceCode))
    (fit : DescentBundleTagKeys.Fits old A G p R (u,xs)) :
    Printed old (fields (rawWords (n:=n) (p:=p) (R:=R) (birth (A:=A) (G:=G) old u xs))) u xs := by
  apply raw_emits old u xs _ _ fit
  refine ⟨rfl,rfl,fit.2.1,fit.2.2.1,?_,?_⟩
  · intro j;simp [birth]
  · intro j;simp [birth,List.getElem?_eq_getElem j.isLt]

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
