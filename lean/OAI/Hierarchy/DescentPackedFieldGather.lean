import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Assemble bounded packed fields by native indexed dictionary reads -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {d N H G M w : ℕ}

private theorem encode_zero (a n : ℕ) : encode a n (fun _=>0)=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val=0
  simp []

private theorem zero_fields (a n : ℕ) : (encode a n).symm 0=(fun _=>0) :=
  (encode a n).symm_apply_eq.mpr (encode_zero a n).symm

def setField (i : Fin N) (acc : Cell (d*N)) (v : Cell d) :=
  encode d N (fun j=>if i=j then v else (encode d N).symm acc j)

private theorem set_zero (i : Fin N) : setField (d:=d) i 0 0=0 := by
  simp only [setField,zero_fields,ite_self,encode_zero]

def collect (tables : Fin N→Tables) (field : Fin N→Expr) : List (Fin N)→Expr
  | []=>.lit 0
  | i::is=>(tables i).read (collect tables field is) (field i)

def Bounds (tables : Fin N→Tables) (field : Fin N→Expr) (out : ℕ) : Prop :=
  ∀i,(field i).Fits w out ∧ (tables i).shift.Fits w out ∧ (tables i).apply.Fits w out ∧
    (tables i).shift.bits=(d*N)*M ∧ (tables i).apply.bits=(d*N+d)*M

include d M in
theorem fits (tables : Fin N→Tables) (field : Fin N→Expr) (out : ℕ)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field out) (is : List (Fin N)) : (collect tables field is).Fits w out := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    simp [collect,Tables.read,Expr.Fits,(bounds i).2.2.1,(bounds i).1,(bounds i).2.1,ih]

theorem collected (tables : Fin N→Tables) (field : Fin N→Expr) (out : ℕ)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field out) (m : Memory w)
    (static : ∀i,Static (tables i) (setField (d:=d) i) M m)
    (v : Fin H→Fin G→Fin N→Cell d) (source : ∀i,Source (field i) (fun h g=>v h g i) M m) (is : List (Fin N)) :
    Source (collect tables field is) (fun h g=>encode d N (fun j=>if j∈is then v h g j else 0)) M m := by
  induction is with
  | nil =>
    intro rowId
    simp only [List.not_mem_nil,ite_false,encode_zero]
    change 0=(((finFunctionFinEquiv (fun i : Fin M=>if _ : rowId.2.val*M+i.val<G then (0:Cell (d*N)) else 0)).val:ℕ):Word w)
    simp []
  | cons i is ih =>
    have b := bounds i
    have sf : DescentPackedZip.Fits (tables i) (collect tables field is) (field i) (d*N) d M out w :=
      ⟨fits tables field out bounds is,b.1,b.2.1,b.2.2.1,b.2.2.2.1,b.2.2.2.2⟩
    have ready := read_data (tables i) (collect tables field is) (field i) out sf (setField (d:=d) i) (set_zero i) m (static i)
      _ _ ih (source i)
    have agree (h : Fin H) (g : Fin G) :
        setField i (encode d N (fun j=>if j∈is then v h g j else 0)) (v h g i)=
        encode d N (fun j=>if j∈i::is then v h g j else 0) := by
      unfold setField
      congr 1
      funext j
      by_cases equal : i=j
      · subst j;simp
      · simp [equal,Ne.symm equal]
    simpa only [collect,agree] using ready

def assembly (tables : Fin N→Tables) (field : Fin N→Expr) := collect tables field (List.finRange N)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
