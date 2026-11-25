import OAI.Hierarchy.DescentTerminalCombinedRole
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Six packed numerical columns of the combined role writer, in original group and node order -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentEpochTagKeys DescentBundleHistory DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {U : Type} {n A G p R N M : ℕ}
abbrev width (n A G p R : ℕ) : Fin 6→ℕ :=
  ![Nat.clog 2 (n+1),Nat.clog 2 (A+1),A*Nat.clog 2 (G+1),G*Nat.clog 2 (p+1),
    G*Nat.clog 2 (R+2),G*Nat.clog 2 (R+2)]
local notation "size" => width n A G p R
def output (n A G p R : ℕ) := Nat.clog 2 (DescentBundleTagKeys.capacity n A G p R+1)

abbrev Arrays (n A G p R : ℕ) := (j:Fin 6)→Word (width n A G p R j)
def fields (src : Arrays n A G p R) : Fields A G where
  primitive := (src 0).val
  arity := (src 1).val
  groups j := digit (Nat.clog 2 (G+1)) j.val (src 2).val
  triple j := ⟨digit (Nat.clog 2 (p+1)) j.val (src 3).val,
    digit (Nat.clog 2 (R+2)) j.val (src 4).val,digit (Nat.clog 2 (R+2)) j.val (src 5).val⟩

def localRole (old : Codec U n) (src : Arrays n A G p R) : Word (output n A G p R) :=
  ⟨written old p R (fields src),(Nat.lt_succ_of_le (written_bound old (fields src))).trans_le (Nat.le_pow_clog (by decide) _)⟩

theorem role_digits (old : Codec U n) (src : Arrays n A G p R) (u:U) (xs:List (List SliceCode))
    (ready : Printed old (fields src) u xs) (born : old.fits u) :
    (localRole old src).val=((DescentBundleTagKeys.codec old A G p R).store (u,xs)).val+1 :=
  written_read old _ u xs born ready

/-- The first axis is the actual old group and the second is the chronological node at that venue. -/
abbrev Sources (n A G p R N M : ℕ) := (j:Fin 6)→Word (width n A G p R j*N*M)
def collect (x : Fin M→Fin N→Arrays n A G p R) : Sources n A G p R N M :=
  fun f=>encode (size f*N) M (fun g=>encode (size f) N (fun v=>x g v f))

def node (src : Sources n A G p R N M) (g : Fin M) (u : Fin N) : Arrays n A G p R :=
  fun f=>(encode (size f) N).symm ((encode (size f*N) M).symm (src f) g) u

def rolePanel (old : Codec U n) (src : Sources n A G p R N M) : Word (output n A G p R*N*M) :=
  encode (output n A G p R*N) M (fun g=>encode (output n A G p R) N (fun u=>localRole old (node src g u)))

theorem node_collect (x : Fin M→Fin N→Arrays n A G p R) (g : Fin M) (u : Fin N) : node (collect x) g u=x g u := by
  funext f
  simp [node,collect]

theorem rolePanel_read (old : Codec U n) (x : Fin M→Fin N→Arrays n A G p R) (g : Fin M) (u : Fin N) :
    digit (output n A G p R) u.val (digit (output n A G p R*N) g.val (rolePanel old (collect x)).val)=(localRole old (x g u)).val := by
  rw [rolePanel,digit_encode,digit_encode,node_collect]

theorem rolePanel_zero (old : Codec U n) (x : Fin M→Fin N→Arrays n A G p R) (g : Fin M) (u : Fin N) (absent : x g u 0=0) :
    digit (output n A G p R) u.val (digit (output n A G p R*N) g.val (rolePanel old (collect x)).val)=0 := by
  rw [rolePanel_read];exact empty old _ (by simp [fields,absent])

theorem payload_size : (∑f : Fin 6,size f*N*M)=
    (Nat.clog 2 (n+1)+Nat.clog 2 (A+1)+A*Nat.clog 2 (G+1)+G*(Nat.clog 2 (p+1)+2*Nat.clog 2 (R+2)))*N*M := by
  simp [Fin.sum_univ_succ,width]
  ring

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
