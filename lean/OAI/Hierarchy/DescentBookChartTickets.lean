import OAI.Hierarchy.DescentIssuedSharedBook
import OAI.Hierarchy.DescentShortBookScan

namespace OAI
/-! # Short tickets for a host's shared fallback rank table -/
namespace Hierarchy.DescentSharedBookScan
open DescentSIMDLookup DescentSharedLeafLookup
open DescentFallbackShapeTable DescentContacts
open scoped Classical Fin.CommRing
noncomputable section
variable {r Y Δ d : ℕ}

def bits (r Y Δ : ℕ) := Nat.clog 2 (width r Y Δ+1)
def ticket (p : Fields r Y Δ) : Cell (bits r Y Δ) :=
  ⟨(fieldId p).val+1,(Nat.succ_lt_succ (fieldId p).isLt).trans_le (Nat.le_pow_clog (by decide) _)⟩

theorem choose_ticket (p : Fields r Y Δ) (rank : Fin (width r Y Δ)→Cell d) :
    choose _ (ticket p) (encode d _ rank)=rank (fieldId p) := by
  have ok : 0<(ticket p).val ∧ (ticket p).val≤width r Y Δ:=⟨Nat.zero_lt_succ _,(fieldId p).isLt⟩
  simp only [choose,dite_eq_left ok,Equiv.symm_apply_apply]
  congr 1

def shapeCell (z : Endpoint Y) (small : z.1.1≤r) (valid : z.1.2<2^z.1.1) : Fin (rows r Y) :=
  ⟨cell r z,cell_fit r z small valid⟩

/-- A remote stencil field is `2*cell + bad` in the packed reset matrix.
Zero is a genuine shape at an occupied vertex. The incoming live tag is separate. -/
def remote (root : Fin (rows r Y)) (arrival : Option (Fin Δ)) (word : ℕ) : Cell (bits r Y Δ) :=
  match arrival with
  | none=>0
  | some j=>if ok : word/2<rows r Y then ticket (root,j.succ,⟨word/2,ok⟩) else 0

theorem remote_read (root : Fin (rows r Y)) (j : Fin Δ) (z : Endpoint Y)
    (small : z.1.1≤r) (valid : z.1.2<2^z.1.1) (bad : Bool) :
    remote root (some j) (2*cell r z+bad.toNat)=ticket (root,j.succ,shapeCell z small valid) := by
  have dec : (2*cell r z+bad.toNat)/2=cell r z := by cases bad <;> simp; omega
  simp only [remote,dec,dite_eq_left (cell_fit r z small valid)]
  rfl

def amount (root : Fin (rows r Y)) : Cell (bits r Y Δ) := ticket (root,0,root)

theorem choose_empty (scores : Cell (d*width r Y Δ)) :
    choose (width r Y Δ) (0:Cell (bits r Y Δ)) scores=0 := by simp [choose]

end
end Hierarchy.DescentSharedBookScan

end OAI
