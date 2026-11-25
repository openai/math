import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Numeric indices into the previously reached pointer, chip and cohort registers -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section
variable {cap N A H w d : ℕ}
def columns (cap N A : ℕ) := 3+N+4*(N*A)+2*cap
local notation "numCols" => columns cap N A
abbrev Source (cap N A d : ℕ) := Fin (columns cap N A)→ Cell d

def ncol : Fin numCols:=⟨0,by unfold columns;omega⟩
def mcol : Fin numCols:=⟨1,by unfold columns;omega⟩
def fcol : Fin numCols:=⟨2,by unfold columns;omega⟩
def acol (j : Fin N) : Fin numCols:=⟨3+j.val,by have:=j.isLt;unfold columns;omega⟩
def pcol (f : Fin 4) (j : Fin (N*A)) : Fin numCols:=
  ⟨3+N+(finProdFinEquiv (f,j)).val,by have:=(finProdFinEquiv (f,j)).isLt;unfold columns;omega⟩
def scol (j : Fin (2*cap)) : Fin numCols:=⟨3+N+4*(N*A)+j.val,by have:=j.isLt;unfold columns;omega⟩


section Reads
variable {C : ℕ}
/-- A table key is assembled from the actual words already resident at the target
common host. Only the short bit bound on a numerical word is needed to read it. -/
def observed (banks : Fin C→ Bank) (m : Memory w) (narrow : ∀h : Fin H,∀j,(m ((banks j).base+h.val)).val < 2^d)
    (h : Fin H) (j : Fin C) : Cell d:=⟨_,narrow h j⟩

theorem observed_reads (banks : Fin C→ Bank) (m : Memory w) (narrow : ∀h : Fin H,∀j,(m ((banks j).base+h.val)).val < 2^d)
    (h : Fin H) (j : Fin C) : m ((banks j).base+h.val)=((observed banks m narrow h j).val:Word w) := by
  simp only [observed,Fin.cast_val_eq_self]

/-- Any bits above the paid source format are ignored by the actual bounded read. -/
def low (banks : Fin C→ Bank) (m : Memory w) (h : Fin H) (j : Fin C) : Cell d :=
  ((m ((banks j).base+h.val)).val:Cell d)


end Reads
end
end Hierarchy.DescentTerminalPointerDigits

end OAI
