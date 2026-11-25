import OAI.Hierarchy.DescentTerminalRecipeRows
import OAI.Hierarchy.DescentTerminalScanFacts
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # A single bounded remainder lookup per common position in the terminal plane -/
namespace Hierarchy.DescentTerminalSiteOffsets
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalBinPack DescentTerminalRecipeRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w n W S : ℕ}
structure Layout where
  first : Bank
  modulo : Bank
  offsets : Bank

variable (L:Layout)
def read : Expr := .lookup L.modulo (.lookup L.first .row)
def program (w S : ℕ) := scan w L.offsets.base S (read L)
def result (S : ℕ) (m : Memory w) := image L.offsets.base S (read L) m
def time (S : ℕ) := 4+S*(2*(read L).work+4)

structure Room (w S : ℕ) : Prop where
  first : L.first.Fits w L.offsets.base
  modulo : L.modulo.Fits w L.offsets.base
  offsets : L.offsets.base+S<2^w

theorem run (S : ℕ) (m : Memory w) (ok:Room L w S) :
    (program L w S).Exec m (result L S m) (time L S) ∧ CheapCode (program L w S) := by
  unfold program result time
  exact ⟨@scan_exec w L.offsets.base S (read L) m ⟨ok.modulo,ok.first,trivial⟩ ok.offsets,
    @scan_cheap w L.offsets.base S (read L)⟩

theorem time_eq (S : ℕ) : time L S=4+28*S := by
  change 4+S*28=4+28*S
  omega

theorem actual (sites : Fin S→Site) (q W : ℕ) (m : Memory w)
    (firsts : ∀v:Fin S,L.first.read m (v.val:Word w)=(first W (counts (q:=q) sites) v:Word w))
    (total : ∀v:Fin S,first W (counts (q:=q) sites) v<n)
    (table : ∀x:Fin n,L.modulo.read m (x.val:Word w)=((x.val%W:ℕ):Word w))
    (v:Fin S) : result L S m (L.offsets.base+v.val)=(offset W (counts (q:=q) sites) v:Word w) := by
  unfold result
  rw [DescentTerminalChipRuntime.image_at]
  change L.modulo.read m (L.first.read m (v.val : Word w)) = _
  rw [firsts v]
  exact table ⟨_,total v⟩

theorem early (S : ℕ) (m : Memory w) {j:ℕ} (hj:j<L.offsets.base) : result L S m j=m j :=
  DescentTerminalChipRuntime.image_low _ _ _ _ hj


end
end Hierarchy.DescentTerminalSiteOffsets

end OAI
