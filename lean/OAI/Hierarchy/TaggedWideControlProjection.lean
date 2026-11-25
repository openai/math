import OAI.Hierarchy.TaggedWideControlValues

namespace OAI
/-! # Project a native control field to its numerical word -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope
open ThreeFlat.RAM DescriptorExpr
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged PassiveWindow
variable {S W D cap : ℕ} {s : Fin S}
variable (pass before after : ((portGraph S).Port s)→ℕ)
    (l : Parts ((portGraph S).Port s) (Fin D) cap fun p=>pass p+before p) (r : Parts ((portGraph S).Port s) (Fin D) cap fun p=>pass p+after p)

def expected : Field D→ℕ
  | .inl (side,.inl (i,j)) => if side then (ChordAperture.sizeAt r i j).val else (ChordAperture.sizeAt l i j).val
  | .inl (side,.inr (.inl (i,b)))=> if side then (ChordAperture.head r i b).val else (ChordAperture.head l i b).val
  | .inl (side,.inr (.inr i))=>if side then ChordAperture.room r i else ChordAperture.room l i
  | .inr ((i,j),f)=>if f=0 then (header cap (l.view before i) (r.view after j) (linked pass before after l r i j)).val
    else (heads cap (l.view before i) (r.view after j) (decide (f=2))).val

theorem CompiledFields.project (m : Memory W) (reg : Word W) (col : Bool→Fin D→LocalPrefix.Columns)
    (low : Bool→Fin D→Expr) (read : CompiledFields m reg pass before after l r col low) (f : Field D) :
    ((compile cap col low f).eval m reg).val=expected pass before after l r f := by
  rcases f with ⟨side,field⟩|⟨⟨i,j⟩,q⟩
  · rcases field with ⟨i,j⟩|second
    · exact read.size side i j
    · rcases second with ⟨i,b⟩|i
      · exact read.head side i b
      · exact read.room side i
  · fin_cases q
    · exact read.length i j
    · exact read.heads i j false
    · exact read.heads i j true

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
