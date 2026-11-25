import OAI.Hierarchy.DescentResetOriginalDonorRead

namespace OAI
/-! Dense successor label and cargo words read through the earlier, physically mounted inverse. -/
namespace Hierarchy.DescentResetOriginalDonors.Layout
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (L : DescentResetOriginalDonors.Layout) {H used w : ℕ}
  (name : Fin used→Fin L.sparseHosts) (v : L.Values)
  (m : Memory w) (base first : ℕ) (cnt inv : Bank)
local notation "relay" => (⟨first,H,L.sparseHosts,chunks L.groups L.lanes⟩ : DescentResetDenseOperand.Layout)

def denseLabel (x : Fin L.blocks) (side : Bool) (j : Fin L.slots) : Fin H→Fin L.groups→Cell L.selectorBits :=
  dense name (fun h g=>DescentContactWidthPage.recode L.selectorBits (v.label side j h (finProdFinEquiv (g,x))))

def denseCargo (x : Fin L.blocks) (side : Bool) (field : Fin 2) (j : Fin L.slots) : Fin H→Fin L.groups→Cell L.shortBits :=
  if field=0 then
    dense name (fun h g=>DescentContactWidthPage.recode L.shortBits (v.ticket side j h (finProdFinEquiv (g,x))))
  else dense name (fun h g=>DescentContactWidthPage.recode L.shortBits (v.halo j h (finProdFinEquiv (g,x))))

structure Directory (cut : ℕ) : Prop where
  books : (⟨first,H,L.sparseHosts,chunks L.groups L.lanes⟩ : DescentResetDenseOperand.Layout).Books m
  fits : (⟨first,H,L.sparseHosts,chunks L.groups L.lanes⟩ : DescentResetDenseOperand.Layout).Fits cnt inv w cut
  count : m cnt.base=(used:Word w)
  inverse : ∀i : Fin used,m (inv.base+i.val)=((name i).val:Word w)
  countFits : used<2^w
  hostFits : H≤2^w
  invFits : used≤ inv.size

theorem dense_sources (cut : ℕ) (directory : L.Directory (H:=H) name m first cnt inv cut)
    (printed : L.Exhibits base v m) :
    (∀x s j,Source (L.label base relay cnt inv x s j) (L.denseLabel (H:=H) name v x s j) L.lanes m) ∧
    (∀x s a j,Source (L.cargo base relay cnt inv x s a j) (L.denseCargo (H:=H) name v x s a j) L.lanes m) :=by
  obtain ⟨one,tickets,halos⟩:=L.compact base v m printed first cnt inv name directory.books
    cut directory.fits directory.count directory.inverse directory.countFits directory.hostFits directory.invFits
  refine ⟨one,?_⟩
  intro x s a j
  fin_cases a
  · exact tickets x s j
  · exact halos x s j

end
end Hierarchy.DescentResetOriginalDonors.Layout

end OAI
