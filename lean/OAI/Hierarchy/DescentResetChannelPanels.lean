import OAI.Hierarchy.DescentResetMeasuredChannels
import OAI.Hierarchy.DescentResetGLPanels

namespace OAI
/-! # Physical suffix panels and true original-order bits from one remixed bank -/
namespace Hierarchy.DescentSixParty.PackedFlow.Channels
open DescentGLPacked DescentGLPacked.BankImage DescentPlainTerminal.Suffix DescentGL DescentColonies
open DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {D H h l b w c M : ℕ}
abbrev Index (D m : ℕ) := Fin ((1+D)+m)

def loadIndex (D m : ℕ) : Index D m := finSumFinEquiv (.inl (finSumFinEquiv (.inl (0:Fin 1))))
def flowIndex (m : ℕ) (j : Fin D) : Index D m := finSumFinEquiv (.inl (finSumFinEquiv (.inr j)))
def planeIndex (D : ℕ) {m : ℕ} (d : Fin m) : Index D m := finSumFinEquiv (.inr d)

variable (weights : Fin H→Block (h + l)→Cell b) (flows : Fin D→Fin H→Block (h + l)→Cell b) (pos : 0<b)
    (L : DescentGL.Layout (h + l)) (bank : Index D (h + l)→Bank) (mem : Memory w)
    (published : ∀i,Dense (h:=h) (l:=l) (bank i).base (fun v x=>values weights flows pos i v ((rearrange L).symm x)) mem)

def blockValues (small : c≤ (h + l)) (row : Fin H→Block (h + l)→Cell b) (L : DescentGL.Layout (h + l)) (v : Fin H) (hi : Block c) :
    Cell (b*2^((h + l)-c)) := encode b (2^((h + l)-c)) (fun x=>row v ((rearrange L).symm (join small hi x)))

include published in
theorem panel_at (small : c≤ (h + l)) (pitch : M*2^((h + l)-c)=2^l) (lanes : 0<M) (out : ℕ)
    (fits : ∀i,(bank i).Fits w out) (size : ∀i,H*chunks (2^c) M≤(bank i).size) (i : Index D (h + l)) :
    Source (.lookup (bank i) .row) (blockValues small (values weights flows pos i) L) M mem := by
  apply source_column (bank i) out (fits i) mem _ (size i)
  exact grouped_remix small pitch lanes (bank i).base (values weights flows pos i) L mem (published i)

include published in
theorem operands (small : c≤ (h + l)) (pitch : M*2^((h + l)-c)=2^l) (lanes : 0<M) (out : ℕ)
    (fits : ∀i,(bank i).Fits w out) (size : ∀i,H*chunks (2^c) M≤(bank i).size)
    (narrow : Bank) (narrowFit : narrow.Fits w out) (narrowSize : narrow.bits=(b*2^((h + l)-c))*M)
    (static : ∀z : Cell ((b*2^((h + l)-c))*M),
       mem (narrow.base+z.val)=((DescentSIMDLookup.table (Original.narrow b ((h + l)-c)) z).val:Word w)) :
    Source (.lookup (bank (loadIndex D (h + l))) .row) (blockValues small weights L) M mem ∧
    (∀j : Fin D,Source (.lookup (bank (flowIndex (h + l) j)) .row) (blockValues small (flows j) L) M mem) ∧
    (∀j : Fin (h + l),Source (DescentPlainTerminal.PackedOrder.projected narrow (.lookup (bank (planeIndex D j)) .row))
      (fun (_ : Fin H) hi=>DescentPlainTerminal.PackedOrder.panel small L hi j) M mem) := by
  have reads:=panel_at weights flows pos L bank mem published small pitch lanes out fits size
  refine ⟨?_,?_,?_⟩
  · have load : values weights flows pos (loadIndex D (h + l)) = weights := by
      funext v x
      unfold values
      simp only [loadIndex, Equiv.symm_apply_apply, Sum.elim_inl]
    simpa only [load] using reads (loadIndex D (h + l))
  · intro j
    have flow : values weights flows pos (flowIndex (h + l) j) = flows j := by
      funext v x
      unfold values
      simp only [flowIndex, Equiv.symm_apply_apply, Sum.elim_inr]
    simpa only [flow] using reads (flowIndex (h + l) j)
  · intro j
    have plane : values weights flows pos (planeIndex D j) = fun _ x => Original.bit pos j x := by
      funext v x
      unfold values
      simp only [planeIndex, Equiv.symm_apply_apply]
    have read := reads (planeIndex D j)
    rw [plane] at read
    unfold blockValues at read
    exact Original.panel_source small pos L j _ narrow out mem narrowFit narrowSize static read

end
end Hierarchy.DescentSixParty.PackedFlow.Channels

end OAI
