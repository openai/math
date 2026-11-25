import OAI.Hierarchy.ProbeFixedAttemptStates
import OAI.Hierarchy.TaggedWireAttemptBalances
import OAI.Hierarchy.TaggedWireGoodsDistinct

namespace OAI
/-! # Native stock words collect onto their genuine center-to-center physical chords -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProtocolRAM Calendar WireTelescope
open scoped Classical BigOperators

variable {h d k S g : ℕ} (π : Equiv.Perm (Fin (2^h))) (place : Site h d k→Fin S)
local notation "I" => FeedTransfer.Data h d k

/-- Each RAM inventory row is the image under precisely its native word slot,
including distinct signed demands with the same actual pair of sites. -/
def ordinalGoods (order : I≃Fin g) : PortGraph (Fin S) (Fin g) :=
  let G:=commodityGraph π place
  ⟨G.tail ∘ order.symm,G.head ∘ order.symm⟩

theorem ordinalGoods_width (order : I≃Fin g) (bits : Fin g→ℕ) :
    (ordinalGoods π place order).chordWidths bits=(commodityGraph π place).chordWidths (bits ∘ order) := by
  unfold PortGraph.chordWidths
  have same (i : I) : (ordinalGoods π place order).chordWidth (order i) (bits (order i))=
      (commodityGraph π place).chordWidth i (bits (order i)) := by
    simp only [PortGraph.chordWidth,ordinalGoods,Function.comp_apply,Equiv.symm_apply_apply]
  rw [←order.sum_comp (fun i=>(ordinalGoods π place order).chordWidth i (bits i))]
  exact Finset.sum_congr rfl (fun i _=>same i)

theorem ordinalGoods_distinct (order : I≃Fin g) (inj : Function.Injective place) (i : Fin g) :
    (ordinalGoods π place order).tail i≠(ordinalGoods π place order).head i :=
  inj.ne (goods_different π (order.symm i))

theorem chordWidths_empty {A : Type} [Fintype A] (G : PortGraph (Fin S) A) :
    G.chordWidths (fun _=>0)=0 := by
  unfold PortGraph.chordWidths
  apply Finset.sum_eq_zero
  intro i _
  unfold PortGraph.chordWidth
  split_ifs <;> simp

end Hierarchy.ProbeStage.CoreBoard

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)

def nativeGoods (π : Equiv.Perm (Fin (2^z))) (a : Attempt) :=
  ordinalGoods π (siteNumber z (2^v.W) k) (v.nativeSlots P z width a)

theorem nativeGoods_stock (π : Equiv.Perm (Fin (2^z))) (a : Attempt) (base : ℕ)
    {W : ℕ} (m : Computability.VPVNP.BurstRAM.Memory W) :
    (v.nativeGoods P z width π a).chordWidths (fun i=>(m (base+i.val)).val)=
      (commodityGraph π (siteNumber z (2^v.W) k)).chordWidths (PurchaseInventory.stock base m) :=
  ordinalGoods_width π (siteNumber z (2^v.W) k) (v.nativeSlots P z width a) _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
