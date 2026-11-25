import OAI.Hierarchy.TaggedWireQuantityDecoder
import OAI.Hierarchy.TaggedWireStripTender
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost

namespace OAI
/-! # Bounded quantity work and interpretation in the installed strip tender -/

noncomputable section
namespace Hierarchy.ProtocolRAM.EarnedQuantity
open Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing
variable {F E A T : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E} {box : Set (E→ℝ)}
  {ε tree : ℝ} {N w : ℕ} (menu : Probe.FixedMenu F edge req box ε tree N)

private theorem totals_work (n U : ℕ) (cells : Fin n→Expr) (small : ∀ i,(cells i).work≤U) :
    (totals n cells).work≤1+n*(U+1) := by
  induction n with
  | zero => simp [totals,Expr.work]
  | succ n ih =>
    have rest := ih (fun i=>cells i.succ) (fun i=>small i.succ)
    have first := small 0
    simp only [totals,Expr.work,Nat.succ_mul]
    omega

private def entryWork (B : ℕ) (j : menu.index) :=
  let P := menu.packet j
  let copies := Finset.univ.sup (fun x : Fin P.terms × E => P.count x.1 x.2)
  max (1+P.terms*(1+copies*(B+1)+1)) (1+P.selectorBits*2)

def workCap (tagWork counterWork : ℕ) :=
  1+Fintype.card menu.index*(tagWork+(Finset.univ.sup (entryWork menu counterWork))+2)

theorem work (tag : Expr) (counter : ℕ→Expr) (copies tagWork counterWork : ℕ)
    (tagBound : tag.work≤tagWork) (fields : ∀i,(counter i).work≤counterWork) (role : E⊕T) :
    (compile menu tag counter copies role).work≤workCap menu tagWork counterWork := by
  let K := Finset.univ.sup (entryWork menu counterWork)
  have small (j : menu.index) : (term (menu.packet j).count (menu.packet j).selectorBits copies counter role).work ≤ K := by
    apply le_trans _ (show entryWork menu counterWork j≤K from Finset.le_sup (Finset.mem_univ j))
    let P := menu.packet j
    let M := Finset.univ.sup (fun x : Fin P.terms × E => P.count x.1 x.2)
    cases role with
    | inl e =>
      apply le_trans _ (Nat.le_max_left ..)
      apply totals_work
      intro i
      rw [scale_work]
      exact Nat.add_le_add_left (Nat.mul_le_mul (show P.count i e ≤ M from
        Finset.le_sup (f:=fun x : Fin P.terms × E => P.count x.1 x.2) (Finset.mem_univ (i,e))) (Nat.add_le_add_right (fields _) 1)) 1
    | inr t =>
      apply le_trans _ (Nat.le_max_right ..)
      exact (scale_work P.selectorBits (.lit copies)).le
  exact (BoughtSockets.choose_work_bound _ 1 K _ tag (fun i=>small ((Fintype.equivFin _).symm i))).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right tagBound K) 2)) 1)


end Hierarchy.ProtocolRAM.EarnedQuantity

namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Strip Probe ProtocolRAM
open scoped BigOperators Classical Fin.CommRing

/-- The physical quantity expression supplies precisely the width argument to
the strip tender's public tree-first occurrence order. -/
theorem qty_bits_ordered {F E A Ball : Type} [Field F] [Fintype E] [Fintype A] [Fintype Ball]
    {n k N S w : ℕ} (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k)))
    (roles : E→DistinctPair (TreeSite n k)) (req : A→E) (place : Ball×TreeSite n k ↪ Fin S) (u : Ball)
    (rt : Fin (Fintype.card (TreeSite n k))) (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e)) req)
    (copies : ℕ) (phys : Fin N→Chord S)
    (installed : Installs (Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)) phys)
    {r : ℕ} (ordinal : Fin r≃Σi,Fin ((installed.steps (treeFirst E (TreeLink n k))) i).length)
    (t : Histogram (Fin P.terms) copies) (qty : E⊕TreeLink n k→Expr) (m : Memory w) (row : Word w)
    (amount : ∀ x, (qty x).eval m row = ((Sum.elim (histWidth P.count t) (fun _=>copies*P.selectorBits) x : ℕ) : Word w))
    (i : Fin (Fintype.card (E⊕TreeLink n k))) :
    let tender := stripTender name roles req place u rt P copies phys installed ordinal
    (qty (treeFirst E (TreeLink n k) i)).eval m row = (tender.bits t (tender.order i) : Word w) := by
  dsimp only
  rw [bits_ordered name roles req place u rt P copies phys installed ordinal t i]
  exact amount _

/-- On a genuine ballot the native lookup and weighted archived counts equal the
width of the installed witness at every occurrence, including its selector tree. -/
theorem compiled_bits_ordered {F E A Ball : Type} [Field F] [Fintype E] [Nonempty E]
    [Fintype A] [Fintype Ball] {n k N S w : ℕ}
    [Nonempty (Fin (Fintype.card (TreeSite n k)))]
    (name : TreeSite n k ≃ Fin (Fintype.card (TreeSite n k)))
    (roles : E→DistinctPair (TreeSite n k)) (req : A→E)
    {box : Set (E→ℝ)} {ε tree : ℝ} {minimum : ℕ}
    (menu : FixedMenu F (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e)) req box ε tree minimum)
    (j : menu.index) (place : Ball×TreeSite n k ↪ Fin S) (u : Ball)
    (rt : Fin (Fintype.card (TreeSite n k))) (copies : ℕ) (phys : Fin N→Chord S)
    (installed : Installs (Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)) phys)
    {r : ℕ} (ordinal : Fin r≃Σi,Fin ((installed.steps (treeFirst E (TreeLink n k))) i).length)
    (hist : Histogram (Fin (menu.packet j).terms) copies) (tag : Expr) (counter : ℕ→Expr)
    (m : Memory w) (row : Word w) (room : 1+Fintype.card menu.index≤2^w)
    (chosen : (tag.eval m row).val=1+((Fintype.equivFin _) j).val)
    (counted : ∀t : Fin (menu.packet j).terms,(counter t.val).eval m row=((hist.val t).val:Word w))
    (i : Fin (Fintype.card (E⊕TreeLink n k))) :
    let tender := stripTender name roles (fun a : PositiveDemand req j.val.val=>req a.val)
      place u rt (menu.packet j) copies phys installed ordinal
    (EarnedQuantity.compile menu tag counter copies (treeFirst E (TreeLink n k) i)).eval m row =
      (tender.bits hist (tender.order i) : Word w) :=
  qty_bits_ordered name roles _ place u rt (menu.packet j) copies phys installed ordinal hist _
    m row (EarnedQuantity.read menu tag counter copies j hist m row room chosen counted) i


end Hierarchy.WireTelescope.ChosenPackets.RowRouting
end

end OAI
