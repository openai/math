import OAI.Hierarchy.ProtocolRAMCatalogueAlignment
import OAI.Hierarchy.ProtocolRAMCataloguePruning

namespace OAI
/-! # Positive terminal rows retain their original injective catalogue ordinals -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ProbeStage.ReportSockets AdaptiveProbe ProtocolRAMEmit
open scoped Classical Fin.CommRing
noncomputable section

variable {w h W k attempts r : ℕ} {I J : Type*} [Fintype I] [Fintype J]

/-- Build the injective positive catalogue alignment from the six native words
of each row. Geometry can have been loaded before the terminal width scans. -/
def Board.reportAlignment (b : Board) (rows : Fin b.rows→Row) (m : Memory w)
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marks : Marks h W k attempts)
    (M : ℕ) (fixed : Fin b.rows→ℕ) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (acquired : Bought S π depth marks→Fin b.boughtRows)
    (coreReads : ∀j : Fin b.coreRows,Reads (rows (b.coreIndex j)) (b.core.view m (j.val:Word w))
      (b.idBase+(b.coreIndex j).val))
    (boughtReads : ∀j : Fin b.boughtRows,Reads (rows (b.boughtIndex j)) (b.bought.view m (j.val:Word w))
      (b.idBase+(b.boughtIndex j).val))
    (coreAt : ∀j,Located S π depth marks M (b.core.view m (j.val:Word w)) (.inl (order j)))
    (support : ∀j,0<fixed (b.boughtIndex j)→b.bought.flag.eval m (j.val:Word w)≠0)
    (boughtAt : ∀j,b.bought.flag.eval m (j.val:Word w)≠0 →
      ∃p : Bought S π depth marks,acquired p=j ∧ Located S π depth marks M (b.bought.view m (j.val:Word w)) (.inr p)) :
    Alignment b S π depth marks M rows fixed (b.original S π depth marks order acquired) := by
  let name:=b.original S π depth marks order acquired
  have atSite (i : {i : Fin b.rows // 0<fixed i}) : ∃e : Catalogue S π depth marks,name e=i.val ∧
      ∃flip : Bool,let ends:=actualEnds S π depth marks e
        (rows i.val).endpoint=(siteNumber h (2^W) k (if flip then ends.2 else ends.1)).val ∧
        (rows i.val).opposite=(siteNumber h (2^W) k (if flip then ends.1 else ends.2)).val ∧
        (rows i.val).lengthCode=lenCode S π depth marks M e := by
    rcases b.split_index i.val with ⟨j,eq⟩|⟨j,eq⟩
    · refine ⟨.inl (order j),?_,?_⟩
      · change b.coreIndex (order.symm (order j))=i.val
        exact (congrArg b.coreIndex (order.symm_apply_apply j)).trans eq
      · rw [←eq]
        exact (coreAt j).sorted (coreReads j)
    · have used : 0<fixed (b.boughtIndex j) := eq.symm ▸ i.property
      obtain ⟨p,ord,loc⟩:=boughtAt j (support j used)
      refine ⟨.inr p,?_,?_⟩
      · exact (congrArg b.boughtIndex ord).trans eq
      · rw [←eq]
        exact loc.sorted (boughtReads j)
  choose edge original flip word using atSite
  have inj : Function.Injective edge := fun x y eq=>
    Subtype.ext ((original x).symm.trans ((congrArg name eq).trans (original y)))
  have joins (i : {i : Fin b.rows // 0<fixed i}) :
      let ends:=actualEnds S π depth marks (edge i)
      let a:=(siteNumber h (2^W) k ends.1).val
      let z:=(siteNumber h (2^W) k ends.2).val
      ((rows i.val).endpoint=a ∧ (rows i.val).opposite=z) ∨
      ((rows i.val).endpoint=z ∧ (rows i.val).opposite=a) := by
    dsimp only
    cases hf : flip i with
    | false => exact Or.inl (by simpa only [hf,Bool.false_eq_true,ite_false] using And.intro (word i).1 (word i).2.1)
    | true => exact Or.inr (by simpa only [hf,ite_true] using And.intro (word i).1 (word i).2.1)
  exact ⟨⟨edge,inj⟩,original,joins,fun i=>(word i).2.2⟩

def Board.locatedInjection (b : Board) (banks : RouteSettlement.Banks) (source table destination : ℕ)
    (owners : Bank) (m : Memory w) {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marks : Marks h W k attempts)
    (M : ℕ) (fixed : Fin b.rows→ℕ) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (acquired : Bought S π depth marks→Fin b.boughtRows)
    (room : b.idBase+b.rows<2^w) (wide : 1<2^w)
    (fits : ∀f : Fin 7,f≠4→(b.geometry f).Fits w banks.width.base) (space : banks.width.base+b.rows≤ source)
    (coreAt : ∀j,Located S π depth marks M (b.core.view m (j.val:Word w)) (.inl (order j)))
    (support : ∀j,0<fixed (b.boughtIndex j)→b.bought.flag.eval m (j.val:Word w)≠0)
    (boughtAt : ∀j,b.bought.flag.eval m (j.val:Word w)≠0 →
      ∃p : Bought S π depth marks,acquired p=j ∧ Located S π depth marks M (b.bought.view m (j.val:Word w)) (.inr p)) :
    Alignment b S π depth marks M ((b.sink r banks source table destination owners).terminalRows m enum ci cj)
      fixed (b.original S π depth marks order acquired) :=
  b.reportAlignment _ m S π depth marks M fixed order acquired
    (fun j=>b.core_reads banks source table destination owners m enum ci cj j room fits space)
    (fun j=>b.bought_reads banks source table destination owners m enum ci cj j room wide fits space)
    coreAt support boughtAt

end
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
