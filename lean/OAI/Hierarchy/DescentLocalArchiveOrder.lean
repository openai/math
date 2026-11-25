import OAI.Hierarchy.DescentOriginalNodeCapacity
import OAI.Hierarchy.DescentNodeLocalEnumeration
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentResetLocalNodes
import OAI.Hierarchy.DescentOrdinaryLocalBirth

namespace OAI
/-! # The local scalar directory on the selected branch -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentSharedCableNames
open DescentStageEdgeReceipt DescentPhysicalOrder DescentInitialHost Catalyst DescentRotor
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}


variable {J V I : Type} [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V] [Fintype I]
variable {price ε : ℝ} {k age : ℕ} (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
    (S : AtomSchedule) (ready : A.StateBounds S age) (B : BitDescription W) (o : Local B)
    (pick : I×Fin 2↪W.graph.Edge) (used : ∀i,pick (i,0)∈W.core)

variable (sites : W.graph.Site ↪ Fin (Fintype.card W.graph.Site))

def donorEntry : NodeOrder.All B ⊕ (I×Fin 6) ↪
    Fin (Fintype.card W.graph.Site) × Fin (maxNodes B + A.cap*6) where
  toFun
    | .inl ⟨v,u⟩=>(sites v,finSumFinEquiv (.inl (bounded B o v u)))
    | .inr (i,j)=>(sites (W.graph.src (pick (i,0))),
      finSumFinEquiv (.inr (finProdFinEquiv
        (Stage.outgoing A native S ready ⟨pick (i,0),A.quantum_positive _ (used i)⟩,j))))
  inj' := by
    rintro (⟨v,u⟩|⟨i,j⟩) (⟨v',u'⟩|⟨i',j'⟩) eq
    · have same:= sites.injective (congrArg Prod.fst eq)
      subst v'
      exact congrArg (fun x=>(Sum.inl ⟨v,x⟩ : NodeOrder.All B ⊕ (I×Fin 6))) ((bounded B o v).injective
        (Sum.inl.inj (finSumFinEquiv.injective (congrArg Prod.snd eq))))
    · have clash := finSumFinEquiv.injective (congrArg Prod.snd eq)
      cases clash
    · have clash := finSumFinEquiv.injective (congrArg Prod.snd eq)
      cases clash
    · have same := sites.injective (congrArg Prod.fst eq)
      have pair := finProdFinEquiv.injective (Sum.inr.inj (finSumFinEquiv.injective (congrArg Prod.snd eq)))
      have edges := Stage.outgoing_identify A native S ready _ _ same (congrArg Prod.fst pair)
      have ip : i=i' := congrArg Prod.fst (pick.injective (congrArg Subtype.val edges))
      have jp : j=j' := congrArg Prod.snd pair
      subst i';subst j';rfl

def donorKey : NodeOrder.All B ⊕ (I×Fin 6) ↪ ℕ :=
  (donorEntry A native S ready B o pick used sites).trans (finProdFinEquiv.toEmbedding.trans Fin.valEmbedding)

variable {u q : ℝ} {S} {i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "next" => Archive.bit (OrdinaryLink.advance ticket arch)

def roots : NodeOrder.All next ≃ NodeOrder.All arch.bit ⊕ ((r).pairs×Fin 6) :=
  (NodeOrder.followNames n _).trans ((NodeOrder.castNames ((r).state c).symm _).trans
    (NodeOrder.selectedNames arch.bit G (r).pick (fun _=>T.z) (fun _=>T.unitPos)
      (r).fit (fun _=>le_refl T.z) (r).pack ((r).profile c)))

def ordinaryKey (previous : Local arch.bit) (v : n.result.graph.Site) : ((next).recipe v).Node↪ℕ :=
  (Function.Embedding.sigmaMk v).trans ((roots ticket arch).toEmbedding.trans
    (donorKey cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid arch.bit previous (r).pick
      (fun j=>(r).picked (j,0)) (cap.placement.site cap.vertex cap.valid.coordinates)))

def advance (previous : Local arch.bit) : Local next := fun v=>physical (ordinaryKey ticket arch previous v)

theorem advance_read (previous : Local arch.bit) (v : n.result.graph.Site) (node : ((next).recipe v).Node) :
    (advance ticket arch previous v node).val =
      (Finset.univ.filter (fun t=>ordinaryKey ticket arch previous v t < ordinaryKey ticket arch previous v node)).card :=
  physical_val _ _

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
