import OAI.Hierarchy.ProbePurchaseSockets
import OAI.Hierarchy.ProbeReportSockets
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Positive reported links in the fixed supergroup table -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open AdaptiveProbe TaggedShorterSupergroups
open scoped Classical

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
abbrev Marks (h W k attempts : ℕ) := Fin attempts → StageAt h (2^W) →
  (Fin k × Bool) → Finset (Fin (2^h))
variable (marked : Marks h W k attempts)
abbrev Exclusive (marked : Marks h W k attempts) :=
  ∀ a t c c' p,p∈marked a t c → p∈marked a t c' → c=c'
variable (unique : Exclusive marked)

abbrev Core (h W k : ℕ) := (StageAt h (2^W) × Fin (2^h)) × ColumnLayer k
abbrev Bought := Σ a : Fin attempts, LiveChains S π depth (marked a)
abbrev Row := Core h W k ⊕ Bought S π depth marked

def coreSite : Core h W k × Bool ↪ StageColumns h (2^W) × ColumnLayer k where
  toFun := fun (((t,p),l),s) => (⟨t,occupiedStagePort π t (p,s)⟩,l)
  inj' := by
    rintro ⟨⟨⟨t,p⟩,l⟩,s⟩ ⟨⟨⟨u,q⟩,m⟩,v⟩ same
    have sites := congrArg Prod.fst same
    obtain ⟨rfl,ports⟩ := Sigma.mk.inj_iff.mp sites
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj ((occupiedStagePort π t).injective (eq_of_heq ports))
    have layers : l=m := congrArg Prod.snd same
    subst m; rfl

def boughtSite : Bought S π depth marked × Bool ↪ StageColumns h (2^W) × Fin attempts where
  toFun := fun (⟨a,p⟩,s) => (purchaseSockets S π depth (marked a) (unique a) (p,s),a)
  inj' := by
    rintro ⟨⟨a,p⟩,s⟩ ⟨⟨b,q⟩,v⟩ same
    have attempt : a=b := congrArg Prod.snd same
    subst b
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj <|
      (purchaseSockets S π depth (marked a) (unique a)).injective (congrArg Prod.fst same)
    rfl

/-- The immutable address of a core tile includes its layer. A bought link
uses the actual initial inlet and the final outlet in its own attempt. -/
def locate : Row S π depth marked × Bool ↪ StageColumns h (2^W) × Role k attempts :=
  ((Equiv.sumProdDistrib (Core h W k) (Bought S π depth marked) Bool).toEmbedding.trans
    ((coreSite π).sumMap (boughtSite S π depth marked unique))).trans
    (Equiv.prodSumDistrib (StageColumns h (2^W)) (ColumnLayer k) (Fin attempts)).symm.toEmbedding

theorem same_group (r : Row S π depth marked) :
    owner (locate S π depth marked unique (r,false)).1 =
      owner (locate S π depth marked unique (r,true)).1 := by
  rcases r with ⟨⟨t,p⟩,l⟩|⟨a,p⟩
  · rfl
  · change owner (purchaseSockets S π depth (marked a) (unique a) (p,false)) =
      owner (purchaseSockets S π depth (marked a) (unique a) (p,true))
    rw [purchaseSockets_in,purchaseSockets_out]
    rfl

variable {H : ℕ} (dir : Directory (reserved h W (copies k attempts)) H)

/-- Both endpoint roles can be reoriented in the native emission. The
embedding even distinguishes the two ends of each represented original row. -/
def placed : Row S π depth marked × Bool ↪ Fin dir.groups × Fin H :=
  (locate S π depth marked unique).trans (packed dir)

theorem placed_group (r : Row S π depth marked) (s : Bool) :
    (placed S π depth marked unique dir (r,s)).1 =
      (placed S π depth marked unique dir (r,false)).1 := by
  cases s
  · rfl
  · exact congrArg dir.group (same_group S π depth marked unique r).symm

/-- Any observed positive sublist gets the same public endpoint ordinals.
Only the identification with the original active input row is needed. -/
def reported {I : Type*} (actual : I ↪ Row S π depth marked) (side : I → Bool) :
    I ↪ Fin dir.groups × Fin H where
  toFun i := placed S π depth marked unique dir (actual i,side i)
  inj' := by
    intro i j eq
    have full := (placed S π depth marked unique dir).injective eq
    have rows := congrArg Prod.fst full
    exact actual.injective rows

open ProtocolRAMReportedPorts in
theorem portDistinct {n : ℕ} (rows : Fin n → ProtocolRAMEmit.Row) (w m γ : ℕ)
    (actual : {i : Fin n // 0<pieces rows w i} ↪ Row S π depth marked)
    (side : Fin n → Bool) (port : Fin n → Fin H)
    (groupWord : ∀ i : {v : Fin n // 0<pieces rows w v},(rows i.val).group =
      (placed S π depth marked unique dir (actual i,false)).1.val)
    (portWord : ∀ i : {v : Fin n // 0<pieces rows w v},port i.val = (placed S π depth marked unique dir (actual i,side i.val)).2)
    (g : Fin dir.groups) : Tagged.WideStack.PortDistinct rows w m γ g.val port := by
  apply Tagged.WideStack.portDistinct_of_grouped rows w m γ port
    (reported S π depth marked unique dir actual (fun i=>side i.val))
  · intro i
    exact (congrArg Fin.val (placed_group S π depth marked unique dir (actual i) (side i.val))).trans
      (groupWord i).symm
  · exact fun i=>(portWord i).symm

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
