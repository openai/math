import OAI.Hierarchy.DescentCommonHostEdges
import OAI.Hierarchy.DescentResetAtomLedger

namespace OAI
/-! # Every post-reset physical edge reads a common degree-three host edge -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentResetAttachments DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P H Q X : Type} [Field F] [Fintype H] [Fintype Q] {n d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w)) (tab : R.Tables F)
local notation "M" => install A home group hub same R tab

omit [Fintype Q] in
theorem read_common_incidence (site : ((Bool×H)⊕R.Site)→X) (rel : X→X→Prop)
    (old : ∀s i,rel (site (.inl (s,home (ends A.graph s i)))) (site (.inr (R.attach (s,group s i)))))
    (join : ∀z,rel (site (.inl (false,z))) (site (.inl (true,z))))
    (hardware : ∀e,rel (site (.inr (R.src e))) (site (.inr (R.dst e)))) :
    ∀e : (M).graph.Edge,
      rel (site (installedNames A home group hub same R tab ((M).graph.src e)))
        (site (installedNames A home group hub same R tab ((M).graph.dst e))) := by
  subst w
  rintro (⟨s,i⟩|z|e)
  · exact old s i
  · exact join z
  · exact hardware e
end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetAttachments DescentChosenRouter DescentCommonHost DescentRelativeContacts
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "L" => Z.placement
local notation "m" => T.commonDepth
local notation "view" => bankNode L Z.graph m T.code Z.positive Z.pay Z.circuit d
local notation "lab" => fun t=>shortName m (T.code t)
local notation "adj" => DescentCommonHost.near L Z.graph m T.code
local notation "X" => Node Z.V (Z.V×DescentContacts.Endpoint (2^Z.n)) (Computability.BorderVNP.Crossing.Network.Site (DescentCommonPalette.rotor Z.graph))

def commonName : (W).graph.Site→X :=
  (Sum.elim (fun st=>.trunk st.1 (lab st.2)) view) ∘ resetNames Z T

theorem common_edges (e : (W).graph.Edge) :
    commonName Z T ((W).graph.dst e)∈adj (commonName Z T ((W).graph.src e)) ∧
    commonName Z T ((W).graph.src e)∈adj (commonName Z T ((W).graph.dst e)) := by
  let read : (Bool×Z.Fallback)⊕Z.bank.Site→X := Sum.elim (fun st=>.trunk st.1 (lab st.2)) view
  apply read_common_incidence A T.home (L).input T.hub (funext fun i=>(Z.allWidths i).symm) Z.bank Z.tables read
    (fun x y=>y∈adj x ∧ x∈adj y) _ _ _ e
  · intro s i
    have fan := public_mem L Z.graph m T.code T.fallbackCoherent s ((L).input s i)
    have name := public_read L T.code T.source s i
    rw [←T.attach] at name
    let trunk : X := .trunk s (lab (T.home (ends A.graph s i)))
    have incidence (v : X) (atPublic : v = publicNode L Z.graph m T.code s ((L).input s i)) :
        v ∈ adj trunk ∧ trunk ∈ adj v := by
      subst v
      simpa only [trunk, name] using fan
    exact incidence (view (Z.bank.attach (s,(L).input s i)))
      (publicNode_at L Z.graph m T.code Z.positive Z.pay Z.circuit d s ((L).input s i))
  · intro z
    exact ⟨Finset.mem_insert_self ..,Finset.mem_insert_self ..⟩
  · exact internal_mem L Z.graph m T.code Z.positive Z.pay Z.circuit d T.joined T.fallbackCoherent

/-- Restrict the common template to names realized by some concrete site.
Symmetrization retains every physical edge. -/
def commonNames : Finset X := Finset.univ.image (commonName Z T)
def placed (v : (W).graph.Site) : ↥(commonNames Z T) :=
  ⟨commonName Z T v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩
def commonNear (x : ↥(commonNames Z T)) : Finset ↥(commonNames Z T) :=
  Finset.univ.filter (fun y=>y.val∈adj x.val ∧ x.val∈adj y.val)

theorem common_degree (x : ↥(commonNames Z T)) : (commonNear Z T x).card≤3 := by
  have sub : (commonNear Z T x).map (Function.Embedding.subtype _) ⊆ adj x.val := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hy
    exact (Finset.mem_filter.mp hz).2.1
  simpa only [Finset.card_map] using (Finset.card_le_card sub).trans (DescentCommonHost.degree L Z.graph m T.code x.val)

theorem common_symmetric (x y : ↥(commonNames Z T)) : y∈commonNear Z T x ↔ x∈commonNear Z T y := by
  simp [commonNear,and_comm]

theorem placed_edges (e : (W).graph.Edge) : placed Z T ((W).graph.dst e)∈commonNear Z T (placed Z T ((W).graph.src e)) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,common_edges Z T e⟩

/-- All incidences in the physical reset graph, including zero-width wires and
both orientations. This is the degree-three aperture emitted to the next epoch. -/
def emittedNear (x : ↥(commonNames Z T)) : Finset ↥(commonNames Z T) :=
  Finset.univ.filter (fun y=>∃e:(W).graph.Edge,
    (placed Z T ((W).graph.src e)=x ∧ placed Z T ((W).graph.dst e)=y) ∨
    (placed Z T ((W).graph.dst e)=x ∧ placed Z T ((W).graph.src e)=y))

theorem emitted_sub (x : ↥(commonNames Z T)) : emittedNear Z T x ⊆ commonNear Z T x := by
  intro y yes
  rcases (Finset.mem_filter.mp yes).2 with ⟨e,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
  · exact placed_edges Z T e
  · exact (common_symmetric Z T _ _).mp (placed_edges Z T e)

theorem emitted_degree (x : ↥(commonNames Z T)) : (emittedNear Z T x).card≤3 :=
  (Finset.card_le_card (emitted_sub Z T x)).trans (common_degree Z T x)

theorem emitted_symmetric (x y : ↥(commonNames Z T)) : y∈emittedNear Z T x ↔ x∈emittedNear Z T y := by
  simp only [emittedNear,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor <;> rintro ⟨e,⟨a,b⟩|⟨a,b⟩⟩
  · exact ⟨e,Or.inr ⟨b,a⟩⟩
  · exact ⟨e,Or.inl ⟨b,a⟩⟩
  · exact ⟨e,Or.inr ⟨b,a⟩⟩
  · exact ⟨e,Or.inl ⟨b,a⟩⟩

theorem emitted_edges (e : (W).graph.Edge) :
    placed Z T ((W).graph.dst e)∈emittedNear Z T (placed Z T ((W).graph.src e)) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,Or.inl ⟨rfl,rfl⟩⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
