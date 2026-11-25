import OAI.LinearAlgebra.SpectralBooks.CompleteMapLabelsPartition
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsPatch
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsStarEncoding

/-! # The unique, logarithmic-size local certificate for spherical maps

This is the map-labels lemma of the sharp planar restriction paper. The
vertex and edge predicates are fixed for the entire sum over maps. The
port positions at the two ends retain both incidences of a loop.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarCertSize PlanarPatch

universe u v

/-- Full certificate alphabet at cap `N` and patch-size cutoff `K`. -/
abbrev Label (N K : ℕ) := PortView (BaseAlphabet N) (2*K+2)

/-- The common predicate on a full view. -/
def viewTest {N : ℕ} (K : ℕ) (ε : ℝ) (z : Label N K) : Prop :=
  starTest (PortView.shorten (show 1 ≤ 2*K+2 by omega) z) ∧ patchValid K ε z

/-- The vertex predicate sees only the type and label. The edge predicate
sees the two endpoint slots and labels. -/
def tests (N K : ℕ) (ε : ℝ) : MapLabelTests (Label N K) :=
  MapLabelTests.views (2*K+1) (viewTest K ε)

def vertexName {N K : ℕ} (z : Label N K) : ℕ := vertexVal z.1 .preorderName
def patchName {N K : ℕ} (z : Label N K) : ℕ := vertexVal z.1 .patchName

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
variable (M : RootedMap V E) {N K : ℕ} {ε : ℝ}

/-- A passing label assignment is exactly the full encoding of a checked
certificate. This correspondence includes all padding and suffix fields. -/
theorem pass_iff_encode (hN : 1 ≤ N) (z : V → Label N K) :
    (tests N K ε).Pass M z ↔ ∃ c : RootedMap.Certificate V E, ∃ h : M.CertificateChecks N K ε c,
      z = PortView.actual M.slots (M.encodeBase hN h) (2*K+2) := by
  rw [tests, MapLabelTests.pass_views_iff]
  constructor
  · rintro ⟨hz,hv⟩
    let b := fun v => (z v).1
    have he : z = PortView.actual M.slots b (2*K+2) := hz
    have ht : TypesAgree M b := fun v => (hv v).2
    have hs (v : V) : starTest (PortView.actual M.slots b 1 v) := by
      have h := (hv v).1.1
      rw [he, PortView.shorten_actual] at h
      exact h
    obtain ⟨hn,hcheck⟩ := unpack_checked M b ht hs
    have hp := (patchValid_actual_iff M b hn.name_injective K ε).mp
      (fun v => he ▸ (hv v).1.2)
    have hc := hcheck K ε hp
    exact ⟨unpack M b, hc, by rw [encode_unpack_eq M b hN ht hs hc]; exact he⟩
  · rintro ⟨c,h,rfl⟩
    let b := M.encodeBase hN h
    have hp := (patchValid_actual_iff M b h.tree.name_injective K ε).mpr h.patches
    refine ⟨rfl,fun v => ⟨⟨?_,hp v⟩,rfl,rfl⟩⟩
    change starTest (PortView.shorten _ (PortView.actual M.slots b (2*K+2) v))
    rw [PortView.shorten_actual]
    exact encode_starTest M hN h v

/-- The patch identifier and vertex name are visible at the center of every view. -/
theorem pass_partition (hN : 1 ≤ N) (z : V → Label N K) (hz : (tests N K ε).Pass M z)
    (hcand : M.HasCandidates K ε) :
    Function.Injective (fun v => vertexName (z v)) ∧
    (∀ v, Connected M.graph.tail M.graph.head (RootedMap.patchFiber (fun x => patchName (z x)) v) ∧
      (RootedMap.patchFiber (fun x => patchName (z x)) v).card ≤ K) ∧
    ((Finset.univ.filter (fun e : E => patchName (z (M.graph.tail e)) ≠
        patchName (z (M.graph.head e)))).card : ℝ) ≤ ε * Fintype.card V := by
  obtain ⟨c,h,rfl⟩ := (pass_iff_encode M hN z).mp hz
  exact ⟨h.tree.name_injective, h.partition M hcand⟩

variable [DecidableEq E]

/-- A passing label forces the vertex cap and the exact genus-zero condition. -/
theorem pass_member (hN : 1 ≤ N) (z : V → Label N K) (hz : (tests N K ε).Pass M z) :
    Fintype.card V ≤ N ∧ M.Spherical := by
  obtain ⟨_,h,_⟩ := (pass_iff_encode M hN z).mp hz
  exact h.member M

/-- On a member of the family, even the numerical records and their padded
views admit exactly one assignment. -/
theorem existsUnique_passing (hN : 1 ≤ N) (hs : M.Spherical) (hcap : Fintype.card V ≤ N)
    (hcand : M.HasCandidates K ε) : ∃! z : V → Label N K, (tests N K ε).Pass M z := by
  obtain ⟨c,h,hu⟩ := M.existsUnique_certificate hcap hs hcand
  refine ⟨_,(pass_iff_encode M hN _).mpr ⟨c,h,rfl⟩,fun y hy => ?_⟩
  obtain ⟨c',h',rfl⟩ := (pass_iff_encode M hN y).mp hy
  cases hu c' h'
  rfl

/-- Sharp map-labels lemma. The patch bound depends only on the positive edge
budget. The verifier is uniform over all finite connected rooted port graphs,
and the logarithmic bit bound applies to its entire label. -/
theorem map_labels (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N : ℕ, 1 ≤ N →
      Nonempty (Label N K ↪ (Fin ((80*5^(2*K+2))*Nat.clog 2 (2*N)) → Bool)) ∧
      ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (M : RootedMap V E),
        ((∃ z, (tests N K ε).Pass M z) ↔ Fintype.card V ≤ N ∧ M.Spherical) ∧
        (Fintype.card V ≤ N → M.Spherical → ∃! z, (tests N K ε).Pass M z) ∧
        ∀ z, (tests N K ε).Pass M z →
          Function.Injective (fun v => vertexName (z v)) ∧
          (∀ v, Connected M.graph.tail M.graph.head (RootedMap.patchFiber (fun x => patchName (z x)) v) ∧
            (RootedMap.patchFiber (fun x => patchName (z x)) v).card ≤ K) ∧
          ((Finset.univ.filter (fun e : E => patchName (z (M.graph.tail e)) ≠
            patchName (z (M.graph.head e)))).card : ℝ) ≤ ε * Fintype.card V := by
  obtain ⟨K,hK⟩ := uniform_spherical_candidates.{u,v} ε hε
  refine ⟨K,fun N hN => ⟨exists_full_view_encoding hN K,?_⟩⟩
  intro V E _ _ _ _ M
  have cand (hs : M.Spherical) : M.HasCandidates K ε :=
    hK V E M.graph M.num.rotation (underlying_connected_of_connectedFrom _ _ M.connected) hs M.degree
  have uniq (hcap : Fintype.card V ≤ N) (hs : M.Spherical) := existsUnique_passing M hN hs hcap (cand hs)
  exact ⟨⟨fun ⟨z,hz⟩ => pass_member M hN z hz, fun ⟨hcap,hs⟩ => (uniq hcap hs).exists⟩,uniq,
    fun z hz => pass_partition M hN z hz (cand (pass_member M hN z hz).2)⟩

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
