import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMap
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarCanonicalPartition
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarFaceTotals
import OAI.LinearAlgebra.SpectralBooks.PlanarCertSize.PlanarLabelFields

/-! # Canonical records for rooted, numbered maps

The root-size and Euler checks use the very same tree as the preorder
certificate. Face minima are ordered by the certified names and the
actual port numbers. The patch records are indexed by those names.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.RootedMap

open PlanarPatch PlanarCertSize
universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
variable (M : RootedMap V E)

/-- Embed the consecutive port numbers in the four-slot alphabet. -/
def slots : M.graph.FourPortNumbering :=
  fun v => (M.num v).toEmbedding.trans (Fin.castLEEmb (M.degree v))

/-- The tree uses the same order as the local tensor ports. -/
def slotNat (v : V) (p : M.graph.Port v) : ℕ := (M.num v p).val

theorem slotNat_injective (v : V) : Function.Injective (M.slotNat v) :=
  fun _ _ h => (M.num v).injective (Fin.ext h)

abbrev NameChecks (rec : TreeNameRecord V) :=
  TreeNameChecks M.graph M.root M.slotNat M.slotNat_injective rec

/-- All fields before replacing the face-minimum dart by its two integer coordinates. -/
@[ext] structure Certificate (V E : Type*) extends TreeNameRecord V where
  face : E × Bool → (E × Bool) × ℕ
  edges : V → ℕ
  faces : V → ℕ
  patch : V → ℕ × ℕ

variable [DecidableEq E]

/-- Tests on the unpacked records, with a single certified preorder shared by
the face, subtree, and patch checks. -/
structure CertificateChecks (N K : ℕ) (ε : ℝ) (c : Certificate V E) : Prop where
  tree : M.NameChecks c.toTreeNameRecord
  cap : c.size M.root ≤ N
  face : letI := M.graph.namedPortOrder ⟨c.name, tree.name_injective⟩ M.slots
         PlanarFace.Valid M.num.rotation.picture.face c.face
  edges : SubtreeTotals M.root
    (canonicalParent M.graph M.slotNat M.slotNat_injective tree.distances)
    (edgeWeight M.graph) c.edges
  faces : letI := M.graph.namedPortOrder ⟨c.name, tree.name_injective⟩ M.slots
          SubtreeTotals M.root
            (canonicalParent M.graph M.slotNat M.slotNat_injective tree.distances)
            (faceWeight M.graph c.face) c.faces
  euler : (c.size M.root : ℤ) - c.edges M.root + observedFaces M.graph M.root (c.faces M.root) = 2
  patches : RecordsValid ⟨c.name, tree.name_injective⟩
    (candidatesOn M.graph.tail M.graph.head K ε) Finset.univ N c.patch

theorem CertificateChecks.member {N K : ℕ} {ε : ℝ} {c : Certificate V E}
    (h : M.CertificateChecks N K ε c) : Fintype.card V ≤ N ∧ M.Spherical := by
  let := M.graph.namedPortOrder ⟨c.name, h.tree.name_injective⟩ M.slots
  exact ⟨h.tree.size_root ▸ h.cap,
    (rootEuler_iff_genusZero M.graph M.num.rotation
      (underlying_connected_of_connectedFrom _ _ M.connected) h.face h.tree.sizes h.edges h.faces).mp h.euler⟩

/-- The separator supplies a single patch bound for all sizes and maps. -/
def HasCandidates (K : ℕ) (ε : ℝ) : Prop :=
  ∀ R : Finset V, R.Nonempty → ∃ P, Candidate M.graph.tail M.graph.head K ε R P

omit [DecidableEq E] in
theorem CertificateChecks.unique {N K : ℕ} {ε : ℝ} (hcand : M.HasCandidates K ε)
    {c c' : Certificate V E} (h : M.CertificateChecks N K ε c) (h' : M.CertificateChecks N K ε c') :
    c = c' := by
  rcases c with ⟨a, f, e, b, p⟩
  rcases c' with ⟨a', f', e', b', p'⟩
  obtain rfl : a' = a := (existsUnique_treeNameRecord _ _ _ _ M.connected).unique h'.tree h.tree
  let := M.graph.namedPortOrder ⟨a'.name, h.tree.name_injective⟩ M.slots
  obtain rfl : f' = f := funext fun d => (h'.face.eq_canonical d).trans (h.face.eq_canonical d).symm
  have depth := canonicalParent_depth_lt M.graph M.slotNat M.slotNat_injective h.tree.distances
  obtain rfl : e' = e := (existsUnique_subtreeTotals M.root _ _ _ depth).unique h'.edges h.edges
  obtain rfl : b' = b := (existsUnique_subtreeTotals M.root _ _ _ depth).unique h'.faces h.faces
  obtain rfl : p' = p := funext fun x => recordsValid_unique _ _
    (fun _ _ h => ⟨(mem_candidatesOn.mp h).1, (mem_candidatesOn.mp h).2.1⟩)
    (fun _ hR => let ⟨P,hP⟩ := hcand _ hR; ⟨P, mem_candidatesOn.mpr hP⟩)
    h'.patches h.patches x (Finset.mem_univ x)
  rfl

/-- A spherical map under the size cap has exactly one simultaneous solution
of the tree, face, Euler, and removal-round equations. -/
theorem existsUnique_certificate {N K : ℕ} {ε : ℝ} (hN : Fintype.card V ≤ N)
    (hs : M.Spherical) (hcand : M.HasCandidates K ε) :
    ∃! c, M.CertificateChecks N K ε c := by
  obtain ⟨a, ht, -⟩ := existsUnique_treeNameRecord M.graph M.root M.slotNat M.slotNat_injective M.connected
  let key : V ↪ ℕ := ⟨a.name, ht.name_injective⟩
  let := M.graph.namedPortOrder key M.slots
  let φ := M.num.rotation.picture.face
  let f := fun d => (PlanarFace.leastPort φ d, PlanarFace.forwardDistance φ d)
  have hf : PlanarFace.Valid φ f := PlanarFace.canonical_valid φ
  have hd := canonicalParent_depth_lt M.graph M.slotNat M.slotNat_injective ht.distances
  obtain ⟨e, he, -⟩ := existsUnique_subtreeTotals M.root _ _ (edgeWeight M.graph) hd
  obtain ⟨b, hb, -⟩ := existsUnique_subtreeTotals M.root _ _ (faceWeight M.graph f) hd
  obtain ⟨p, hp⟩ := exists_recordsValid key (candidatesOn M.graph.tail M.graph.head K ε)
    (fun _ _ h => ⟨(mem_candidatesOn.mp h).1, (mem_candidatesOn.mp h).2.1⟩)
    (fun _ hR => let ⟨P,hP⟩ := hcand _ hR; ⟨P, mem_candidatesOn.mpr hP⟩)
    (show (Finset.univ : Finset V).card ≤ N by simpa using hN)
  let c : Certificate V E := ⟨a, f, e, b, p⟩
  have hc : M.CertificateChecks N K ε c :=
    ⟨ht, ht.size_root.trans_le hN, hf, he, hb,
      (rootEuler_iff_genusZero M.graph M.num.rotation
        (underlying_connected_of_connectedFrom _ _ M.connected) hf ht.sizes he hb).mpr hs, hp⟩
  exact ⟨c, hc, fun _ h => h.unique M hcand hc⟩

end PortGraph.RootedMap

end

end SpectralBooks
end LinearAlgebra
end OAI
