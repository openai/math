import OAI.LinearAlgebra.SpectralBooks.PlanarFace.PlanarFaceCertificate
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarTreeNames
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchCertificates
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortViews

/-! # Size of the base fields in the map certificate

The base data at each vertex consist of its type, eight integers, and three
integers for each of its four port positions. The port positions beyond its
degree have fixed zero fields. Counting all possible padded records gives an
upper bound on the number of base labels even before the local tests run.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarCertSize

open PlanarPatch

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Degree counts ports, so each loop contributes twice. -/
theorem card_ports_le (G : PortGraph V E) {N : ℕ} (hv : Fintype.card V ≤ N)
    (hdeg : ∀ v, Fintype.card (G.Port v) ≤ 4) : Fintype.card (E × Bool) ≤ 4*N := by
  calc
    Fintype.card (E × Bool) = Fintype.card ((v : V) × G.Port v) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv fun p : E × Bool => G.vertex p.1 p.2)).symm
    _ = ∑ v, Fintype.card (G.Port v) := Fintype.card_sigma
    _ ≤ ∑ _ : V, 4 := Finset.sum_le_sum fun v _ => hdeg v
    _ ≤ 4*N := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right 4 hv

theorem card_edges_le (G : PortGraph V E) {N : ℕ} (hv : Fintype.card V ≤ N)
    (hdeg : ∀ v, Fintype.card (G.Port v) ≤ 4) : Fintype.card E ≤ 2*N := by
  have h := card_ports_le G hv hdeg
  simp only [Fintype.card_prod, Fintype.card_bool] at h
  omega

omit [Fintype E] [DecidableEq V] in
/-- An accepted root-distance field is strictly less than the number of vertices. -/
theorem distance_lt_card {G : SimpleGraph V} {r : V} {d : V → ℕ}
    (hG : G.Connected) (hd : DistanceChecks G r d) (v : V) : d v < Fintype.card V := by
  obtain ⟨p,hp⟩ := hG.exists_isPath v r
  rw [hd.eq_dist]
  exact (G.dist_le p).trans_lt hp.length_lt

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The patch name is a vertex name or the fixed zero for unused fields. -/
theorem leastName_le (key : V ↪ ℕ) {N : ℕ} (hk : ∀ v, key v ≤ N) (P : Finset V) :
    leastName key P ≤ N := by
  by_cases hp : P.Nonempty
  · obtain ⟨v,hv⟩ := hp.exists_mem
    simpa [leastName, hp] using
      (Finset.min'_le (P.map key) (key v) (Finset.mem_map.mpr ⟨v,hv,rfl⟩)).trans (hk v)
  · simp [leastName, hp]

omit [Fintype V] [Fintype E] in
/-- Both integers in an accepted partition report are at most the vertex cap. -/
theorem patchRecord_le (key : V ↪ ℕ) (C : Finset V → Finset (Finset V))
    {N : ℕ} {R : Finset V} {rec : V → ℕ × ℕ} (hk : ∀ v, key v ≤ N)
    (hc : RecordsValid key C R N rec) {v : V} (hv : v ∈ R) :
    (rec v).1 ≤ N ∧ (rec v).2 ≤ N := by
  have hpos := (hc.1 v hv).1
  obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hcheck := hc.2 v hv t (by omega)
  obtain ⟨P, hP, hin⟩ := hcheck.1.mp ht
  exact ⟨(hc.1 v hv).2, (hcheck.2 P hP hin).trans_le (leastName_le key hk P)⟩

/-- Each face's forward-distance field is bounded by the number of darts.
This includes faces traversing repeated vertices. -/
theorem faceDistance_le (G : PortGraph V E) [LinearOrder (E × Bool)]
    {N : ℕ} (hv : Fintype.card V ≤ N) (hdeg : ∀ v, Fintype.card (G.Port v) ≤ 4)
    (φ : Equiv.Perm (E × Bool)) {record : E × Bool → (E × Bool) × ℕ}
    (hc : PlanarFace.Valid φ record) (p : E × Bool) : (record p).2 ≤ 4*N := by
  rw [hc.eq_canonical]
  exact (PlanarFace.forwardDistance_lt_card φ p).le.trans (card_ports_le G hv hdeg)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The port's recorded minimum is itself a real dart. Its coordinates in
a valid naming therefore satisfy the same cap as every vertex and port name. -/
theorem leastPort_coordinates_le (G : PortGraph V E) (key : V ↪ ℕ) {N : ℕ}
    (hk : ∀ v, key v ≤ N) (number : (v : V) → G.Port v → Fin 4) (p : E × Bool) :
    key (G.vertex p.1 p.2) ≤ N ∧ (number _ ⟨p,rfl⟩).val + 1 ≤ 4 :=
  ⟨hk _, (number _ _).isLt⟩

/-- Scalar fields at a vertex, including the parent port with zero at the root. -/
inductive VertexField
  | distance | parentPort | subtreeSize | preorderName | subtreeEdges | subtreeFaces
  | removalRound | patchName
  deriving DecidableEq

instance : Fintype VertexField :=
  Fintype.ofList [.distance, .parentPort, .subtreeSize, .preorderName,
    .subtreeEdges, .subtreeFaces, .removalRound, .patchName] (by intro f; cases f <;> simp)

/-- Fields attached to each of the four port positions. -/
inductive PortField
  | minimumVertex | minimumPort | forwardDistance
  deriving DecidableEq

instance : Fintype PortField :=
  Fintype.ofList [.minimumVertex, .minimumPort, .forwardDistance] (by intro f; cases f <;> simp)

/-- Root flag, port directions in order (with an unused code), and the
bounded numerical fields. -/
abbrev BaseAlphabet (N : ℕ) :=
  Bool × (Fin 4 → Option Bool) × (VertexField ⊕ (Fin 4 × PortField) → Fin (4*N+1))

theorem baseAlphabet_card (N : ℕ) : Fintype.card (BaseAlphabet N) = 162 * (4*N+1)^20 := by
  have hV : Fintype.card VertexField = 8 := by decide
  have hP : Fintype.card PortField = 3 := by decide
  simp [BaseAlphabet, Fintype.card_sum, hV, hP, ← Nat.mul_assoc]

/-- The polynomial alphabet bound for one base label. It can be composed with
the constant number of entries in the bounded port-walk view. -/
theorem baseAlphabet_card_le {N : ℕ} (hN : 1 ≤ N) :
    Fintype.card (BaseAlphabet N) ≤ (2*N)^68 := by
  have h2 : 2 ≤ 2*N := by omega
  have hconst : 162 ≤ (2*N)^8 := (by decide : 162 ≤ 2^8).trans (Nat.pow_le_pow_left h2 8)
  have h4 : 4 ≤ (2*N)^2 := (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_left h2 2)
  have hfield : 4*N+1 ≤ (2*N)^3 := by
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (2*N) h4]
  rw [baseAlphabet_card]
  calc
    162 * (4*N+1)^20 ≤ (2*N)^8 * ((2*N)^3)^20 := Nat.mul_le_mul hconst (Nat.pow_le_pow_left hfield 20)
    _ = (2*N)^68 := by rw [← pow_mul, ← pow_add]

/-- A fixed-width binary encoding of the base label needs at most
`68 * ⌈log₂(2N)⌉` bits. -/
theorem baseAlphabet_bits {N : ℕ} (hN : 1 ≤ N) :
    Nat.clog 2 (Fintype.card (BaseAlphabet N)) ≤ 68 * Nat.clog 2 (2*N) := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  calc
    Fintype.card (BaseAlphabet N) ≤ (2*N)^68 := baseAlphabet_card_le hN
    _ ≤ (2 ^ Nat.clog 2 (2*N))^68 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = _ := by rw [← pow_mul, Nat.mul_comm 68]

/-- The certificate including every walked-to base label and arrival port
out to radius `2K+2` admits a fixed-width binary encoding. -/
theorem exists_full_view_encoding {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    Nonempty (PortGraph.PortView (BaseAlphabet N) (2*K+2) ↪
      (Fin ((80 * 5^(2*K+2)) * Nat.clog 2 (2*N)) → Bool)) :=
  PortGraph.PortView.exists_bitEncoding (2*K+2) hN (baseAlphabet_card_le hN)

end PlanarCertSize

end SpectralBooks
end LinearAlgebra
end OAI
