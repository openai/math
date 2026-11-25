import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsCore

/-! # Reading the canonical partition from the vertex labels

Taking the fiber of a reported patch name recovers the entire selected patch.
In particular each crossing edge is counted exactly as in the partition
inequality, including when different wires have the same pair of endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarPatch
open Finset

variable {V E : Type*} [DecidableEq V] [Fintype E]
variable (key : V ↪ ℕ) (tail head : E → V) (K : ℕ) (ε : ℝ)

/-- Membership in the union of the families of the first `N` rounds. -/
theorem mem_canonicalBlocks {R P : Finset V} {N : ℕ} :
    P ∈ canonicalBlocks key tail head K ε R N ↔ ∃ t < N,
      P ∈ roundSelected key (candidatesOn tail head K ε)
        (residual key (candidatesOn tail head K ε) R t) := by
  let C := candidatesOn tail head K ε
  have mem_union (L : List (Finset (Finset V))) :
      P ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ B ∈ L, P ∈ B := by
    induction L with
    | nil => simp
    | cons a l ih => simp [ih]
  rw [canonicalBlocks, mem_union]
  constructor
  · rintro ⟨B,hB,hP⟩
    obtain ⟨t,ht,rfl⟩ := (mem_patchRounds key C).mp hB
    exact ⟨t,ht,hP⟩
  · rintro ⟨t,ht,hP⟩
    exact ⟨_,(mem_patchRounds key C).mpr ⟨t,ht,rfl⟩,hP⟩

/-- On each block every recorded patch name is its least vertex name. -/
theorem patchName_eq_of_mem {R P : Finset V} {N : ℕ} {record : V → ℕ × ℕ}
    (h : RecordsValid key (candidatesOn tail head K ε) R N record)
    (hP : P ∈ canonicalBlocks key tail head K ε R N) {x : V} (hx : x ∈ P) :
    (record x).2 = leastName key P := by
  obtain ⟨t,_,ht⟩ := (mem_canonicalBlocks ..).mp hP
  exact congrArg Prod.snd (record_eq_of_valid key _ (fun _ _ h => ⟨(mem_candidatesOn.mp h).1,
    (mem_candidatesOn.mp h).2.1⟩) h ht hx)

omit [DecidableEq V] [Fintype E] in
private theorem exists_name_eq_leastName {P : Finset V} (hp : P.Nonempty) :
    ∃ v ∈ P, key v = leastName key P := by
  simpa [leastName, hp] using (Finset.mem_map.mp (Finset.min'_mem (P.map key) (hp.map)))

/-- Two blocks with the same reported minimum meet at that named vertex. -/
theorem eq_of_eq_leastName {blocks : Finset (Finset V)} (hd : (↑blocks : Set (Finset V)).PairwiseDisjoint id)
    {P Q : Finset V} (hP : P ∈ blocks) (hQ : Q ∈ blocks) (hp : P.Nonempty) (hq : Q.Nonempty)
    (he : leastName key P = leastName key Q) : P = Q := by
  obtain ⟨x,hx,hxn⟩ := exists_name_eq_leastName key hp
  obtain ⟨y,hy,hyn⟩ := exists_name_eq_leastName key hq
  obtain rfl : x = y := key.injective ((hxn.trans he).trans hyn.symm)
  by_contra hn
  exact Finset.disjoint_left.mp (hd hP hQ hn) hx hy

end PlanarPatch

namespace PortGraph.RootedMap

open PlanarPatch Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (M : RootedMap V E) {N K : ℕ} {ε : ℝ} {c : Certificate V E}

/-- The partition specified by the label's minimum-name coordinate. -/
def patchFiber (id : V → ℕ) (v : V) : Finset V :=
  univ.filter (fun x => id x = id v)

/-- A patch-name fiber is one of the canonically selected blocks. -/
theorem CertificateChecks.patchFiber_mem (h : M.CertificateChecks N K ε c) (hc : M.HasCandidates K ε) (v : V) :
    patchFiber (fun x => (c.patch x).2) v ∈ canonicalBlocks ⟨c.name,h.tree.name_injective⟩
      M.graph.tail M.graph.head K ε univ N := by
  classical
  let key : V ↪ ℕ := ⟨c.name,h.tree.name_injective⟩
  let B := canonicalBlocks key M.graph.tail M.graph.head K ε univ N
  have hcard : Fintype.card V ≤ N := h.tree.size_root ▸ h.cap
  obtain ⟨hcov,hd,hb,-⟩ := (canonical_peeling key M.graph.tail M.graph.head K ε univ
    (fun R _ => hc R) (by simpa using hcard)).partition
  have cover (v : V) : ∃ P ∈ B, v ∈ P :=
    Finset.mem_biUnion.mp (hcov ▸ mem_univ v : v ∈ B.biUnion id)
  have name {P : Finset V} (hP : P ∈ B) {v : V} (hv : v ∈ P) : (c.patch v).2 = leastName key P :=
    patchName_eq_of_mem key M.graph.tail M.graph.head K ε h.patches hP hv
  have fiber {v : V} {P : Finset V} (hP : P ∈ B) (hv : v ∈ P) :
      patchFiber (fun x => (c.patch x).2) v = P := by
    ext x
    simp only [patchFiber, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨Q,hQ,hxQ⟩ := cover x
      have he := (name hQ hxQ).symm.trans (hx.trans (name hP hv))
      exact eq_of_eq_leastName key hd hQ hP (hb Q hQ).1 (hb P hP).1 he ▸ hxQ
    · intro hx
      exact (name hP hx).trans (name hP hv).symm
  obtain ⟨P,hP,hv⟩ := cover v
  rwa [fiber hP hv]

/-- The actual name fibers are connected, have at most `K` vertices, and cut
at most `ε|V|` edge identifiers. -/
theorem CertificateChecks.partition (h : M.CertificateChecks N K ε c) (hc : M.HasCandidates K ε) :
    (∀ v, Connected M.graph.tail M.graph.head (patchFiber (fun x => (c.patch x).2) v) ∧
      (patchFiber (fun x => (c.patch x).2) v).card ≤ K) ∧
      ((univ.filter (fun e : E => (c.patch (M.graph.tail e)).2 ≠ (c.patch (M.graph.head e)).2)).card : ℝ) ≤
        ε * Fintype.card V := by
  classical
  let key : V ↪ ℕ := ⟨c.name,h.tree.name_injective⟩
  let B := canonicalBlocks key M.graph.tail M.graph.head K ε univ N
  have hcard : Fintype.card V ≤ N := h.tree.size_root ▸ h.cap
  obtain ⟨_,_,hb,hcut⟩ := (canonical_peeling key M.graph.tail M.graph.head K ε univ
    (fun R _ => hc R) (by simpa using hcard)).partition
  have name {P : Finset V} (hP : P ∈ B) {v : V} (hv : v ∈ P) : (c.patch v).2 = leastName key P :=
    patchName_eq_of_mem key M.graph.tail M.graph.head K ε h.patches hP hv
  have hfib := h.patchFiber_mem M hc
  refine ⟨fun v => (hb _ (hfib v)).2, ?_⟩
  have he : univ.filter (fun e : E => (c.patch (M.graph.tail e)).2 ≠ (c.patch (M.graph.head e)).2) =
        crossing M.graph.tail M.graph.head univ B := by
      ext e
      simp only [crossing, mem_filter, mem_univ, true_and]
      constructor
      · rintro hn ⟨P,hP,ht,hh⟩
        exact hn ((name hP ht).trans (name hP hh).symm)
      · intro hsep hsame
        exact hsep ⟨_,hfib (M.graph.tail e),mem_filter.mpr ⟨mem_univ _,rfl⟩,
          mem_filter.mpr ⟨mem_univ _,hsame.symm⟩⟩
  rw [he]
  simpa using hcut

end PortGraph.RootedMap

end

end SpectralBooks
end LinearAlgebra
end OAI
