import OAI.Computability.VPVNP.CompressorRecordsPortRankRAM
import OAI.Computability.VPVNP.CompressorSlotOwnerRuns

/-!
# Filling the absolute-port rank table

The classifier's owner and pivot columns, the bundle counts and the rectangular
key table are read-only throughout the scan. The output column is indexed by
the original arc's full outgoing-port ID, including the residual lane.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRankRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- All addresses that can be read by the call at this port in its input memory. -/
def inputs (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (cap : ℕ) : List (Word w) :=
  [p 0+i, p 1+i, p 4+owner p m i] ++ (List.range cap).map (fun j ↦ start p m i + Fin.ofNat _ j)

private theorem result_congr (p : Fin 6 → Word w) (i : Word w) (cap : ℕ) {m init : Memory w}
    (eqv : ∀ a ∈ inputs p init i cap, m a.val = init a.val) :
    result p m i cap = result p init i cap := by
  have ho : owner p m i = owner p init i := eqv (p 0+i) (by simp [inputs])
  have hp : pivot p m i = pivot p init i := eqv (p 1+i) (by simp [inputs])
  have hlen : lengthAt p m i = lengthAt p init i := by
    simp only [lengthAt, ho]
    exact eqv _ (by simp [inputs])
  have hs : start p m i = start p init i := by simp only [start, ho]
  have hrow : row p m i cap = row p init i cap := by
    simp only [row_eq_map, hs]
    apply List.map_congr_left
    intro j hj
    exact eqv _ (List.mem_append_right _ (List.mem_map.mpr ⟨j,hj,rfl⟩))
  simp only [result, hp, hlen, hrow]

/-- Regions for a full absolute-port scan. Input arrays may be placed in
arbitrary order and used by other phases of the compressor. -/
structure Regions (p : Fin 6 → Word w) (m : Memory w) (cap A : ℕ) : Prop where
  outputFits : (p 5).val + A ≤ 2^w
  reads : ∀ i < A, ∀ a ∈ inputs p m (Fin.ofNat _ i) cap,
    a.val < (p 5).val ∨ (p 5).val + A ≤ a.val

private theorem visit_segment {p : Fin 6 → Word w} {initial : Memory w} {cap A : ℕ}
    (reg : Regions p initial cap A) (k n : ℕ) (hk : k+n ≤ A) :
    SlotOwnerPass.Visit ((template (visit cap) 0).instantiate w p).program (1+(visit cap).length)
      (cap+4) (visit cap).length (p 5).val k n (fun i ↦ result p initial (Fin.ofNat _ i) cap) initial := by
  intro j _ hj m frame
  let i := Fin.ofNat (2^w) j
  have heq := result_congr p i cap (m := m) (init := initial)
    (fun a ha ↦ frame a.val (by have := reg.reads j (by omega) a ha; omega))
  obtain ⟨es,he,hm,hp,hl⟩ := run_one p m i cap
  have hs : i+1 = Fin.ofNat (2^w) (j+1) := by
    apply Fin.ext
    simp [i, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
  have hd : p 5+i = Fin.ofNat (2^w) ((p 5).val+j) := by
    apply Fin.ext
    simp [i, Fin.val_add, Nat.add_mod_mod]
  exact ⟨es, hs ▸ he, by rw [hm,hd,heq], hp,hl⟩

/-- The native segment visits exactly the requested subinterval of the old IDs. -/
theorem interval_run (p : Fin 6 → Word w) (initial : Memory w) (cap A k n : ℕ)
    (reg : Regions p initial cap A) (hk : k+n ≤ A) :
    let M := (template (visit cap) 0).instantiate w p
    ∃ rs, runSegment M.program (1+(visit cap).length) (some (Fin.ofNat _ k)) initial
        (List.replicate n []) = some rs ∧
      endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k+n)) ∧
      (∀ j, k ≤ j → j < k+n → after initial (eventLog rs) ((p 5).val+j) =
        result p initial (Fin.ofNat _ j) cap) ∧
      (∀ a, a < (p 5).val+k ∨ (p 5).val+k+n ≤ a → after initial (eventLog rs) a = initial a) ∧
      rs.length = n ∧ (∀ r ∈ rs, r.probes = cap+4 ∧ r.events.length = (visit cap).length) ∧
      RAMBuckets.cost Report.probes rs = (1+(cap+4))*n := by
  apply SlotOwnerPass.run
  · have := reg.outputFits
    omega
  · exact visit_segment reg k n hk

/-- The complete increasing-cursor rank scan has one call per old port,
`cap+4` probes per call, and a frame covering every other external array. -/
theorem scan_run (p : Fin 6 → Word w) (initial : Memory w) (cap A : ℕ)
    (reg : Regions p initial cap A) :
    let M := (template (visit cap) 0).instantiate w p
    ∃ rs, SlotOwners.FilledRun M.program (1+(visit cap).length) (cap+4) (visit cap).length
      A (p 5) (fun j ↦ result p initial (Fin.ofNat _ j) cap) initial rs := by
  apply SlotOwners.filled_run _ _ _ _ _ _ _ initial reg.outputFits
  exact visit_segment reg 0 A (by omega)

/-- Contents of the cells read for one genuine port. The live keys can
occupy any prefix of the uniform-stride row. -/
structure StoredRow {E : Type*} {K : ℕ} (p : Fin 6 → Word w) (m : Memory w) (i : Word w)
    (cap : ℕ) (key : E → Fin K) (fit : K ≤ 2^w) (e : E) (ids : List E) : Prop where
  count : (lengthAt p m i).val = ids.length
  capacity : ids.length ≤ cap
  pivot_eq : pivot p m i = (key e).castLE fit
  rowFits : (start p m i).val + ids.length ≤ 2^w
  keys : ∀ j : Fin ids.length, m ((start p m i).val + j.val) = (key ids[j.val]).castLE fit

theorem StoredRow.result {E : Type*} {K : ℕ} {p : Fin 6 → Word w} {m : Memory w} {i : Word w}
    {cap : ℕ} {key : E → Fin K} {fit : K ≤ 2^w} {e : E} {ids : List E}
    (h : StoredRow p m i cap key fit e ids) :
    result p m i cap = Fin.ofNat _ (ids.countP (fun a ↦ decide (key a < key e))) := by
  let word := fun a ↦ (key a).castLE fit
  have he : (row p m i cap).take (lengthAt p m i).val = ids.map word := by
    rw [row_eq_map, h.count]
    apply List.ext_getElem
    · simp [h.capacity]
    · intro j hj hk
      have hi : j < ids.length := by simpa using hk
      have hp := h.rowFits
      have ha : (start p m i + Fin.ofNat _ j).val = (start p m i).val+j := by
        rw [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
      simp only [List.getElem_take, List.getElem_map, List.getElem_range, ha]
      exact h.keys ⟨j,hi⟩
  rw [PortRankRAM.result, he, h.pivot_eq, List.countP_map]
  rfl

open Compression Compression.PackingData Slots BundleRank

variable {V H Tag L : Type} {N J A d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (arcs : Arc V H Tag L d c ≃ Fin A)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- From the two materialized key tables, a single fixed template fills the
entire rank column. Its entries are the exact piece numbers and concatenation
numbers of the packed graph, including distinct old wires with shared endpoints. -/
theorem graph_scan (p : Fin 6 → Word w) (initial : Memory w) (cap : ℕ)
    (reg : Regions p initial cap A) (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
    (fitM : N*(J*(d*(2^c*d))) ≤ 2^w) (fitT : 2^c*d ≤ 2^w)
    (motifs : ∀ b (x : P.MotifFiber b), ∃ r : IncidentRow P.bundle b,
      StoredRow p initial (Fin.ofNat _ (arcs x.1.1).val) cap (motifKey P vertices tags)
        fitM x.1 r.ids)
    (thick : ∀ b (x : P.ThickFiber b), ∃ r : IncidentRow (fun a : P.ThickWire ↦ a.1.1) b,
      StoredRow p initial (Fin.ofNat _ (arcs x.1.1).val) cap (thickKey P) fitT x.1 r.ids) :
    let M := (template (visit cap) 0).instantiate w p
    ∃ rs, SlotOwners.FilledRun M.program (1+(visit cap).length) (cap+4) (visit cap).length
        A (p 5) (fun j ↦ result p initial (Fin.ofNat _ j) cap) initial rs ∧
      (∀ b (x : P.MotifFiber b), after initial (eventLog rs) ((p 5).val+(arcs x.1.1).val) =
        Fin.ofNat _ (P.sortedBundleNumbering vertices tags hc b x).val) ∧
      (∀ b (x : P.ThickFiber b), after initial (eventLog rs) ((p 5).val+(arcs x.1.1).val) =
        Fin.ofNat _ (P.sortedThickNumbering hc b x).val) := by
  obtain ⟨rs,run⟩ := scan_run p initial cap A reg
  refine ⟨rs,run,?_,?_⟩
  · intro b x
    obtain ⟨r,h⟩ := motifs b x
    rw [run.filled _ (arcs _).isLt, h.result, motif_rank P vertices tags hc b r x]
  · intro b x
    obtain ⟨r,h⟩ := thick b x
    rw [run.filled _ (arcs _).isLt, h.result, thick_rank P hc b r x]

end CompressorRecords.PortRankRAM

end VPVNP
end Computability
end OAI
