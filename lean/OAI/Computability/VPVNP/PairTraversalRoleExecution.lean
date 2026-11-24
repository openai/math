import OAI.Computability.VPVNP.PairTraversalRoles
import OAI.Computability.VPVNP.PairTraversalBuildExecution

/-!
# Native role directory for the selected history

One pass per physical level writes the cursor, shrink, or refresh tag at the
public offset from each live descriptor header. Each pass starts with the
memory left by its predecessor. A separate final-bit interval can occupy
the gap between the descriptor region and these sparse tags.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression TraversalRows LocalHistory
open scoped Fin.CommRing

variable {w : ℕ}

/-- Post-memory of the per-layer writes. -/
noncomputable def writeTags (offset cap base : ℕ) : List TaggedLayer → Memory w → Memory w
  | [], m => m
  | L :: ls, m => writeTags offset cap (endPos cap base L.layer) ls
    (Native.image offset cap base L.layer.count (L.role.code : Word w) m)

/-- The word region occupied by these tags has the same extent as the
corresponding row region, translated by the public offset. -/
def tagWords (cap : ℕ) (ls : List TaggedLayer) : ℕ := words cap (ls.map TaggedLayer.layer)

private theorem tagWords_cons (cap : ℕ) (L : TaggedLayer) (ls : List TaggedLayer) :
    tagWords cap (L :: ls) = (cap + 2) * L.layer.count + tagWords cap ls := by
  simp [tagWords, words, Nat.mul_add]

/-- Tag writing cannot alter any earlier descriptor, final bit, or memory cell
outside its own layer intervals. -/
theorem write_tags_outside (offset cap base : ℕ) (ls : List TaggedLayer) (m : Memory w) (x : ℕ)
    (hx : x < offset + base ∨ offset + base + tagWords cap ls ≤ x) :
    writeTags offset cap base ls m x = m x := by
  induction ls generalizing base m with
  | nil => rfl
  | cons L ls ih =>
    let next := endPos cap base L.layer
    have hn : base ≤ next := Nat.le_add_right _ _
    have he : offset + base + tagWords cap (L :: ls) = offset + next + tagWords cap ls := by
      simp [next, endPos, address, tagWords_cons, Nat.add_assoc]
    have ht : x < offset + next ∨ offset + next + tagWords cap ls ≤ x := by omega
    apply (ih next _ ht).trans
    apply Native.image_outside
    intro i hi
    have hlo : base ≤ address cap base i := Nat.le_add_right _ _
    have hhi : address cap base i < next := by
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hi (by omega)) _
    omega

/-- Every selected layer's role can be read back at each site's actual header
address. -/
theorem writeTags_reads (offset cap base : ℕ) (ls : List TaggedLayer) (m : Memory w) :
    Reads w (writeTags offset cap base ls m) offset cap base ls := by
  induction ls generalizing base m with
  | nil => trivial
  | cons L ls ih =>
    let next := endPos cap base L.layer
    let memory := Native.image offset cap base L.layer.count (L.role.code : Word w) m
    refine ⟨fun i => ?_, ih next memory⟩
    have h : address cap base i.val < next :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left i.isLt (by omega)) _
    exact (write_tags_outside offset cap next ls memory _ (Or.inl (Nat.add_lt_add_left h _))).trans
      (Native.image_at offset cap base L.layer.count _ m i.isLt)

/-- Replay of the fixed-width-independent role worker over all selected layers. -/
inductive RolePasses (offset cap : ℕ) : ℕ → List TaggedLayer → Memory w → List (Report w) → Prop
  | nil (base : ℕ) (m : Memory w) : RolePasses offset cap base [] m []
  | cons {base : ℕ} {L : TaggedLayer} {ls : List TaggedLayer} {m : Memory w}
      {rs rest : List (Report w)}
      (run : let p := Native.params offset cap base (L.role.code : Word w)
        let M := (template Native.visit 0).instantiate w p
        runSegment M.program 12 (some 0) m (List.replicate L.layer.count []) = some rs)
      (next : RolePasses offset cap (endPos cap base L.layer) ls (after m (eventLog rs)) rest) :
      RolePasses offset cap base (L :: ls) m (rs ++ rest)

/-- Exactly one burst and one external write per stored role. The final memory
agrees with the directory read by the visit dispatcher. -/
theorem native_write_tags (offset cap base : ℕ) (ls : List TaggedLayer) (m : Memory w)
    (fit : offset + base + tagWords cap ls ≤ 2 ^ w) :
    ∃ rs, RolePasses offset cap base ls m rs ∧
      after m (eventLog rs) = writeTags offset cap base ls m ∧
      rs.length = (ls.map (fun L => L.layer.count)).sum ∧
      (∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 1) ∧
      RAMBuckets.cost Report.probes rs = 2 * (ls.map (fun L => L.layer.count)).sum := by
  induction ls generalizing base m with
  | nil => exact ⟨[], .nil _ _, rfl, rfl, by simp, rfl⟩
  | cons L ls ih =>
    let next := endPos cap base L.layer
    have hfit : offset + next + tagWords cap ls ≤ 2 ^ w := by
      simpa [next, endPos, address, tagWords_cons, Nat.add_assoc] using fit
    obtain ⟨rs, run, memory, calls, each, cost⟩ := Native.run_layer offset cap base L.layer
      (L.role.code : Word w) m ((Nat.le_add_right _ _).trans hfit)
    obtain ⟨tail, runs, hmem, hc, heach, hcost⟩ := ih next (after m (eventLog rs)) hfit
    refine ⟨rs ++ tail, .cons run runs, ?_, ?_, ?_, ?_⟩
    · have happ : eventLog (rs ++ tail) = eventLog rs ++ eventLog tail := by simp [eventLog]
      rw [happ, show after m (eventLog rs ++ eventLog tail) = after (after m (eventLog rs))
        (eventLog tail) from List.foldl_append, hmem, memory]
      rfl
    · simp only [List.length_append, calls, hc, List.map_cons, List.sum_cons]
    · intro r hr
      exact (List.mem_append.mp hr).elim (each r) (heach r)
    · simp only [RAMBuckets.cost_append, cost, hcost, List.map_cons, List.sum_cons, Nat.mul_add]

/-- The arithmetic performed by the dispatcher reads the same natural address
as the tag directory when the public offset and node pointer fit together. -/
theorem probe_word_add (offset node : ℕ) (m : Memory w) (fit : offset + node < 2 ^ w) :
    m (((offset : Word w) + (node : Word w)).val) = m (offset + node) := by
  rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt fit]

private theorem reads_above {ls : List TaggedLayer} {offset cap base : ℕ} {m m' : Memory w}
    (hr : Reads w m offset cap base ls) (agree : ∀ x ≥ offset + base, m' x = m x) :
    Reads w m' offset cap base ls := by
  induction ls generalizing base with
  | nil => trivial
  | cons L ls ih =>
    refine ⟨fun i => (agree _ (Nat.add_le_add_left (Nat.le_add_right _ _) _)).trans (hr.1 i), ?_⟩
    apply ih hr.2
    intro x hx
    exact agree x ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hx)

variable {k R : Type*} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → R) (hf : B.IsSolution f) {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n)
variable (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T hT X).Choices)

/-- Build the tags and the DFS descriptors in disjoint intervals of the same
memory. With `F` final-bit words between the intervals, all `F` cells retain
their original contents. The pointer offset used by the dispatcher is exactly
`rowWords + F`. -/
theorem selected_tags_and_rows (base F : ℕ) (m : Memory w)
    (fit : base + words B.recordLimit (selectedLayers B f hf T hT X z) < 2 ^ w) :
    let ls := selectedLayers B f hf T hT X z
    let offset := words B.recordLimit ls + F
    let tagged := writeTags offset B.recordLimit base (selected B f hf T hT X z) m
    let final := build B.recordLimit base base ls tagged
    Reads w final offset B.recordLimit base (selected B f hf T hT X z) ∧
      (∀ i < F, final (base + words B.recordLimit ls + i) = m (base + words B.recordLimit ls + i)) ∧
      AllRows w final B.recordLimit base base ls := by
  let ls := selectedLayers B f hf T hT X z
  let taggedLayers := selected B f hf T hT X z
  let size := words B.recordLimit ls
  let offset := size + F
  let tagged := writeTags offset B.recordLimit base taggedLayers m
  have hr := writeTags_reads offset B.recordLimit base taggedLayers m
  refine ⟨reads_above hr (fun x hx => build_outside ls _ _ _ tagged x (Or.inr (by
    change offset + base ≤ x at hx
    change base + size ≤ x
    dsimp only [offset] at hx
    omega))), fun i hi => ?_, ?_⟩
  · let addr := base + size + i
    have h := build_outside ls B.recordLimit base base tagged addr
      (Or.inr (show base + size ≤ addr from Nat.le_add_right _ _))
    exact h.trans (write_tags_outside offset B.recordLimit base taggedLayers m addr
      (Or.inl (by dsimp only [addr, offset]; omega)))
  · exact build_rows ls B.recordLimit base base tagged (selected_capacity B f hf T hT X z) fit

/-- Initialize the selected branch's role tags using one native write per site.
The running time and probe cost use the actual number of compressor stages. -/
theorem native_selected_roles (base F : ℕ) (m : Memory w)
    (fit : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F ≤ 2 ^ w) :
    let ls := selected B f hf T hT X z
    let offset := words B.recordLimit (selectedLayers B f hf T hT X z) + F
    ∃ rs, RolePasses offset B.recordLimit base ls m rs ∧
      after m (eventLog rs) = writeTags offset B.recordLimit base ls m ∧
      Reads w (after m (eventLog rs)) offset B.recordLimit base ls ∧
      rs.length ≤ ((S.steps + 1) * T + 1) * X.positions ∧
      (∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 1) ∧
      RAMBuckets.cost Report.probes rs ≤ 2 * (((S.steps + 1) * T + 1) * X.positions) := by
  let ls := selected B f hf T hT X z
  let size := words B.recordLimit (selectedLayers B f hf T hT X z)
  let offset := size + F
  have hsize : tagWords B.recordLimit ls = size := by
    rw [tagWords, show ls.map TaggedLayer.layer = _ from selected_layers B f hf T hT X z]
  obtain ⟨rs, run, hm, hc, he, hp⟩ := native_write_tags offset B.recordLimit base ls m (by
    rw [hsize]
    change base + 2 * size + F ≤ _ at fit
    dsimp only [offset]
    omega)
  have bound : (ls.map (fun l => l.layer.count)).sum ≤ ((S.steps + 1) * T + 1) * X.positions := by
    have h := selected_count_sum_le B f hf T hT X z
    rw [← selected_layers B f hf T hT X z, List.map_map] at h
    exact h
  refine ⟨rs, run, hm, ?_, hc.trans_le bound, he, hp.trans_le (Nat.mul_le_mul_left 2 bound)⟩
  rw [hm]
  exact writeTags_reads offset B.recordLimit base ls m

end PairSimulation.TraversalRoles

end VPVNP
end Computability
end OAI
