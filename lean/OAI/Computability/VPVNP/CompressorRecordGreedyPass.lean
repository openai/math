import OAI.Computability.VPVNP.CompressorRecordGreedyDirectory

/-!
# Preparing and reading the current compressor level

The initializer derives both greedy operand directories from the evolving level's
forward and inverse mate arrays. The color reader follows label pointers. The tag
reader additionally uses the zero and outgoing displacement cells already present
in that level. These arrays may occur anywhere outside the current output region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.WalkLayout

open BurstRAM Compression Compression.SlotGraph

variable {w N width d j : ℕ} {V : Type*}

private theorem assignment_addresses (L : WalkLayout w N width) (T : PortTables w)
    (order : V ≃ Fin N) (h : T.labels = Fin.ofNat _ L.origin) :
    (T.addresses (d := d) order).label = L.label ∘ order := by
  funext x
  apply Fin.ext
  simp only [PortTables.addresses, WalkLayout.label, vertexNumber, h, Fin.val_add, Fin.val_ofNat,
    Nat.mod_add_mod, Nat.add_mod_mod, Function.comp_apply]

/-- A field outside both mutable assignments and the directory has its supplied
value throughout the complete reader scan. -/
private theorem fixed_value {L : WalkLayout w N width} {A : Type*} {ptrs : Fin N → List (Word w)}
    {outside m : Memory w} {encode : A → Word w} {order : V ≃ Fin N} {f : V → A}
    (r : L.Represents (L.initialMemory ptrs outside) m encode order f) (a : Word w)
    (ha : a.val < L.origin ∨ L.limit ≤ a.val) : m a.val = outside a.val := by
  rcases ha with h | h
  · rw [r.frame _ (Or.inl h)]
    simp [initialMemory, h]
  · rw [r.frame _ (.inr (by unfold limit at h; omega))]
    exact initialMemory_after L _ _ h

/-- Existing immutable displacement data for the native tag pass. -/
structure OffsetData (L : WalkLayout w N width) (T : PortTables w) (order : V ≃ Fin N)
    (hw : j ≤ w) (τ : V × Fin d → BitWord j) (m : Memory w) : Prop where
  zero : m T.zero.val = 0
  zeroOutside : T.zero.val < L.origin ∨ L.limit ≤ T.zero.val
  displacement : ∀ e, m ((T.addresses order).displacement e).val = tagWord hw (τ e)
  displacementOutside : ∀ e : V × Fin d, let a := ((T.addresses order).displacement e).val
    a < L.origin ∨ L.limit ≤ a

theorem color_read_prepared (L : WalkLayout w N (2 * d)) (T : PortTables w)
    (G : SlotGraph V d) (order : V ≃ Fin N) (outside : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (hfit : 2 * d < 2 ^ w) :
    L.Pass (L.initialMemory (fun i => rowWords T G order (order.symm i) (colorOperandRows d)) outside)
      1 (2 * d) (fun v : Fin (2 * d + 1) => Fin.ofNat _ v.val) order (G.orderedColor order) := by
  have eqn : (fun i => rowWords T G order (order.symm i) (colorOperandRows d)) = L.colorOperands G order := by
    funext i
    rw [rowWords_color, assignment_addresses (d := d) L T order labels]
    rfl
  rw [eqn]
  exact color_pass L G order outside hfit

theorem tag_read_prepared (L : WalkLayout w N (4 * tagCount d)) (T : PortTables w)
    (G : SlotGraph V d) (order : V ≃ Fin N) (outside : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (τ : V × Fin d → BitWord j)
    (hw : j ≤ w) (hcard : tagCount d < 2 ^ j) (data : OffsetData L T order hw τ outside) :
    L.Pass (L.initialMemory (fun i => rowWords T G order (order.symm i) (tagOperandRows d)) outside)
      4 (tagCount d) (tagWord hw) order (G.orderedTagOffsets order (bitWordFinEquiv j) τ hcard) := by
  classical
  rw [orderedTagOffsets_fold]
  apply scan_pass L 0 (tagWord_zero hw) order (G.chooseTag (bitWordFinEquiv j) τ hcard)
    (fun i => rowWords T G order (order.symm i) (tagOperandRows d)) _ outside
  · intro m f i rep rows
    apply tag_visit G (order.symm i) τ f hcard hw m _ (T.addresses order) _
      (by simpa only [rowWords_tag] using rows)
    constructor
    · exact (fixed_value rep _ data.zeroOutside).trans data.zero
    · exact fun e => (fixed_value rep _ (data.displacementOutside e)).trans (data.displacement e)
    · rw [assignment_addresses (d := d) L T order labels]
      exact rep.labels
  · intro i
    rw [rowWords_tag_length, tagTests_length, Nat.mul_comm]


/-- Two consecutive native phases. The reader starts in exactly the external
memory left by the preparer's report log. Both machines reset private storage
on every call. -/
def PreparedPass {A : Type*} (L : WalkLayout w N width) (rows : OperandRows d)
    (outside : Memory w) (arity n : ℕ) (encode : A → Word w) (order : V ≃ Fin N)
    (f : V → A) : Prop :=
  ∃ rs, runSegment (prepareMachine w rows).program (1 + (prepareCode rows).length)
      (some 0) outside (List.replicate N []) = some rs ∧
    endState (some 0) rs = some (Fin.ofNat _ N) ∧ rs.length = N ∧
    RAMBuckets.cost (fun r : Report w => countProbes r.events) rs = N * (12 + rows.length + width) ∧
    (∀ r ∈ rs, r.events.length ≤ 32 + 8 * rows.length + 6 * width ∧
      countProbes r.events = 11 + rows.length + width) ∧
    L.Pass (after outside (eventLog rs)) arity n encode order f

theorem prepared_color_pass (L : WalkLayout w N (2 * d)) (T : PortTables w)
    (G : SlotGraph V d) (order : V ≃ Fin N) (m : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (control : Stores m 0 (controlWords L T)) (low : 8 ≤ L.origin) (space : L.limit < 2 ^ w)
    (outside : GraphOutside (d := d) L T order) (hfit : 2 * d < 2 ^ w) :
    L.PreparedPass (colorOperandRows d) m 1 (2 * d)
      (fun v : Fin (2 * d + 1) => Fin.ofNat _ v.val) order (G.orderedColor order) := by
  obtain ⟨rs, hr, hend, hm, hl, hc, hwork⟩ :=
    L.prepare_directory T G order (colorOperandRows d) m labels rep control low space outside
      (fun _ => rowWords_color_length T G order _)
  refine ⟨rs, hr, hend, hl, hc, hwork, ?_⟩
  rw [hm]
  exact color_read_prepared L T G order m labels hfit

theorem prepared_tag_pass (L : WalkLayout w N (4 * tagCount d)) (T : PortTables w)
    (G : SlotGraph V d) (order : V ≃ Fin N) (m : Memory w)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (control : Stores m 0 (controlWords L T)) (low : 8 ≤ L.origin) (space : L.limit < 2 ^ w)
    (outside : GraphOutside (d := d) L T order) (τ : V × Fin d → BitWord j)
    (hw : j ≤ w) (hcard : tagCount d < 2 ^ j) (data : OffsetData L T order hw τ m) :
    L.PreparedPass (tagOperandRows d) m 4 (tagCount d) (tagWord hw) order
      (G.orderedTagOffsets order (bitWordFinEquiv j) τ hcard) := by
  have size (x : V) : (rowWords T G order x (tagOperandRows d)).length = 4 * tagCount d := by
    rw [rowWords_tag_length, tagTests_length, Nat.mul_comm]
  obtain ⟨rs, hr, hend, hm, hl, hc, hwork⟩ :=
    L.prepare_directory T G order (tagOperandRows d) m labels rep control low space outside
      (fun _ => size _)
  refine ⟨rs, hr, hend, hl, hc, hwork, ?_⟩
  rw [hm]
  exact tag_read_prepared L T G order m labels τ hw hcard data

/-- Total calls plus probes for preparing and scanning a level with `N` base vertices. -/
theorem PreparedPass.cost {A : Type*} {L : WalkLayout w N width} {rows : OperandRows d}
    {outside : Memory w} {arity n : ℕ} {encode : A → Word w} {order : V ≃ Fin N} {f : V → A}
    (h : L.PreparedPass rows outside arity n encode order f) :
    ∃ prep reads, runSegment (prepareMachine w rows).program (1 + (prepareCode rows).length)
        (some 0) outside (List.replicate N []) = some prep ∧
      runSegment (visitMachine w arity n).program (1 + (visitCode arity n).length)
        (some (L.base 0)) (after outside (eventLog prep)) (List.replicate N []) = some reads ∧
      RAMBuckets.cost (fun r : Report w => countProbes r.events) prep +
        RAMBuckets.cost (fun r : Report w => countProbes r.events) reads =
        N * (16 + rows.length + width + 2 * arity * n * n) := by
  obtain ⟨prep, hp, _, _, hcost, _, hr⟩ := h
  obtain ⟨reads, he, hc⟩ := hr.cost
  refine ⟨prep, reads, hp, he, ?_⟩
  rw [hc, hcost]; ring

end CompressorRecords.Greedy.WalkLayout

end VPVNP
end Computability
end OAI
