import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.PairTraversalNodeBounds
import OAI.Computability.VPVNP.PairSimulationMapWordBounds
import OAI.Computability.VPVNP.CompressorDescriptorSquare
import OAI.Computability.VPVNP.CompressorDescriptorBranchSpace

/-!
# Word capacity of the private DFS argument frames

Section 13 indexes a private argument interval by the absolute address of its
DFS row. The row lies in the selected branch's descriptor region, while the
stride only needs to accommodate the two sets of half-wire fields of a single
site. Bounding both before choosing the branch gives a live-word bound on the
product of row address and stride, including all offsets used by the map
entry readers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments

open CursorBounds CursorNetwork Compression CompressorRecords TraversalRows Filter
open MotifBlocks MotifConversion MotifSelector MotifGrid MapStream

variable {a g : ℕ}

/-- All the independent half-wires at a vertex fit in two degree-sized rows
of maximum-width slots. -/
theorem packed_length_le (X : State a g) (v : X.network.Site) (h : X.network.Half v) :
    (packed X v h).length ≤ 2 * (2 ^ a) * X.maxWireWidth := by
  rw [packed_length]
  calc
    _ ≤ ∑ _ : Bool, ∑ _ : Fin (2 ^ a), X.maxWireWidth :=
      Finset.sum_le_sum fun dir _ ↦ Finset.sum_le_sum fun j _ ↦ X.halfWidth_le_max v dir j
    _ = _ := by simp [two_mul, Nat.add_mul]

/-- Even an empty field has its start and exclusive end inside the full
argument interval. -/
theorem field_end_le (X : State a g) (v : X.network.Site) (h : X.network.Half v)
    (A : Arena) (node : ℕ) (dir : Bool) (j : Fin (2 ^ a)) :
    A.fieldAddress X v node dir j + X.halfWidth v dir j ≤ A.base node + (packed X v h).length := by
  obtain ⟨pre, post, eqn, len⟩ := packed_member X v h dir j
  rw [Arena.fieldAddress, ← len, eqn]
  simp only [List.length_append, List.length_ofFn]
  omega

/-- Reserve both sets of numbered half-wires using the fixed schedule's
maximum degree and an upper bound on every selected width. -/
def frameStride (degree width : ℕ) : ℕ := 2 * degree * width + 1

theorem frameStride_bounded (degree : ℕ) : PolynomiallyBounded (frameStride degree) :=
  ((PolynomiallyBounded.const (2 * degree)).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 1)

variable {k : Type*} [_root_.Field k] {J D S₀ : Type} [Fintype J] [Fintype D] [Fintype S₀]
variable {src dst : D → J} {P : Supply J S₀} {p : D → ℚ} {q : S₀ → ℚ} {H H' : ℝ}

/-- The four kinds of map-reader endpoints, including cumulative payload
offsets even when a selector sequence later fails its total-width check. -/
def ReadEndsFit (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H')
    (w n address : ℕ) : Prop :=
  ∀ u ≤ n, ∀ z (θ : Fin u → Selector B) (i : Fin u),
    (∀ e, address + baseDemand B z e * i.val + baseDemand B z e < 2 ^ w) ∧
    (∀ e, address + MotifEntry.offset (fun l ↦ basePayload B (θ l) e) i +
      basePayload B (θ i) e < 2 ^ w) ∧
    (∀ e, totalWidth (basePayload B) θ e < 2 ^ w) ∧
    ∀ v ≤ n, address + v + B.selectorBits * i.val + B.selectorBits < 2 ^ w

/-- Polynomial bounds may be fixed independently for the first private
address, the *absolute* row address, the stride and an additional scratch
suffix. Every address up to the resulting end supports the map's reads. -/
theorem eventually_sparseFrame (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H')
    (b : ℕ) (hb : 1 ≤ b) {first limit stride extra : ℕ → ℕ}
    (hf : PolynomiallyBounded first) (hl : PolynomiallyBounded limit)
    (hs : PolynomiallyBounded stride) (he : PolynomiallyBounded extra) :
    ∀ᶠ n : ℕ in atTop, ∀ node ≤ limit n,
      let arena : Arena := ⟨first n, stride n⟩
      arena.base node + arena.stride + extra n < 2 ^ wordBits b n ∧
      ∀ addr ≤ arena.base node + arena.stride + extra n, ReadEndsFit B (wordBits b n) n addr := by
  let bound := fun n ↦ first n + limit n * stride n + stride n + extra n
  have hc : PolynomiallyBounded bound := ((hf.add (hl.mul hs)).add hs).add he
  filter_upwards [CursorRAM.eventual_word_room b hb hc,
    eventually_polynomial_field_addresses B b hb bound hc] with n hroom hmap
  intro node hnode arena
  have h : arena.base node + arena.stride + extra n ≤ bound n :=
    Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ hnode) _) _) _
  exact ⟨h.trans_lt hroom, fun addr ha u hu z θ i ↦
    hmap.2.2.2 u hu z θ i addr (ha.trans h)⟩

/-- Start shared map scratch beyond the reserved frame for the last possible
node. Frames at all smaller absolute node addresses precede this workspace. -/
def Arena.scratch (A : Arena) (limit : ℕ) := A.base limit + A.stride

theorem Arena.frame_before_scratch (A : Arena) {node limit : ℕ} (hn : node ≤ limit) :
    A.base node + A.stride ≤ A.scratch limit :=
  Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _) _

/-- The same address bound applies to a common scratch arena above *all*
private argument frames, for every address in its reserved suffix. -/
theorem eventually_global_map_scratch
    (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H') (b : ℕ) (hb : 1 ≤ b)
    {first rowStart stride extra : ℕ → ℕ} (hf : PolynomiallyBounded first)
    (hl : PolynomiallyBounded rowStart) (hs : PolynomiallyBounded stride)
    (he : PolynomiallyBounded extra) :
    ∀ᶠ n : ℕ in atTop,
      let arena : Arena := ⟨first n, stride n⟩
      let limit := rowStart n + (initialPositions b n) ^ 2
      let scratch := arena.scratch limit
      scratch + extra n < 2 ^ wordBits b n ∧
        (∀ node ≤ limit, arena.base node + arena.stride ≤ scratch) ∧
        ∀ off ≤ extra n, ReadEndsFit B (wordBits b n) n (scratch + off) := by
  let limit n := rowStart n + (initialPositions b n) ^ 2
  have hc : PolynomiallyBounded limit := hl.add ((CursorRAM.bounded_positions b).pow 2)
  filter_upwards [eventually_sparseFrame B b hb hf hc hs he] with n room
  intro arena last scratch
  obtain ⟨endFit, reads⟩ := room (limit n) le_rfl
  exact ⟨endFit, fun _ h ↦ arena.frame_before_scratch h,
    fun off hoff ↦ reads _ (Nat.add_le_add_left hoff _)⟩

/-- The total argument interval and every individual native slot endpoint
lie below the word modulus. The map read bound is specialized to the actual
`fieldAddress`, independent of the guessed bits. -/
structure SiteFits (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H')
    (w n : ℕ) (arena : Arena) (node : ℕ) (X : State a g) : Prop where
  packed : ∀ v h, (NodeArguments.packed X v h).length ≤ arena.stride
  exclusiveEnd : arena.base node + arena.stride < 2 ^ w
  slot : ∀ v dir j, arena.fieldAddress X v node dir j + X.halfWidth v dir j < 2 ^ w ∧
    ReadEndsFit B w n (arena.fieldAddress X v node dir j)

private theorem siteFits_of_bound (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H')
    (w n : ℕ) (arena : Arena) (node : ℕ) (X : State a g)
    (hs : 2 * (2 ^ a) * X.maxWireWidth ≤ arena.stride) (hr : arena.base node + arena.stride < 2 ^ w)
    (hm : ∀ x ≤ arena.base node + arena.stride, ReadEndsFit B w n x) :
    SiteFits B w n arena node X := by
  have hp (v) (h) := (packed_length_le X v h).trans hs
  refine ⟨hp, hr, fun v dir j ↦ ?_⟩
  let h : X.network.Half v := ⟨fun _ _ _ ↦ false, fun _ _ _ ↦ false⟩
  have he := (field_end_le X v h arena node dir j).trans (Nat.add_le_add_left (hp v h) _)
  exact ⟨he.trans_lt hr, hm _ ((Nat.le_add_right _ _).trans he)⟩

variable {S : BlockSchedule k}

/-- For the actual selected cursor history, all frame and slot endpoints fit
on every intermediate input and on the final state. The threshold precedes
the coefficient specialization, the branch, the visited DFS node and the
old half-wire values. -/
theorem eventually_selected_node_fields
    (M : FixedBlock k src dst P (realWidths p) (realWidths q) H H')
    (F : DescriptorSpace.Shape) (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start privateStart extra : ℕ → ℕ}
    (hstart : PolynomiallyBounded start) (hprivate : PolynomiallyBounded privateStart)
    (hextra : PolynomiallyBounded extra) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        let layout := DescriptorSpace.cursorLayout F b S.steps u.θ (start n) n
        let arena : Arena := ⟨privateStart n, frameStride (slotDegree S) n⟩
        ∀ z : E.Choices, let Y := E.finalState z
          ∀ v node,
            node ∈ (selectedTrees B f hf T hT X z (DescriptorSpace.endAddress layout) v).preorder →
            arena.base node + arena.stride + extra n < 2 ^ wordBits b n ∧
            (∀ addr ≤ arena.base node + arena.stride + extra n,
              ReadEndsFit M (wordBits b n) n addr) ∧
            SiteFits M (wordBits b n) n arena node Y ∧
            ∀ level ∈ executeLevels B f hf T hT X z,
              SiteFits M (wordBits b n) n arena node level.input := by
  let limit n := start n + (initialPositions b n) ^ 2
  have hl : PolynomiallyBounded limit := hstart.add ((CursorRAM.bounded_positions b).pow 2)
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  let K := B.recordLimit + 2
  have sparse := eventually_sparseFrame M b hb' hprivate hl
    (frameStride_bounded (slotDegree S)) hextra
  filter_upwards [sparse,
    DescriptorSpace.eventually_selected_square F B u b hb K, eventually_pairBranchBounds B u b hb,
    eventually_ge_atTop 3] with n hspace hsquare hbranch hn
  intro base lanes labels hD hT R _ f hf X T E layout arena z Y v node hnode
  let rowBase := DescriptorSpace.endAddress layout
  let layers := selectedLayers B f hf T hT X z
  have below := selectedTrees_below B f hf T hT X z rowBase v hnode
  have foot := selected_words_le B f hf T hT X z
  change words B.recordLimit layers ≤ K * Y.positions * B.growthConstant ^ T at foot
  have rows_lt : rowBase + words B.recordLimit layers < start n + (processorCount b n) ^ 2 := by
    refine lt_of_le_of_lt ?_ (hsquare (start n) labels hD hT R f hf z)
    change rowBase + words B.recordLimit layers ≤ rowBase +
      K * (X.positions + processorCount b n + Y.positions * B.growthConstant ^ T + Y.totalWidth) + 1
    nlinarith only [foot, Nat.zero_le (K * (X.positions + processorCount b n + Y.totalWidth))]
  have proc : processorCount b n ≤ initialPositions b n :=
    (Nat.pow_le_pow_right Nat.zero_lt_two (addressBits_le_virtualBits b n hn)).trans
      (Nat.le_mul_of_pos_right _ (by omega : 0 < virtualBits b n))
  have hlim : node ≤ limit n := below.le.trans (rows_lt.le.trans
    (Nat.add_le_add_left (Nat.pow_le_pow_left proc 2) _))
  obtain ⟨hroom, hmap⟩ := hspace node hlim
  have branch := hbranch.2.2 labels hD hT R f hf z
  have hlimWidth : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ n := by
    have hw := branch.2.2.2.2.2.1
    change ((B.growthConstant ^ T * (X.maxWireWidth + 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) at hw
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow : (n : ℝ) ^ (3 / 10 : ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (3 / 10 : ℝ) ≤ 1)
    exact_mod_cast hw.trans hpow
  have fit {c l : ℕ} (Z : State c l) (hd : 2 ^ c ≤ slotDegree S) (hw : Z.maxWireWidth ≤ n) :
      SiteFits M (wordBits b n) n arena node Z := by
    apply siteFits_of_bound
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd) hw).trans (Nat.le_succ _)
    · exact (Nat.le_add_right _ _).trans_lt hroom
    · exact fun addr ha ↦ hmap addr (ha.trans (Nat.le_add_right _ _))
  refine ⟨hroom, hmap, fit Y ?_ (branch.2.2.2.2.1.trans hlimWidth), fun level hlevel ↦ ?_⟩
  · exact (Finset.le_sup (f := fun i : Fin (S.steps + 1) ↦ 2 ^ S.degreeExponent i)
      (Finset.mem_univ 0)).trans (le_max_right _ _)
  · exact fit level.input level.oldDegree_le
      (((executeLevels_limits B f hf T hT X z level hlevel).2).trans hlimWidth)

end PairSimulation.NodeArguments

end VPVNP
end Computability
end OAI
