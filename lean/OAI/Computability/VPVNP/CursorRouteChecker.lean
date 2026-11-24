import OAI.Computability.VPVNP.CursorValidatorContraction
import Mathlib.Data.List.FinRange

/-!
# Reading the routing constraints at one cursor vertex

At most two bit tests per field bit check all the routing constraints of
Section 12. Each test uses the vertex's own outgoing and incoming ports.
A transit comparison probes two bits. A zero check probes one. The program
retains the inactive-successor zero checks at cursor zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting RAMLayout

variable {D H w : ℕ}

/-- The four incident arc slots of a cursor vertex. -/
inductive LocalPort
  | outgoing (flip : Bool)
  | incoming (flip : Bool)

/-- A bit address consists of a local port, a mask-system field, and a bit
within that field. -/
structure LocalAddress (D H w : ℕ) where
  /-- Incoming or outgoing arc slot at which the routing checker reads the bit. -/
  port : LocalPort
  /-- Mask system identifying the RAM field to be read from that port. -/
  system : RAMSystem D
  /-- Bit position within the field of the selected RAM system. -/
  bit : Fin (ramFieldBits H w system)

/-- Primitive routing comparisons, with explicit operands. -/
inductive BitTest (D H w : ℕ)
  | skip
  | clear (a : LocalAddress D H w)
  | same (a b : LocalAddress D H w)

/-- Evaluate a routing test by skipping it, testing a bit for zero, or comparing two addressed
bits. -/
def BitTest.run (read : LocalAddress D H w → Bool) : BitTest D H w → Bool
  | .skip => true
  | .clear a => !read a
  | .same a b => read a == read b

/-- Exact number of bit probes needed for one test. -/
def BitTest.probes : BitTest D H w → ℕ
  | .skip => 0
  | .clear _ => 1
  | .same _ _ => 2

/-- The sort fields are enumerated by their triangular layer ordinals. -/
def systemList (D : ℕ) : List (RAMSystem D) :=
  (List.finRange D).map Sum.inl ++ (List.finRange (layerCount D)).map (Sum.inr ∘ layerAt D)

private theorem mem_systemList (s : RAMSystem D) : s ∈ systemList D := by
  rcases s with k | l
  · simp [systemList]
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨l.ordinal, List.mem_finRange _,
      congrArg Sum.inr ((layerEquiv D).symm_apply_apply l)⟩

/-- The second test at a given bit. -/
def payloadTest [NeZero D] (v : Position D) (s : RAMSystem D)
    (j : Fin (ramFieldBits H w s)) : BitTest D H w :=
  let used := (systemMask s).val.testBit v.1.val
  let q := LocalAddress.mk (.outgoing used) s j
  if v.1 = 0 then
    match s with
    | .inl k =>
      if v.2.val + 1 < 2 ^ D ∧ v.2.val ^^^ (v.2.val + 1) = (systemMask (.inl k)).val then .skip
      else .clear q
    | .inr _ => .skip
  else .same q ⟨.incoming ((systemMask s).val.testBit ((finRotate D).symm v.1).val), s, j⟩

/-- First zero the unused outgoing field. Then check the site's transit or
inactive-successor constraint at this bit. -/
def bitTests [NeZero D] (v : Position D) (s : RAMSystem D) (j : Fin (ramFieldBits H w s)) :
    List (BitTest D H w) :=
  [.clear ⟨.outgoing (!(systemMask s).val.testBit v.1.val), s, j⟩, payloadTest v s j]

/-- All the local bit tests in contiguous mask-system and bit order. -/
def routeTests [NeZero D] (H w : ℕ) (v : Position D) : List (BitTest D H w) :=
  (systemList D).flatMap (fun s ↦ (List.finRange (ramFieldBits H w s)).flatMap (bitTests v s))

/-- Run the Boolean checker using a reader for the four local ports. -/
def routeAccept [NeZero D] (H w : ℕ) (v : Position D) (read : LocalAddress D H w → Bool) : Bool :=
  (routeTests H w v).all (BitTest.run read)

/-- A reader for independently supplied half-wire indices at a position. -/
def readHalf [NeZero D] (v : Position D)
    (z : (network D (ramFieldBits H w : RAMSystem D → ℕ)).Half v)
    (a : LocalAddress D H w) : Bool :=
  match a.port with
  | .outgoing b => out v z b a.system a.bit
  | .incoming b => inc v z b a.system a.bit

private theorem routeAccept_iff [NeZero D] (v : Position D) (read : LocalAddress D H w → Bool) :
    routeAccept H w v read = true ↔
      ∀ s j, read ⟨.outgoing (!(systemMask s).val.testBit v.1.val), s, j⟩ = false ∧
        (payloadTest v s j).run read = true := by
  simp only [routeAccept, routeTests, List.all_eq_true, List.mem_flatMap, forall_exists_index,
    and_imp, List.mem_finRange, true_implies, bitTests, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h s j
    exact ⟨by simpa [BitTest.run] using h _ s (mem_systemList s) j (Or.inl rfl),
      h _ s (mem_systemList s) j (Or.inr rfl)⟩
  · rintro h _ s _ j (rfl | rfl)
    · simpa [BitTest.run] using (h s j).1
    · exact (h s j).2

/-- On all half-wire inputs the local bit program checks precisely the route
conditions and, at cursor zero, the inactive successor fields. -/
theorem routeAccept_readHalf [NeZero D] (v : Position D)
    (z : (network D (ramFieldBits H w : RAMSystem D → ℕ)).Half v) :
    routeAccept H w v (readHalf v z) = true ↔
      Checks systemMask v z ∧ (v.1 = 0 → ActiveSends v.2 (sent systemMask v z)) := by
  rw [routeAccept_iff]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s side hs
      have he : side = !(systemMask s).val.testBit v.1.val := by
        cases side <;> cases hb : (systemMask s).val.testBit v.1.val <;> simp_all
      subst side
      exact funext fun j ↦ (h s j).1
    · intro hz
      funext s j
      simpa [payloadTest, hz, BitTest.run, readHalf, sent, received] using (h s j).2
    · intro hz k hinactive
      funext j
      simpa [payloadTest, hz, hinactive, BitTest.run, readHalf, sent] using (h (.inl k) j).2
  · rintro ⟨⟨hclamp, htransit⟩, hactive⟩ s j
    refine ⟨?_, ?_⟩
    · exact congrFun (hclamp s _ (Bool.not_ne_self _)) j
    · by_cases hz : v.1 = 0
      · rcases s with k | l
        · by_cases h : v.2.val + 1 < 2 ^ D ∧ v.2.val ^^^ (v.2.val + 1) = (systemMask (.inl k)).val
          · simp [payloadTest, hz, h, BitTest.run]
          · simpa [payloadTest, hz, h, BitTest.run, readHalf, sent] using
              congrFun (hactive hz k h) j
        · simp [payloadTest, hz, BitTest.run]
      · simpa [payloadTest, hz, BitTest.run, readHalf, sent, received] using
          congrFun (congrFun (htransit hz) s) j


private theorem sum_widths_systemList (D H w : ℕ) :
    ((systemList D).map (ramFieldBits H w)).sum =
      D * (8 * w) + layerCount D * blockBits H w := by
  simp [systemList, List.map_map, Function.comp_def, ramFieldBits]

/-- Two instructions per payload bit are enough, even for independently
supplied half-wire assignments that fail one of the comparisons. -/
theorem routeTests_length [NeZero D] (v : Position D) :
    (routeTests H w v).length = 2 * (D * (8 * w) + layerCount D * blockBits H w) := by
  have hj (s : RAMSystem D) (js : List (Fin (ramFieldBits H w s))) :
      (js.flatMap (bitTests v s)).length = 2 * js.length := by
    induction js with
    | nil => rfl
    | cons j js ih => simp [bitTests, ih, Nat.mul_add]
  have hs (ss : List (RAMSystem D)) :
      (ss.flatMap (fun s ↦ (List.finRange (ramFieldBits H w s)).flatMap (bitTests v s))).length =
        2 * (ss.map (ramFieldBits H w)).sum := by
    induction ss with
    | nil => rfl
    | cons s ss ih => simp [hj, ih, Nat.mul_add]
  exact (hs (systemList D)).trans (congrArg (2 * ·) (sum_widths_systemList D H w))

private theorem probes_le_two (t : BitTest D H w) : t.probes ≤ 2 := by
  cases t <;> simp [BitTest.probes]

/-- Worst-case probes of the test list. Its first instruction per bit is
always a single zero read. Its second instruction reads at most two bits. -/
theorem routeTests_probes_le [NeZero D] (v : Position D) :
    ((routeTests H w v).map BitTest.probes).sum ≤
      3 * (D * (8 * w) + layerCount D * blockBits H w) := by
  have hj (s : RAMSystem D) (js : List (Fin (ramFieldBits H w s))) :
      (((js.flatMap (bitTests v s)).map BitTest.probes).sum) ≤ 3 * js.length := by
    induction js with
    | nil => rfl
    | cons j js ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, bitTests, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons]
      change 1 + (payloadTest v s j).probes + _ ≤ _
      have := probes_le_two (payloadTest v s j)
      omega
  have hs (ss : List (RAMSystem D)) :
      ((ss.flatMap (fun s ↦ (List.finRange (ramFieldBits H w s)).flatMap (bitTests v s))).map
        BitTest.probes).sum ≤ 3 * (ss.map (ramFieldBits H w)).sum := by
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, Nat.mul_add]
      exact Nat.add_le_add (by simpa using hj s (List.finRange (ramFieldBits H w s))) ih
  exact (hs (systemList D)).trans_eq (congrArg (3 * ·) (sum_widths_systemList D H w))

end CursorNetwork

end VPVNP
end Computability
end OAI
