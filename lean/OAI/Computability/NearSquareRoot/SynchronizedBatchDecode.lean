import OAI.Computability.NearSquareRoot.SynchronizedBatchPlacement
import OAI.Computability.NearSquareRoot.SynchronizedBatchSlots
import OAI.Computability.NearSquareRoot.SynchronizedFixedScheduleSemantics
import OAI.Computability.NearSquareRoot.SynchronizedPlacedSlots

/-! # Reading a lowered instruction from the prepared physical block word

A direct descriptor acts on its placed phase or permutation. The eight
microinstructions of a placed butterfly use the endpoint routing tables
and the three explicit phase tables for active and idle pairs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix IntegerMultiplication.Code SynchronizedLayers SynchronizedLayers.ScheduleProgram AxisWord

noncomputable section

private def direct {X J A : Type} [Fintype X] [Fintype J] [DecidableEq X] [DecidableEq J] [DecidableEq A]
    (e : X × J ↪ A) : Slot X → Slot A
  | .permutation p => .permutation (placedSlotPermutation e p)
  | .phase d h => .phase (placedSlotPhase e d) (placedSlotPhase_norm e d h)
  | .walsh => .walsh

private theorem direct_kind {X J A : Type} [Fintype X] [Fintype J]
    [DecidableEq X] [DecidableEq J] [DecidableEq A] (e : X × J ↪ A) (s : Slot X) :
    (direct e s).kind = s.kind := by cases s <;> rfl

private theorem direct_matrix {X J A S C : Type} [Fintype X] [Fintype J] [Fintype A]
    [DecidableEq X] [DecidableEq J] [DecidableEq A] [DecidableEq S] [DecidableEq C]
    (e : X × J ↪ A) (bits : A ≃ Fin 2 × S) (f : X ≃ Fin 2 × C) (s : Slot X) (hs : s ≠ .walsh) :
    (direct e s).matrix bits = placeHom e (s.matrix f) := by
  cases s with
  | permutation p => exact placedSlotPermutation_matrix e bits p
  | phase d h => exact placedSlotPhase_matrix e bits d h
  | walsh => exact (hs rfl).elim

private theorem fixedSlot_walsh {a k : ℕ} [NeZero a] (x : Inst) :
    fixedSlot a k x = .walsh ↔ x.1.length = 10 := by
  have eq (s : Slot (Ambient k)) : s = .walsh ↔ s.kind = .walsh := by
    cases s <;> simp [Slot.kind]
  rw [eq, fixedSlot_kind]
  split_ifs <;> simp_all

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
  (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
  (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)
  (bits : Address a c ≃ Fin 2 × Fin (Fintype.card (Address a c)/2)) (he : Even (Fintype.card (Address a c)))

/-- Slots of a routed batch butterfly in the opcode generator's order. -/
def walshSlots (i : Fin m) (b : Fin 15) : List (Slot (Address a c)) :=
  RoutedWalsh.routingCode bits dilationAddress (batchEmbedding a c k spectator har hborrow i b)
    (blockRank a c spectator i) (pairLabels a c k i b) he

private def atMicro (g : Fin m × Fin 15 × Inst) (t : Tally) : Slot (Address a c) :=
  if t.length = 0 then direct (batchEmbedding a c k spectator har hborrow g.1 g.2.1) (fixedSlot (a g.1) (k g.1) g.2.2)
  else (walshSlots a c k spectator har hborrow bits he g.1 g.2.1)[t.length - 1]?.getD .walsh

/-- Interpret the literal axis, batch, instruction and microinstruction fields.
Malformed axis or batch fields use an identity permutation. -/
def decodeSlot (z : SlotDescriptor) : Slot (Address a c) :=
  if hi : z.1.1.length < m then
    if hb : z.1.2.1.length < 15 then
      atMicro a c k spectator har hborrow bits he (⟨z.1.1.length,hi⟩,⟨z.1.2.1.length,hb⟩,z.1.2.2) z.2
    else .permutation (Equiv.refl _)
  else .permutation (Equiv.refl _)

private theorem decode_encode (g : Fin m × Fin 15 × Inst) (t : Tally) :
    decodeSlot a c k spectator har hborrow bits he (encode g,t) =
      atMicro a c k spectator har hborrow bits he g t := by
  rcases g with ⟨i,b,x⟩
  simp [decodeSlot, encode, i.isLt, b.isLt]

/-- One complete lowering computes its requested placed matrix. -/
theorem decode_lower_prod (g : Fin m × Fin 15 × Inst) :
    ((lower (encode g)).map (fun r => (decodeSlot a c k spectator har hborrow bits he r).matrix bits)).prod =
      gateMatrix a c k spectator har hborrow g := by
  rcases g with ⟨i,b,x⟩
  rw [gateMatrix_placed]
  by_cases hx : x.1.length = 10
  · have hgate : fixedSlot (a i) (k i) x = .walsh := (fixedSlot_walsh x).2 hx
    have hL : lower (encode (i,b,x)) = microcode.map (fun t => (encode (i,b,x),t)) := by
      simp [lower, encode, hx]
    rw [hL, hgate, List.map_map]
    simp only [Function.comp_def, decode_encode]
    change ((walshSlots a c k spectator har hborrow bits he i b).map (Slot.matrix bits)).prod = _
    exact RoutedWalsh.routingCode_prod ..
  · have hL : lower (encode (i,b,x)) = [(encode (i,b,x),[])] := by simp [lower, encode, hx]
    rw [hL]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, decode_encode]
    exact direct_matrix _ _ _ _ (fun h => hx ((fixedSlot_walsh x).1 h))

/-- The opcode kind on every emitted descriptor agrees with its actual gate. -/
theorem decode_lower_kind (g : Fin m × Fin 15 × Inst) (hx : g.2.2 ∈ fixedWord (tally (k g.1)))
    (r : SlotDescriptor) (hr : r ∈ lower (encode g)) :
    (decodeSlot a c k spectator har hborrow bits he r).kind = slotKind r := by
  rcases g with ⟨i,b,x⟩
  by_cases htag : x.1.length = 10
  · have hL : lower (encode (i,b,x)) = microcode.map (fun t => (encode (i,b,x),t)) := by
      simp [lower, encode, htag]
    rw [hL] at hr
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
    rw [decode_encode]
    simp only [microcode, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h|h|h|h|h|h|h|h <;> subst t <;> rfl
  · have hL : lower (encode (i,b,x)) = [(encode (i,b,x),[])] := by simp [lower, encode, htag]
    rw [hL, List.mem_singleton] at hr
    subst r
    rw [decode_encode]
    change (direct _ (fixedSlot (a i) (k i) x)).kind = instructionKind x
    rw [direct_kind]
    exact fixedSlot_kind_of_mem hx

/-- Full physical matching induced by the completed endpoint table. -/
def completeMatching (i : Fin m) (b : Fin 15) : Fin 2 × Fin (Fintype.card (Address a c)/2) ≃ Address a c :=
  RoutedWalsh.routeMatching dilationAddress (batchEmbedding a c k spectator har hborrow i b)
    (blockRank a c spectator i) (pairLabels a c k i b) he

/-- Outward and return permutation descriptors use the same complete table. -/
theorem decode_routes (g : Fin m × Fin 15 × Inst) :
    let p := (completeMatching a c k spectator har hborrow he g.1 g.2.1).symm.trans bits.symm
    decodeSlot a c k spectator har hborrow bits he (encode g,tally 1) = .permutation p ∧
    decodeSlot a c k spectator har hborrow bits he (encode g,tally 8) = .permutation p.symm := by
  simp only [decode_encode]
  exact ⟨rfl,rfl⟩

theorem decode_routed_walsh (g : Fin m × Fin 15 × Inst) (j : Fin 3) :
    decodeSlot a c k spectator har hborrow bits he (encode g,tally (2*j.val+2)) = .walsh := by
  rw [decode_encode]
  fin_cases j <;> rfl

/-- The routed diagonal coefficients are exactly the phase-table queries
prepared for active and idle pairs. -/
theorem decode_routed_phase (g : Fin m × Fin 15 × Inst) (j : Fin 3) :
    (decodeSlot a c k spectator har hborrow bits he (encode g,tally (2*j.val+3))).matrix bits =
      diagonal (fun p => RoutedWalsh.table
        (fun s => decide (s.val < SynchronizedBorrowing.size (fiberCount a c g.1) g.2.1 * 2 ^ k g.1)) j (bits p)) := by
  rw [decode_encode]
  fin_cases j <;> rfl

/-- A direct permutation descriptor is the actual lifted local permutation. -/
theorem decode_direct_permutation (g : Fin m × Fin 15 × Inst)
    (p : Equiv.Perm (Ambient (k g.1))) (hp : fixedSlot (a g.1) (k g.1) g.2.2 = .permutation p) :
    decodeSlot a c k spectator har hborrow bits he (encode g,[]) =
      .permutation (placedSlotPermutation (batchEmbedding a c k spectator har hborrow g.1 g.2.1) p) := by
  rw [decode_encode]
  change direct _ (fixedSlot _ _ _) = _
  rw [hp]
  rfl

/-- A direct descriptor is itself the placed gate. -/
theorem decode_direct_matrix (g : Fin m × Fin 15 × Inst) (h : g.2.2.1.length ≠ 10) :
    (decodeSlot a c k spectator har hborrow bits he (encode g,[])).matrix bits =
      gateMatrix a c k spectator har hborrow g := by
  have H := decode_lower_prod a c k spectator har hborrow bits he g
  have hl : lower (encode g) = [(encode g,[])] := by simp [lower, encode, h]
  simpa only [hl, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using H

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
