import OAI.ThreeFlat.Diagonal.TraceSortTerminal
import OAI.ThreeFlat.Diagonal.TraceSlotValid
import OAI.ThreeFlat.Diagonal.TraceSortFieldMap
import OAI.ThreeFlat.Diagonal.TraceSortReplay
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI
/-! # A physical site's complete memory-check circuit -/

namespace ThreeFlat.Diagonal.TraceMemoryCircuit

open Computability.VPVNP BurstRAM RAMSort RAMMemory RAMSerialization
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceSlots TraceWords TraceSortSite

variable {w d : ℕ}

/-- Each site can inspect its two input slots, its own and its partner's
sort block for each cross-layer, and its outgoing and incoming boundary slots. -/
abbrev Port (d w : ℕ) := (Fin 2 × Fin 7 × Fin w) ⊕
  ((Fin (RAMLayout.layerCount d) × Bool × Fin 2 × Fin 7 × Fin w) ⊕ (Bool × Fin 7 × Fin w))

def initial (i : Fin 2) : SlotAddr w (Port d w) := fun f j => .inl (i,f,j)
def exchange (l : Fin (RAMLayout.layerCount d)) (own : Bool) (i : Fin 2) : SlotAddr w (Port d w) :=
  fun f j => .inr (.inl (l,own,i,f,j))
def boundary (out : Bool) : SlotAddr w (Port d w) := fun f j => .inr (.inr (out,f,j))

def stagePins (v : Fin (2^d)) : StagePins w d (Port d w) :=
  fun s h u i => exchange (RAMLayout.layerEquiv d ((crossStageEquiv 1 d).symm ⟨s,h⟩)) (decide (u=v)) i

def incoming (m : TraceRecordSort.Packed d w) : Fin (2^d) → Narrow w
  | ⟨0,_⟩ => none
  | ⟨j+1,hj⟩ => m.2 ⟨j,by omega⟩
def outgoing (m : TraceRecordSort.Packed d w) (v : Fin (2^d)) : Narrow w :=
  if h : v.val+1 < 2^d then m.2 ⟨v.val,by omega⟩ else none

theorem incoming_unpack (m : TraceRecordSort.Packed d w) (v : Fin (2^d)) :
    RAMBoundary.receive (TraceRecordSort.unpack m).lastRecords v = (incoming m v).map WordRecord.record := by
  cases v with | mk v hv => cases v <;> rfl

theorem outgoing_unpack (m : TraceRecordSort.Packed d w) (v : Fin (2^d)) :
    RAMBoundary.outgoing (TraceRecordSort.unpack m).lastRecords v = (outgoing m v).map WordRecord.record := by
  unfold RAMBoundary.outgoing outgoing
  split <;> rfl

noncomputable def initialFrame (w d : ℕ) : Frame (Port d w) (Live w) :=
  (Frame.initial id).step fun z => match z with
    | .inl (i,f,j) => .input (initial i f j)
    | .inr _ => .const true

noncomputable def core (v : Fin (2^d)) : Frame (Port d w) Unit :=
  finish (run (stagePins v) v (schedule d) (initialFrame w d)) (boundary false) (boundary true)
    (decide (v.val+1 < 2^d))

theorem core_typed (hw : 2 ≤ w) (v : Fin (2^d)) (x : Port d w → Bool)
    (m : TraceRecordSort.Packed d w) (cur : Fin 2 → Narrow w)
    (hi : ∀ i, ReadSlot hw x (initial i) (cur i))
    (he : ∀ (l : Fin (RAMLayout.layerCount d)) (own : Bool) i,
      let layer := (RAMLayout.layerEquiv d).symm l
      ReadSlot hw x (exchange l own i) (m.1 layer (if own then v else layer.partner v) i))
    (hp : ReadSlot hw x (boundary false) (incoming m v))
    (ho : ReadSlot hw x (boundary true) (outgoing m v)) :
    ((core v).circuit ()).eval x = true ↔ MemoryAt (TraceRecordSort.unpack m) v (toOrdered ∘ cur) := by
  let data := fromPhysical m.1
  have hsend (s : Stage (1+d)) (h : 1 ≤ s.stride) (u : Fin (2^d))
      (hu : u = v ∨ u = sourceSite s h v) (i : Fin 2) :
      ReadSlot hw x (stagePins v s h u i) (data s h u i) := by
    let L := (crossStageEquiv 1 d).symm ⟨s,h⟩
    rcases hu with rfl | rfl
    · simpa [stagePins,data,fromPhysical,L] using he (RAMLayout.layerEquiv d L) true i
    · have hn : sourceSite s h v ≠ v := by rw [sourceSite_eq_physical]; exact L.partner_ne v
      simpa [stagePins,hn,data,fromPhysical,L,sourceSite_eq_physical,RAMLayout.Layer.partner_ne] using he (RAMLayout.layerEquiv d L) false i
  have hinit : ReadLive hw ((initialFrame w d).eval x) cur := by
    intro i f j
    simpa [initialFrame,Expr.eval] using hi i f j
  have hflag : (initialFrame w d).eval x (.inr ()) = true := by simp [initialFrame, Expr.eval]
  obtain ⟨hcur,hok⟩ := run_eval hw (stagePins v) data v x hsend (schedule d) (initialFrame w d) cur hinit
  let final := states data v (schedule d) cur
  have finishAt := finish_eval hw (run (stagePins v) v (schedule d) (initialFrame w d))
    (boundary false) (boundary true) (decide (v.val+1 < 2^d)) x (incoming m v) (outgoing m v) final
    hcur hp ho
  have hpfields : physicalFieldsEquiv 1 d _ (TraceRecordSort.unpack m).sortSends =
      bundle (widened data) (schedule d) := physical_bundle _
  have hf : outputAt (TraceRecordSort.unpack m) v (toOrdered ∘ cur) =
      fun i => (final i).map WordRecord.record := by
    funext i
    unfold outputAt
    rw [hpfields, ← states_replay]
    rfl
  have heq (a b : Narrow w) : a.map WordRecord.record = b.map WordRecord.record ↔ a = b := by
    constructor
    · intro h
      exact toOrdered_injective (congrArg OrderedSlot.mk h)
    · exact fun h => h ▸ rfl
  rw [core, finishAt, hok, hflag, eq_self, true_and,
    outgoingChecks_iff]
  simp only [MemoryAt, hpfields, RAMBoundary.checkAt, hf, incoming_unpack, outgoing_unpack,
    RAMBoundary.lastSlot, heq, decide_eq_true_eq]
  try rfl

def OwnerValid (hw : 2 ≤ w) (v : Fin (2^d)) (x : Port d w → Bool) : Prop :=
  (∀ l i, ∃ r, ReadSlot hw x (exchange l true i) r) ∧
    (v.val+1 < 2^d → ∃ r, ReadSlot hw x (boundary true) r)

def ownerCheck (hw : 2 ≤ w) (v : Fin (2^d)) : Expr (Port d w) :=
  (allBits fun l => allBits fun i => valid hw (exchange l true i)).and
    (if v.val+1 < 2^d then valid hw (boundary true) else .const true)

theorem ownerCheck_eval (hw : 2 ≤ w) (v : Fin (2^d)) (x : Port d w → Bool) :
    (ownerCheck hw v).eval x = true ↔ OwnerValid hw v x := by
  by_cases h : v.val+1 < 2^d <;> simp [ownerCheck,OwnerValid,Expr.eval,allBits_true,valid_at,h]

/-- Sort all records, check five live value fields at the read boundary, and
check one canonical encoding at the owner of every shared outgoing send. -/
noncomputable def row (hw : 2 ≤ w) (v : Fin (2^d)) : Frame (Port d w) Unit :=
  (core v).withInput.step fun _ => ((ownerCheck hw v).rename Sum.inl).and (.input (.inr ()))

theorem row_split (hw : 2 ≤ w) (v : Fin (2^d)) (x : Port d w → Bool) :
    ((row hw v).circuit ()).eval x = true ↔ OwnerValid hw v x ∧ ((core v).circuit ()).eval x = true := by
  simp [row, Expr.eval, ownerCheck_eval]

private theorem initialFrame_size (w d : ℕ) : (initialFrame w d).size ≤ 14*w+1 := by
  let es : Live w → Expr (Port d w) := fun z => match z with
    | .inl (i,f,j) => .input (initial i f j)
    | .inr _ => .const true
  have hs (i : Live w) : (es i).size ≤ 1 := by rcases i with ⟨_,_,_⟩ | ⟨⟩ <;> rfl
  have h := (Frame.initial (id : Port d w → Port d w)).step_size_le es 1 hs
  simp only [Frame.initial_size, zero_add, mul_one, Live, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin,Fintype.card_unit] at h
  exact h.trans (by omega)

private theorem ownerCheck_size (hw : 2 ≤ w) (v : Fin (2^d)) :
    (ownerCheck hw v).size ≤ RAMLayout.layerCount d*(640*(w+1)+4)+320*(w+1)+2 := by
  have h (l : Fin (RAMLayout.layerCount d)) :=
    allBits_size_le (fun i : Fin 2 => valid hw (exchange l true i)) (s := 320*(w+1))
      (fun _ => valid_size hw _)
  have hs := allBits_size_le (fun l : Fin (RAMLayout.layerCount d) =>
    allBits fun i : Fin 2 => valid hw (exchange l true i)) (s := 640*(w+1)+3)
    (fun i => (h i).trans (by omega))
  change _ ≤ RAMLayout.layerCount d*(640*(w+1)+4)+1 at hs
  have hb := valid_size hw (boundary (d := d) true)
  by_cases e : v.val+1 < 2^d <;> simp only [ownerCheck, e, ite_true, ite_false, Expr.size] <;> omega

/-- A uniform polynomial bound for the AND/NOT gates of a single site,
including all sort phases and canonicality checks of every owned send. -/
theorem row_size (hw : 2 ≤ w) (v : Fin (2^d)) :
    (row hw v).circuitSize () ≤ 40000*(d+2)^2*(w+1)^2 := by
  have hi := initialFrame_size w d
  have hs := run_size (stagePins (w := w) v) v (schedule d) (initialFrame w d)
  rw [schedule, length_phases] at hs
  have hf := finish_size (run (stagePins v) v (schedule d) (initialFrame w d))
    (boundary false) (boundary true) (decide (v.val+1 < 2^d))
  change (core (w := w) v).size ≤ _ at hf
  have hv := ownerCheck_size hw v
  have hout := (core (w := w) v).withInput.step_size_le
    (fun _ : Unit => ((ownerCheck hw v).rename Sum.inl).and (.input (.inr ())))
    ((ownerCheck hw v).size+2) (fun _ => by simp [Expr.size])
  change (row hw v).size ≤ _ at hout
  simp only [Frame.withInput_size, Fintype.card_unit, one_mul] at hout
  have ht := (row hw v).circuitSize_le ()
  have hchoose := Nat.choose_le_pow (1+d+1) 2
  have hl : RAMLayout.layerCount d ≤ (d+2)^2 :=
    (Nat.choose_le_pow (d+1) 2).trans (Nat.pow_le_pow_left (by omega) _)
  have hs' : (run (stagePins v) v (schedule d) (initialFrame w d)).size ≤
      (14*w+1)+(d+2)^2*((14*w+1)*(500*(w+1))) := by
    apply hs.trans
    apply Nat.add_le_add hi
    apply Nat.mul_le_mul_right
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hchoose
  have hv' := hv.trans (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _) _)
  apply ht.trans
  apply (Nat.mul_le_mul_left 4 (hout.trans (Nat.add_le_add hf (Nat.add_le_add_right hv' _)))).trans
  apply (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (Nat.add_le_add_right hs' _) _)).trans
  nlinarith only [Nat.zero_le (d^2*w^2), Nat.zero_le (d^2*w), Nat.zero_le (d*w^2),
    Nat.zero_le (d*w), Nat.zero_le d, Nat.zero_le w, Nat.zero_le (d^2), Nat.zero_le (w^2)]

end ThreeFlat.Diagonal.TraceMemoryCircuit

end OAI
