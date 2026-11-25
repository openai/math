import OAI.Hierarchy.ProtocolRAMPurchaseClock
import OAI.Hierarchy.ProtocolRAMPurchaseMarketRun
import OAI.Hierarchy.ProtocolRAMPurchaseHardware

namespace OAI
/-! # Public resource bounds for the entire frozen sweep -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT Filter
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
noncomputable section

variable {z d k : ℕ}

def stages (d k : ℕ) := (2*rounds d+1)*(2*k)

def timeFactor (d D depth k : ℕ) :=
  stages d k*costEnvelope d D depth k 1+8+4*stages d k+18*stages d k*D^depth

def hardware (d D depth k : ℕ) :=
  15+stages d k*suffixText D depth k+(15+stages d k*39)

def footprintFactor (C d D depth k : ℕ) :=
  C+stages d k*factor d D depth+2*(D^depth+1)+stages d k*D^depth

theorem count_stages (z d k : ℕ) : count z d k=stages d k := count_eq z d k

theorem stage_clock (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (hd : 1≤d) :
    sh.stageClock S depth i ≤ costEnvelope d S.degree depth k 1*2^z := by
  have longer := clock_linear S (stage i) (sh.cfg S depth i) hd rfl
  change subdivisionConstant d*2^z+sh.stageClock S depth i≤_ at longer
  exact (Nat.le_add_left ..).trans longer

/-- All stage/sign executions and the final native scan that copies the decision bits. -/
theorem clock_linear (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) (hd : 1≤d) :
    sh.clock S z d k depth≤timeFactor d S.degree depth k*2^z := by
  let C := stages d k
  let E := costEnvelope d S.degree depth k 1
  let Q := S.degree^depth
  have total : (∑ i : Key z d k, sh.stageClock S depth i)≤C*(E*2^z) := by
    calc
      _ ≤ ∑ _i : Key z d k, E*2^z := Finset.sum_le_sum fun i _ => sh.stage_clock S depth i hd
      _ = C*(E*2^z) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [show (permutationFabric z d).shapes.length*(2*k)=C from count_stages z d k]
        simp only [Nat.cast_id]
  have pack := ProtocolRAMPurchaseFlagPack.ticks (fun i : Key z d k => sh.flagBank S depth i)
    (paths z S.degree depth) (sh.flagsBase S z d k depth)
  change _ ≤ 4+count z d k*(4+18*(2^z*Q)) at pack
  rw [count_stages] at pack
  have flat : 8+4*C≤(8+4*C)*2^z := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  calc
    _ ≤ C*(E*2^z)+4+(4+C*(4+18*(2^z*Q))) :=
      Nat.add_le_add (Nat.add_le_add_right total 4) pack
    _ = C*E*2^z+((8+4*C)+(18*C*Q)*2^z) := by ring
    _ ≤ C*E*2^z+((8+4*C)*2^z+(18*C*Q)*2^z) :=
      Nat.add_le_add_left (Nat.add_le_add_right flat _) _
    _ = _ := by dsimp [timeFactor,C,E,Q]; ring

theorem stage_text (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) :
    text (sh.stageProgram S depth i) ≤ suffixText S.degree depth k := by
  let t := stage i
  let c := sh.cfg S depth i
  let s := embedded S t c
  let b := sign S t c
  have tail := signed_text s b (axis i) (wordBits z d copies) (2^z)
    (Fintype.card (stageAt z d t).Group) (stageAt z d t).span depth
  rw [stageProgram,text_seq,dispatch_text]
  exact Nat.add_le_add_right tail 525

private theorem sweep_text {I : Type*} {w : ℕ} (cpu : I → Procedure w) (K : ℕ)
    (small : ∀ i,text (cpu i)≤K) (order : List I) :
    text (ProtocolRAMFrozenSweep.program cpu order)≤15+order.length*K := by
  induction order with
  | nil =>
    have empty := columns_text w 0 0 0 [] (by simp)
    simpa [ProtocolRAMFrozenSweep.program,ProbeStage.Native.columns] using empty
  | cons i rest ih =>
    simp only [ProtocolRAMFrozenSweep.program,text_seq,List.length_cons,Nat.succ_mul]
    have bound := Nat.add_le_add (small i) ih
    omega

/-- Address and word values are immediates. Every instruction, register and public slot is counted. -/
theorem hardware_bound (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) :
    text (sh.program S z d k depth)≤hardware d S.degree depth k := by
  let cpu := fun i : Key z d k => sh.stageProgram S depth i
  let source := fun i : Key z d k => sh.flagBank S depth i
  have run := sweep_text cpu (suffixText S.degree depth k) (sh.stage_text S depth) (List.finRange (count z d k))
  have pack := columns_text (wordBits z d copies) (paths z S.degree depth) (sh.flagsBase S z d k depth) 7
    (ProtocolRAMPurchaseFlagPack.terms source) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      simp only [Expr.work, Nat.reduceAdd, le_refl])
  have length : (ProtocolRAMPurchaseFlagPack.terms source).length = count z d k := by
    simp only [ProtocolRAMPurchaseFlagPack.terms, List.length_ofFn, count]
  change text (ProtocolRAMPurchaseFlagPack.code (wordBits z d copies) source
    (paths z S.degree depth) (sh.flagsBase S z d k depth)) ≤
    15 + (ProtocolRAMPurchaseFlagPack.terms source).length * 39 at pack
  rw [length] at pack
  rw [program,text_seq]
  apply (Nat.add_le_add run pack).trans
  have orderSize : @List.length (Key z d k) (List.finRange (count z d k)) = stages d k :=
    (List.length_finRange (n := count z d k)).trans (count_stages z d k)
  exact (congrArg₂ (fun a b => 15 + a * suffixText S.degree depth k + (15 + b * 39))
    orderSize (count_stages z d k)).le

/-- The three physical hardware counts have the same address-independent bound. -/
theorem hardware_fields (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) :
    let p := sh.program S z d k depth
    let cap := hardware d S.degree depth k
    p.labels ≤ cap ∧ p.registers ≤ cap ∧ p.slots ≤ cap := by
  have cap := sh.hardware_bound S z d k depth
  unfold text at cap
  dsimp
  omega

theorem decision_words (z d k D depth : ℕ) :
    count z d k*paths z D depth=(stages d k*D^depth)*2^z := by
  rw [count_stages,paths]; ring

/-- Bound every writable word, including all disjoint per-sign slabs and their packed exports. -/
theorem footprint (sh : Shelf) (S : PurchaseSampler) (z d k depth C : ℕ)
    (start : sh.firstBase≤heapEnd z d copies+C*2^z) :
    sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤
      heapEnd z d copies+footprintFactor C d S.degree depth k*2^z := by
  let A := stages d k
  let Q := S.degree^depth
  let B := factor d S.degree depth
  have small : 2≤2*2^z := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  unfold flagsBase paths blockSize
  rw [count_stages]
  calc
    _ ≤ heapEnd z d copies+C*2^z+A*(B*2^z)+2*(2^z*Q+1)+A*(2^z*Q) := by
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right start _) _) _
    _ = heapEnd z d copies+(C+A*B+2*Q+A*Q)*2^z+2 := by ring
    _ ≤ heapEnd z d copies+(C+A*B+2*Q+A*Q)*2^z+2*2^z := Nat.add_le_add_left small _
    _ = _ := by dsimp [footprintFactor,A,Q,B]; ring

theorem eventually_room (S : PurchaseSampler) (d k depth C : ℕ) :
    ∀ᶠ z : ℕ in atTop, ∀ sh : Shelf, sh.firstBase≤heapEnd z d copies+C*2^z →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies := by
  filter_upwards [eventually_append_room d copies (footprintFactor C d S.degree depth k)] with z room
  exact fun sh start => (sh.footprint S z d k depth C start).trans_lt room

theorem eventually_budget (S : PurchaseSampler) (d k depth : ℕ) (hd : 1≤d) :
    ∀ᶠ z : ℕ in atTop, ∀ sh : Shelf,
      sh.clock S z d k depth<2^wordBits z d copies ∧ text (sh.program S z d k depth)<2^wordBits z d copies := by
  filter_upwards [eventually_append_room d copies (timeFactor d S.degree depth k),
    eventually_append_room d copies (hardware d S.degree depth k)] with z time space
  intro sh
  have tic := sh.clock_linear S z d k depth hd
  have hw := sh.hardware_bound S z d k depth
  have grow : hardware d S.degree depth k≤hardware d S.degree depth k*2^z :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  exact ⟨tic.trans_lt ((Nat.le_add_left ..).trans_lt time),
    (hw.trans grow).trans_lt ((Nat.le_add_left ..).trans_lt space)⟩


end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
