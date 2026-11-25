import OAI.Hierarchy.DescentSeedRejectTable
import OAI.Hierarchy.DescentSeedHeaderCharge
import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentTerminalEpochLoadPins
import OAI.Hierarchy.DescentPackedSeedHeader
import OAI.Hierarchy.DescentPackedRejection

namespace OAI
/-! # Compact original seed, Boolean epoch shelves, and native one-bit seed admission -/
namespace Hierarchy.DescentTerminalPackedSeedFlags
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentSIMDLookup Computability.BorderVNP.Crossing Catalyst Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory PrivateRAM ProtocolRAM
open ThreeFlat Routing Diagonal TraceBanks RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F A : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s w : ℕ)
set_option quotPrecheck false
local notation "seedLanes" => DescentPackedSeed.multiplicity w s
local notation "d" => digitsNeeded s
local notation "N" => DescentPackedSeed.rows X R s w

def before (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool) : Memory w :=
  DescentTerminalEpochHeader.memory (start X R s w) ts z
    (initialMemory (DescentPackedSeed.headerWords X R s w) (DescentPackedSeed.base X w (z∘sel)))

def initial (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool) : Memory w :=
  let rom:=dictionary X R s w ts
  initialMemory (endInput X R s w ts) fun a=>
    if a < rom.base then before X R s w ts sel z a else (advice s seedLanes (a-rom.base):Word w)

theorem lower (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool) {i : ℕ}
    (low : i < (dictionary X R s w ts).base) :
    initial X R s w ts sel z i=before X R s w ts sel z i := by
  have inside : i < endInput X R s w ts := by unfold endInput;omega
  simp [initial,initialMemory,low,inside]

theorem source_stored (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool)
    (j : DescentPackedSeed.PackedRow X R s w) :
    initial X R s w ts sel z ((source X R s w).base+(row _ _ _ j).val) =
      ((data (DescentPackedSeed.cells X (z∘sel)) j).val:Word w) := by
  have h : (row _ _ _ j).val < (source X R s w).size :=
    (row _ _ _ j).isLt.trans_le (Nat.le_pow_clog (by decide) N)
  have old : (source X R s w).base+(row _ _ _ j).val < start X R s w := by unfold start;omega
  rw [lower X R s w ts sel z (by change _ < start X R s w+_;omega)]
  rw [before,DescentTerminalEpochHeader.initial_frame _ _ _ _ old]
  exact DescentPackedSeed.data_at X w (z∘sel) j

theorem advice_stored (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool) :
    DescentPackedRejection.Table (M:=seedLanes) (predicate s) (dictionary X R s w ts) (initial X R s w ts sel z) := by
  intro key
  have inside : (dictionary X R s w ts).base + key.val < endInput X R s w ts := by
    unfold endInput
    exact Nat.add_lt_add_left key.isLt _
  have branch : ¬ (dictionary X R s w ts).base + key.val < (dictionary X R s w ts).base := by omega
  have keyEq : (key.val : Cell (d*seedLanes)) = key :=
    Fin.ext (Fin.val_cast_of_lt key.isLt)
  simp only [initial, initialMemory, ite_eq_left inside, ite_eq_right branch, Nat.add_sub_cancel_left, advice, keyEq]

def check (ts : List (Source A)) := DescentPackedScore.raw (source X R s w) (dictionary X R s w ts)
  (endInput X R s w ts) 1 (Fintype.card (Old X)) (R*8) seedLanes w

theorem run (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool)
    (wide : 2*d ≤ w) (room : endInput X R s w ts + (N+1) < 2^w) :
    let m := initial X R s w ts sel z
    let out := endInput X R s w ts
    (check X R s w ts).Spec (·=m) (fun _ o =>
      o (out+N)=(if valid X (z∘sel) then 0 else 1) ∧ ∀i < out,o i=m i)
      (4+(N+1)*66) ∧ CheapCode (check X R s w ts) := by
  let src:=source X R s w
  let rom:=dictionary X R s w ts
  let out:=endInput X R s w ts
  let m:=initial X R s w ts sel z
  have oldSize : N ≤ src.size := Nat.le_pow_clog (by decide) N
  have old : src.Fits w out := by
    have h : src.base+src.size ≤ out := by
      change start X R s w ≤ start X R s w+DescentTerminalEpochHeader.extent ts+rom.size
      omega
    have upper : out < 2^w := by dsimp [out];omega
    exact ⟨Nat.two_pow_pos _,by omega,h⟩
  have new_ : rom.Fits w out := by
    have end_ : rom.base+rom.size=out := rfl
    have upper : out < 2^w := by dsimp [out];omega
    exact ⟨Nat.two_pow_pos _,by omega,end_.le⟩
  have pos : 0 < seedLanes := DescentPackedSeed.multiplicity_pos wide
  have source_ := source_stored X R s w ts sel z
  have table := advice_stored X R s w ts sel z
  have native := DescentPackedRejection.run src rom out (predicate s) (DescentPackedSeed.cells X (z∘sel)) m
    (by simp [predicate]) pos old new_ oldSize rfl room source_ table
  refine ⟨?_,native.2⟩
  refine Procedure.Spec.mono (A := check X R s w ts) native.1 (fun _ h => h) ?_ le_rfl
  intro _ o h
  have char : (∀v j,predicate s (DescentPackedSeed.cells X (z∘sel) v j)=0) ↔ valid X (z∘sel) := by
    simp [predicate,DescentPackedSeed.valid_iff]
  refine ⟨?_, fun i hi => h.2 i (Or.inl hi)⟩
  change o (out + Fintype.card (Old X) * chunks (R * 8) seedLanes) = _
  by_cases good : valid X (z ∘ sel)
  · simpa only [ite_eq_left good, ite_eq_left (char.mpr good)] using h.1
  · simpa only [ite_eq_right good, ite_eq_right (mt char.mp good)] using h.1

/-- A literal projection on every address of the compact original seed, epoch arrays, and ROM. -/
def pin (ts : List (Source A)) (sel : Select X R s→ A) (a : ℕ) (j : Fin (w+1)) : A⊕Bool :=
  if a < start X R s w then
    if ia : a < DescentPackedSeed.headerWords X R s w then
      (DescentPackedSeed.headerPin X R s w (⟨a,ia⟩,j)).map sel id else .inr false
  else if a < (dictionary X R s w ts).base then DescentTerminalEpochHeader.loadPin w ts (a-start X R s w) j
  else if a < endInput X R s w ts then
    .inr (TraceWords.bits (TraceBanks.wide (advice s seedLanes (a-(dictionary X R s w ts).base):Word w)) j)
  else .inr false

theorem pin_at (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool)
    (wide : ∀a∈ts,width a.C ≤ w) (a : ℕ) (j : Fin (w+1)) :
    (pin X R s w ts sel a j).elim z id=TraceWords.bits (TraceBanks.wide (initial X R s w ts sel z a)) j := by
  by_cases low : a < start X R s w
  · have prior : a < (dictionary X R s w ts).base := by change _ < start X R s w+_;omega
    rw [lower X R s w ts sel z prior,before,DescentTerminalEpochHeader.initial_frame _ _ _ _ low]
    by_cases inside : a < DescentPackedSeed.headerWords X R s w
    · have read := DescentPackedSeed.headerPin_at X w (z∘sel) (⟨a,inside⟩,j)
      simp only [pin,ite_eq_left low,dite_eq_left inside,initialMemory,ite_eq_left inside]
      generalize hp : DescentPackedSeed.headerPin X R s w (⟨a,inside⟩,j)=p at *
      cases p <;> exact read
    · simp [pin,low,inside,initialMemory,TraceWords.bits,TraceBanks.wide]
  · by_cases mid : a < (dictionary X R s w ts).base
    · rw [lower X R s w ts sel z mid]
      change _=TraceWords.bits (TraceBanks.wide (DescentTerminalEpochHeader.memory (start X R s w) ts z _ a)) j
      have live : a < start X R s w + DescentTerminalEpochHeader.extent ts := mid
      simpa only [pin,ite_eq_right low,ite_eq_left mid,DescentTerminalEpochHeader.memory,initialMemory,ite_eq_left live] using
        DescentTerminalEpochHeader.load_pin w ts z wide (a-start X R s w) j
    · by_cases high : a < endInput X R s w ts <;>
        simp [pin,initial,initialMemory,low,mid,high,TraceWords.bits,TraceBanks.wide]

theorem epochs_read (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool) {p : DescentTerminalEpochHeader.Shelf A}
    (hp : p∈DescentTerminalEpochHeader.directory (start X R s w) ts) (fit : width p.source.C ≤ w)
    (j : Fin p.source.seats) :
    (initial X R s w ts sel z (p.codes.base+j.val)).val=DescentTerminalEpochBits.raw (z∘p.source.pin) j := by
  have bound := DescentTerminalEpochHeader.placed _ _ hp
  have ij := j.isLt.trans_le bound.2.1
  rw [lower X R s w ts sel z (by change _ < start X R s w+DescentTerminalEpochHeader.extent ts;omega)]
  exact DescentTerminalEpochHeader.physical _ _ z _ hp fit j

/-- The seed checker hands the next native phase the raw, fixed profile
banks and the scalar word certifying the exact compact-census predicate. -/
theorem ready (ts : List (Source A)) (sel : Select X R s→ A) (z : A→ Bool)
    (wide : 2*d ≤ w) (room : endInput X R s w ts+(N+1) < 2^w) :
    let m := initial X R s w ts sel z
    let out := endInput X R s w ts
    (check X R s w ts).Spec (·=m) (fun _ o =>
      (o (out+N)=0 ↔ valid X (z∘sel)) ∧
      (∀p∈DescentTerminalEpochHeader.directory (start X R s w) ts,∀j : Fin p.source.seats,
        o (p.codes.base+j.val) = before X R s w ts sel z (p.codes.base+j.val)) ∧
      ∀i < out,o i=m i) (4+(N+1)*66) := by
  refine Procedure.Spec.mono (A := check X R s w ts) (run X R s w ts sel z wide room).1
    (fun _ h => h) ?_ le_rfl
  intro _ o h
  have one : (1:Word w)≠0 := by
    intro eqn
    have n : 1 < 2^w := by omega
    have val := congrArg Fin.val eqn
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt n, Fin.val_zero] at val
    exact Nat.one_ne_zero val
  refine ⟨?_,?_,h.2⟩
  · rw [h.1]
    by_cases good : valid X (z∘sel) <;> simp [good,one]
  · intro p hp j
    have addr := DescentTerminalEpochHeader.placed (start X R s w) ts hp
    have site := j.isLt.trans_le addr.2.1
    have low : p.codes.base+j.val < (dictionary X R s w ts).base := by
      change _ < start X R s w+DescentTerminalEpochHeader.extent ts
      exact (Nat.add_lt_add_left site p.codes.base).trans_le addr.2.2
    have beforeEnd : p.codes.base+j.val < endInput X R s w ts := low.trans_le (Nat.le_add_right _ _)
    exact (h.2 _ beforeEnd).trans (lower X R s w ts sel z low)

theorem header_bits (ts : List (Source A)) (wide : 2*d ≤ w) :
    endInput X R s w ts*w ≤
      2*((6+90*(X.size+1))*w+320*(X.size+1)*R*d)+
        (1+DescentTerminalEpochHeader.extent ts+2^(w/2))*w := by
  calc
    _ ≤ (2*DescentPackedSeed.headerWords X R s w+1+DescentTerminalEpochHeader.extent ts+2^(w/2))*w :=
      Nat.mul_le_mul_right w (header_extent X R s w ts wide)
    _ = 2*(DescentPackedSeed.headerWords X R s w*w)+(1+DescentTerminalEpochHeader.extent ts+2^(w/2))*w := by ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left 2 (DescentPackedSeed.startup_bits X R s w wide)) _


end
end Hierarchy.DescentTerminalPackedSeedFlags

end OAI
