import OAI.Hierarchy.DescentTerminalEpochChart
import OAI.Hierarchy.DescentSeedProjection
import OAI.Hierarchy.DescentTerminalSeedSelectors
import OAI.Hierarchy.DescentScheduledBitHistory
import OAI.Hierarchy.DescentMatchedPublication

namespace OAI
/-! # One original Boolean selector encoding for every reached terminal history -/

namespace Hierarchy.DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentTerminalEpochBits DescentPacking DescentSixParty
open DescentKernelHistory.BitDescription DescentInitialHost Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ}
variable (G : PoweredGadget F) {u ε : ℝ} (hu : 0 ≤ u) (he : 0 ≤ ε)

abbrev Numbering := ∀ (W : MarkedWorld F d P portBits) (T : StageInput W G u ε),
  (scannedRows he T).pairs ≃ Fin (Fintype.card (scannedRows he T).pairs)

/-- The branch's native dense pair order, including all gaps in the occupied colony directory. -/
def dense : Numbering (d:=d) (portBits:=portBits) G (u:=u) he :=
  fun W T =>
    let r := scannedRows he T
    PairRAM.globalNumber W.graph W.core (scanHome T r.μ) (scanColor T r.μ r.α r.β) T.cap

variable (order : Numbering (d:=d) (portBits:=portBits) G (u:=u) he)
variable {H : Histories F d P portBits} (input : SubroundInput H G (u:=u) he)

def count (c : H.Choice) := Fintype.card (scannedRows he (input.placement c)).pairs
def maxSeats := Finset.univ.sup (count G he input)

theorem count_le (c : H.Choice) : count G he input c ≤ maxSeats G he input :=
  Finset.le_sup (Finset.mem_univ c)

theorem maxSeats_le {bound : ℕ} (h : ∀c,count G he input c ≤ bound) : maxSeats G he input ≤ bound :=
  Finset.sup_le fun c _=>h c

set_option maxHeartbeats 1200000 in
/-- Each pair has two distinct actual matched core edges. -/
theorem count_core (c : H.Choice) : 2*count G he input c ≤ (H.state c).core.card := by
  let T := input.placement c
  let r := scannedRows he T
  let f : r.pairs×Fin 2 ↪ ((H.state c).core : Type) :=
    ⟨fun i=>⟨r.pick i,r.picked i⟩,fun _ _ eqn=>r.pick.injective (congrArg Subtype.val eqn)⟩
  change 2 * Fintype.card r.pairs ≤ (H.state c).core.card
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.mul_comm 2] using
    (Fintype.card_le_of_embedding f)

theorem maxSeats_core :
    maxSeats G he input ≤ (Finset.univ.sup fun c : H.Choice=>(H.state c).core.card)/2 := by
  apply maxSeats_le
  intro c
  have pair := count_core G he input c
  have full := Finset.le_sup (f:=fun c : H.Choice=>(H.state c).core.card) (Finset.mem_univ c)
  omega

variable {S Z : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop}

def extend {source : H.Choice→Z} (old : Chart bits ok source) :
    Chart bits ok (fun v : (H.extend he input).Choice=>source v.1) :=
  DescentTerminalEpochChart.extend old (count G he input)
    (fun c=>order (H.state c) (input.placement c)) (count_le G he input)
    (fun c=>(scannedRows he (input.placement c)).profile)

theorem extend_size {source : H.Choice→Z} (old : Chart bits ok source) :
    Fintype.card (extend G he order input old).Pin =
      Fintype.card old.Pin + maxSeats G he input * DescentTerminalEpochBits.width G.C := by
  change Fintype.card (old.Pin ⊕ Pins G.C (maxSeats G he input))=_
  simp [Pins]

def schedule : {t : ℕ} → {H : Histories F d P portBits} →
    (plan : Schedule G (u:=u) he t H) → {source : H.Choice→Z} → Chart bits ok source →
    Chart bits ok (fun c=>source (Schedule.seedChoice G he plan c))
  | 0,_,_,_,old => old
  | _+1,_,plan,_,old => schedule plan.2 (extend G he order plan.1 old)

def epochs {t h C Ht : ℕ} : {J : ℕ} → {H : Histories F d P portBits} →
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) → {source : H.Choice→Z} →
    Chart bits ok source → Chart bits ok (fun c=>source (Epochs.seedChoice G hu he run c))
  | 0,_,_,_,old => old
  | _+1,_,run,_,old => epochs run.2 (schedule G he order run.1.subrounds old)

def scheduleSeats : {t : ℕ} → {H : Histories F d P portBits} → Schedule G (u:=u) he t H → ℕ
  | 0,_,_ => 0
  | _+1,_,run => maxSeats G he run.1 + scheduleSeats run.2

def epochSeats {t h C Ht : ℕ} : {J : ℕ} → {H : Histories F d P portBits} →
    Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H → ℕ
  | 0,_,_ => 0
  | _+1,_,run => scheduleSeats G he run.1.subrounds + epochSeats run.2

theorem schedule_size {t : ℕ} {H : Histories F d P portBits}
    (plan : Schedule G (u:=u) he t H) {s : H.Choice→Z} (old : Chart bits ok s) :
    Fintype.card (schedule G he order plan old).Pin =
      Fintype.card old.Pin + scheduleSeats G he plan * DescentTerminalEpochBits.width G.C := by
  induction t generalizing H with
  | zero =>
    simp only [schedule, scheduleSeats, Nat.zero_mul, Nat.add_zero];
      exact Fintype.card_congr (Equiv.refl _)
  | succ t ih=>
    rw [schedule,scheduleSeats,ih,extend_size]
    ring

theorem epochs_size {t h C Ht J : ℕ} {H : Histories F d P portBits}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) {s : H.Choice→Z}
    (old : Chart bits ok s) :
    Fintype.card (epochs G hu he order run old).Pin =
      Fintype.card old.Pin + epochSeats G hu he run * DescentTerminalEpochBits.width G.C := by
  induction J generalizing H with
  | zero =>
    simp only [epochs, epochSeats, Nat.zero_mul, Nat.add_zero];
      exact Fintype.card_congr (Equiv.refl _)
  | succ J ih =>
    rcases run with ⟨one, rest⟩
    let next := schedule G he order one.subrounds old
    have tail := ih (H := one.finish G hu he) rest
      (s := fun c => s (Schedule.seedChoice G he one.subrounds c)) next
    have head := schedule_size G he order one.subrounds old
    change _ = Fintype.card old.Pin +
      (scheduleSeats G he one.subrounds + epochSeats G hu he rest) * DescentTerminalEpochBits.width G.C
    exact tail.trans ((congrArg (fun n => n + epochSeats G hu he rest * DescentTerminalEpochBits.width G.C)
      head).trans (by ring))

section Initial
open DescentSeedRoot
variable {k pins : ℕ} (X : Catalyst.Approximation F k pins) (R s w : ℕ) (word : s < 2^w)
set_option quotPrecheck false
local notation "initial" => initialGroup X R s

def seedChart : Chart (selectBit X (R:=R) (s:=s) w) (valid X (R:=R) (s:=s)) (id : (initial).Choice→(initial).Choice) where
  Pin := Select X R s
  seed := id
  store := selectBit X w
  read := DescentSeedRoot.decode X
  rows _ := []
  layout := []
  archived _ := ⟨[],rfl⟩
  complete _ _ _ := rfl
  read_iff := decode_iff X word
  original _ _ := rfl
  accepted z := by
    change (∃t,DescentSeedRoot.decode X z=some t) ↔ valid X z ∧ _
    by_cases h : valid X z <;> simp [DescentSeedRoot.decode,h]

variable {J h C Ht t : ℕ}
local notation "initialRun" => Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initialGroup X R s)
local notation "initialOrder" => Numbering (d:=0)
  (portBits:=fun _ : Σ _j : Fin R, Fin (Fintype.card (Catalyst.Port pins X.width)) => s * 1) G (u:=u) he

def actual (run : initialRun) (order : initialOrder) :
    Chart (selectBit X (R:=R) (s:=s) w) (valid X (R:=R) (s:=s))
      (fun c : (Epochs.finish G hu he run).Choice => Epochs.seedChoice G hu he run c) := by
  exact epochs G hu he order (H:=initialGroup X R s) (t:=t) (h:=h) (C:=C) (Ht:=Ht) (J:=J)
    run (seedChart X R s w word)

theorem once (run : initialRun) (order : initialOrder) (t : (Epochs.finish G hu he run).Choice) :
    let b := actual G hu he X R s w word run order
    ∃! a,b.read a=some t :=
  (actual G hu he X R s w word run order).once t

theorem survives (run : initialRun) (order : initialOrder)
    (z : (actual G hu he X R s w word run order).Pin→Bool) :
    let b := actual G hu he X R s w word run order
    (valid X (z∘b.seed) ∧ ∀r∈b.rows z,r.Valid) ↔ ∃t,b.read z=some t :=
  ((actual G hu he X R s w word run order).accepted z).symm

theorem seedCount (run : initialRun) (order : initialOrder)
    (z : (actual G hu he X R s w word run order).Pin→Bool) (t : (Epochs.finish G hu he run).Choice)
    (hit : (actual G hu he X R s w word run order).read z=some t) (key : CountKey X R) :
    let b := actual G hu he X R s w word run order
    (rawCount X (z∘b.seed) key).val=selected X (Epochs.seedChoice G hu he run t) key := by
  let b := actual G hu he X R s w word run order
  have hs := (b.read_iff z t).mp hit
  have old : z∘b.seed=selectBit X w (Epochs.seedChoice G hu he run t) :=
    funext fun a=>(congrFun hs (b.seed a)).trans (b.original t a)
  exact (congrArg (fun bits => (rawCount X bits key).val) old).trans
    (raw_select X word (Epochs.seedChoice G hu he run t) key)

end Initial


end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
