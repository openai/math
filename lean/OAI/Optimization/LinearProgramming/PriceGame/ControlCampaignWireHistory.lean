import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWireCursor
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces

/-! Bounds on an actual campaign prefix. Only already returned rounds enter the
invariant. A finite extension shows that the uniform horizon bound applies at this cursor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open Campaign Learning

attribute [local irreducible] Moment.probes runRound TrialExecution.runReference
  TrialExecution.run TrialExecution.execute

def CertifiedHistory {N : ℕ} (R T t : ℕ) (old : ℕ → RoundResult N) : Prop :=
  ∀ j < t, RoundFits (campaignPriceBits N R T) (old j) ∧
    PublicRoundBounds (population R old j) (old j)

def HistoryGood {N : ℕ} (a : Fin N) (R T t : ℕ) (p : Population N) (positive : ℕ) : Prop :=
  ∃ old : ℕ → RoundResult N, p = population R old t ∧ positive = votesBefore a old t ∧
    CertifiedHistory R T t old

private theorem votes_agree {N : ℕ} (a : Fin N) (t : ℕ) {old new : ℕ → RoundResult N}
    (same : ∀ i < t, old i = new i) : votesBefore a old t = votesBefore a new t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [votesBefore,ih (fun i hi => same i (by omega)),same t (by omega)]

private theorem update_agrees {N t : ℕ} (old : ℕ → RoundResult N) (o : RoundResult N)
    {i : ℕ} (hi : i < t) : Function.update old t o i = old i :=
  Function.update_of_ne (by omega : i ≠ t) o old

private theorem certified_update {N R T t : ℕ} {old : ℕ → RoundResult N}
    (prior : CertifiedHistory R T t old) {o : RoundResult N}
    (now : RoundFits (campaignPriceBits N R T) o ∧ PublicRoundBounds (population R old t) o) :
    CertifiedHistory R T (t+1) (Function.update old t o) := by
  intro j hj
  have state := population_congr R (old := Function.update old t o) (new := old) j
    (fun i hi => update_agrees old o (by omega))
  rw [state]
  by_cases eq : j=t
  · subst j
    simpa only [Function.update_self] using now
  · rw [Function.update_of_ne eq]
    exact prior j (by omega)

private theorem receipt_of_emits {N : ℕ} {A : Type} {p : Computation N A} {tr out}
    {P : A → Prop} {Q : Query N → Prop}
    (e : Trial.Emits p tr out) (guard : p.Guarded Q P) : P out := by
  induction e with
  | pure => exact guard
  | ask b _ ih => exact ih (guard.2 b)

theorem historyGood_start {N : ℕ} (a : Fin N) (R T : ℕ) :
    HistoryGood a R T 0 (.start (Pool.batch N R)) 0 :=
  ⟨fun _ => ⟨fun _ => 0,fun _ => 0,[]⟩,rfl,rfl,fun _ h => by omega⟩

theorem HistoryGood.advance {N R T t : ℕ} {a : Fin N} {p : Population N} {positive : ℕ}
    (good : HistoryGood a R T t p positive) (ht : t < T) {tr o}
    (e : Trial.Emits (runRound R (Driver.commonMarkets N) p) tr o) :
    HistoryGood a R T (t+1) (p.advance (Pool.batch N R) o) (positive + vote a o) := by
  obtain ⟨old,rfl,rfl,prior⟩ := good
  change Trial.Emits (runRound R (fun es => TrialExecution.marketSolverAtCommonWeightUnit es)
    (population R old t)) tr o at e
  have now : RoundFits (campaignPriceBits N R T) o ∧ PublicRoundBounds (population R old t) o :=
    receipt_of_emits (Q := PricesBounded (campaignPriceBits N R T))
      (P := fun x => RoundFits (campaignPriceBits N R T) x ∧ PublicRoundBounds (population R old t) x)
      e (oneRound_prices_with_history a R T old t ht.le (fun j hj => (prior j hj).2.observations))
  let new := Function.update old t o
  have same : ∀ i < t, old i = new i := fun i hi => (update_agrees old o hi).symm
  have endRound : new t = o := Function.update_self ..
  refine ⟨new,?_,?_,certified_update prior now⟩
  · change (population R old t).advance _ o = (population R new t).advance _ (new t)
    rw [population_congr R t same,endRound]
  · change votesBefore a old t + vote a o = votesBefore a new t + vote a (new t)
    rw [votes_agree a t same,endRound]

/-- Continue any recorded prefix with genuine rounds on a fixed answer tape. This
is only used to apply a uniform bound that is stated for a full public horizon. -/
private theorem extend_certified {N R T t : ℕ} (a : Fin N) {old : ℕ → RoundResult N}
    (prior : CertifiedHistory R T t old) (ht : t ≤ T) :
    ∃ new : ℕ → RoundResult N, (∀ j < t, old j = new j) ∧ CertifiedHistory R T T new := by
  have extend (d : ℕ) (hd : t+d ≤ T) :
      ∃ new : ℕ → RoundResult N, (∀ j < t, old j = new j) ∧ CertifiedHistory R T (t+d) new := by
    induction d with
    | zero => exact ⟨old,fun _ _ => rfl,prior⟩
    | succ d ih =>
      obtain ⟨past,same,cert⟩ := ih (by omega)
      let k := t+d
      let next := (runRound R (fun es => TrialExecution.marketSolverAtCommonWeightUnit es)
        (population R past k)).run (fun _ _ => false) []
      have valid : RoundFits (campaignPriceBits N R T) next ∧ PublicRoundBounds (population R past k) next :=
        Computation.Guarded.run (Q := PricesBounded (campaignPriceBits N R T))
          (P := fun x => RoundFits (campaignPriceBits N R T) x ∧ PublicRoundBounds (population R past k) x)
          (p := runRound R (fun es => TrialExecution.marketSolverAtCommonWeightUnit es) (population R past k))
          (oneRound_prices_with_history a R T past k (by dsimp [k]; omega)
            (fun j hj => (cert j hj).2.observations)) (fun _ _ => false) []
      refine ⟨Function.update past k next,?_,certified_update cert valid⟩
      intro j hj
      exact (same j hj).trans (update_agrees (t:=k) past next (i:=j) (by dsimp [k]; omega)).symm
  have endTime : t+(T-t)=T := by omega
  simpa only [endTime] using extend (T-t) endTime.le

theorem sourceCursor_length_prefix {N : ℕ} (a : Fin N) (R T t : ℕ) (ht : t≤T)
    (old : ℕ → RoundResult N) (good : CertifiedHistory R T t old) :
    (campaignCursorCode (Driver.sourceCursor R T (T-t) a (population R old t) (votesBefore a old t))).length ≤
      cursorWidth N R T := by
  obtain ⟨new,same,cert⟩ := extend_certified a good ht
  rw [population_congr R t same,votes_agree a t same]
  exact sourceCursor_length a R T _ _ t new (Nat.sub_le ..) ((votesBefore_le a new t).trans ht) ht
    (fun j hj => (cert j hj).2) (fun j hj => (cert j hj).1)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
