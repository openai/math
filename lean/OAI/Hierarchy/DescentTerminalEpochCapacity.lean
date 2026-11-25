import OAI.Hierarchy.DescentTerminalEpochDecoder
import OAI.Hierarchy.DescentChronologicalCapacity
import OAI.Hierarchy.DescentWholeEpochs

namespace OAI
/-! # Uniform paid envelope of every fixed selector shelf of the actual complete run -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentCompiler DescentSixParty.Chronology DescentKernelHistory.BitDescription
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {q ε u : ℝ} (G : PoweredGadget F)
variable (hu : 0 ≤ u) (he : 0 ≤ ε) {k : ℕ} {S : AtomSchedule}

def selectionCount (s : Selection F P d b G ε) := Fintype.card (scannedRows s.nonneg s.stage).pairs

theorem at_link {W : MarkedWorld F d P b} {i z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k i z D wire hist}
    {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T p n target) (radix : S.radix=2^k) (age : i ≤ S.length) :
    selectionCount G ticket.selection ≤ S.batch := by
  have h:=source.pairs_le age radix he T
  have exp : 8+S.capGain*i ≤ 11+S.capGain*S.length := by
    have := Nat.mul_le_mul_left S.capGain age
    omega
  have cap := Nat.mul_le_mul_left (Reached.siteLimit S)
    (Nat.pow_le_pow_right (by decide : 0 < 2) exp)
  change Fintype.card (scannedRows he T).pairs ≤ Reached.siteLimit S * 2^(11+S.capGain*S.length)
  omega

theorem path_paid {W A : MarkedWorld F d P b} {i z D j z' D' wire hist : ℕ}
    {start : Reached W G q ε S k i z D wire hist} {arrive : Reached A G q ε S k j z' D' wire hist}
    (p : Path start arrive) (radix : S.radix=2^k) (age : j ≤ S.length) :
    ∀s∈p.selections,selectionCount G s ≤ S.batch := by
  induction p with
  | here=>simp [Path.selections]
  | ordinary prev ticket ih=>
    intro s hs
    rcases List.mem_append.mp hs with old|now
    · exact ih (by omega) s old
    · have same : s=ticket.selection := List.mem_singleton.mp now
      subst s
      exact at_link G _ ticket radix (by omega)
  | reset prev ctl ih=>
    exact ih (by omega)

theorem schedule_source_surjective {H : Histories F d P b} {t : ℕ}
    (run : Schedule G (u:=u) he t H) : Function.Surjective (sourceChoice he run) := by
  induction t generalizing H with
  | zero=>exact fun c=>⟨c,rfl⟩
  | succ t ih=>
    intro c
    let T := run.1.placement c
    let zero : Profile G.C := ⟨fun _=>0,by simp⟩
    let row := (scannedRows he T).profile.symm (fun _=>zero)
    obtain ⟨last,h⟩:=ih run.2 ⟨c,row⟩
    exact ⟨last,congrArg Sigma.fst h⟩

theorem epochs_source_surjective {H : Histories F d P b} {t J h C Ht : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) : Function.Surjective (epochsSource G run) := by
  induction J generalizing H with
  | zero=>exact fun c=>⟨c,rfl⟩
  | succ J ih=>
    exact (schedule_source_surjective G he run.1.subrounds).comp (ih run.2)

/-- Every starting choice extends through the tail by selecting the zero profile. -/
theorem first_shelf_paid {H : Histories F d P b} {n B : ℕ} (run : Schedule G (u:=u) he (n+1) H)
    (paid : ∀c,∀s∈scheduled he run c,selectionCount G s ≤ B) : maxSeats G he run.1 ≤ B :=by
  obtain ⟨data,tail⟩ := run
  apply maxSeats_le
  intro c
  let T:=data.placement c
  let prof := (scannedRows he T).profile.symm (fun _=>⟨fun _=>0,by simp⟩)
  let v : (H.extend he data).Choice := ⟨c,prof⟩
  obtain ⟨last,recover⟩:=schedule_source_surjective G he tail v
  let s : Selection F P d b G ε := ⟨_,_,he,T,prof,data.reblock c prof⟩
  have hs : s∈scheduled he (n:=n+1) ⟨data,tail⟩ last := by
    simp only [scheduled,List.mem_cons]
    left
    change sourceChoice he tail last = v at recover
    rw [recover]
  exact paid last s hs

theorem scheduled_paid {H : Histories F d P b} {n B : ℕ} (run : Schedule G (u:=u) he n H)
    (paid : ∀c,∀s∈scheduled he run c,selectionCount G s ≤ B) :
    scheduleSeats G he run ≤ n*B := by
  induction n generalizing H with
  | zero=>simp [scheduleSeats]
  | succ n ih=>
    have first:=first_shelf_paid G he run paid
    have rest := ih run.2 (fun c s hs=>paid c s (List.mem_cons_of_mem _ hs))
    rw [scheduleSeats,Nat.succ_mul]
    omega

theorem epochs_paid {H : Histories F d P b} {t J h C Ht B : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)
    (paid : ∀c,∀s∈epochsSelections G run c,selectionCount G s ≤ B) :
    epochSeats G hu he run ≤ J*(t*B) := by
  induction J generalizing H with
  | zero=>simp [epochSeats]
  | succ J ih=>
    obtain ⟨one,rest⟩:=run
    have first : scheduleSeats G he one.subrounds ≤ t*B := by
      apply scheduled_paid G he
      intro c s hs
      obtain ⟨last,eq⟩:=epochs_source_surjective G hu he rest c
      exact paid last s (List.mem_append_left _ (by simpa only [eq] using hs))
    have after := ih rest (fun c s hs=>paid c s (List.mem_append_right _ hs))
    change scheduleSeats G he one.subrounds + epochSeats G hu he rest ≤ (J+1)*(t*B)
    rw [Nat.succ_mul]
    omega

theorem paid_by_paths {H : Histories F d P b} {h C Ht : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=S.rounds) S.height H)
    (radix : S.radix=2^k)
    (links : ∀c : (Epochs.finish G hu he run).Choice,
      ∃ (i z D j z' D' wire hist : ℕ) (W A : MarkedWorld F d P b)
        (start : Reached W G q ε S k i z D wire hist) (arrive : Reached A G q ε S k j z' D' wire hist)
        (p : Path start arrive),j ≤ S.length ∧ p.selections=epochsSelections G run c) :
    epochSeats G hu he run ≤ S.length*S.batch := by
  have paid := epochs_paid G hu he run (B:=S.batch) (fun c s hs=>by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,p,age,match_⟩:=links c
    exact path_paid G p radix age s (by simpa only [match_] using hs))
  have h := Nat.mul_le_mul_right S.height (show S.rounds ≤ S.rounds+1 by omega)
  calc
    _ ≤ S.height*(S.rounds*S.batch) := paid
    _ = (S.rounds*S.height)*S.batch := by ring
    _ ≤ S.length*S.batch := Nat.mul_le_mul_right _ h

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
