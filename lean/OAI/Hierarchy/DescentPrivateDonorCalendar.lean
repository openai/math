import OAI.Hierarchy.DescentPrivateDonorDiary
import OAI.Hierarchy.DescentPrivateDonorPopulation
import OAI.Hierarchy.DescentPrivateDonorRates

namespace OAI
/-! # Summing the instructions actually selected in the ordinary donor history -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- A history ending at the chosen terminal age pays for every ordinary donor clock,
ROM in the two-table meter, and both program texts in that same chronological history. -/
theorem calibrated_donor_history_at (t f g reset s a e K τ : ℕ)
    (tailRoom : s+3+(e+5)≤τ) :
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀ B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀ M socket p : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      2^h≤2*M → p≤h → 0<socket → socket≤ scale J e → h≤32*(socket*p) →
      ∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W₀ W : MarkedWorld F d P bits}
        {q ε : ℝ} {k j z₀ D₀ z D wire hist header bw : ℕ}
        {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
        {finish : Reached W G q ε S k S.length z D wire hist}
        {path : Path start finish} {calendar : MeterCalendar start header bw path}
        (diary : DonorDiary start header h bw K p calendar),
        (∀i : Fin (S.length+1),(diary.rows i.val).work≤ scale J s) →
        (∀i : Fin (S.length+1),(diary.rows i.val).amount≤ scale J a) →
        diary.total*2^J≤2*(M*(S.copies*p)) := by
  intro _ B positive bought
  have paid:=donor_calibration_at G t f g reset s a e (2*K) τ tailRoom B positive bought
  have room:=NativeBranch.dates_grain_room G t f g reset τ B
  filter_upwards [paid,room] with h invoice population
  dsimp only
  intro M socket p source grain occupied packed cpu P d bits W₀ W q ε k j z₀ D₀ z D wire hist header bw
    start finish path calendar diary works amounts
  rw [←diary.entries_sum (Nat.le_succ _)]
  exact invoice M socket p occupied packed cpu
    (fun i=>(diary.rows i.val).cost) (fun i=>(diary.rows i.val).work) (fun i=>(diary.rows i.val).amount)
    works amounts (fun i=>diary.rows_charge (Nat.two_pow_pos _) (fun v=>population M p v source grain) i.val)

theorem calibrated_donor_history (t f g reset s a e K : ℕ) :
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀ B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀ M socket p : ℕ, let S:=stageNumbers G t J f g reset M (tail (s+3+(e+5)) J)
      2^h≤2*M → p≤h → 0<socket → socket≤ scale J e → h≤32*(socket*p) →
      ∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W₀ W : MarkedWorld F d P bits}
        {q ε : ℝ} {k j z₀ D₀ z D wire hist header bw : ℕ}
        {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
        {finish : Reached W G q ε S k S.length z D wire hist}
        {path : Path start finish} {calendar : MeterCalendar start header bw path}
        (diary : DonorDiary start header h bw K p calendar),
        (∀i : Fin (S.length+1),(diary.rows i.val).work≤ scale J s) →
        (∀i : Fin (S.length+1),(diary.rows i.val).amount≤ scale J a) →
        diary.total*2^J≤2*(M*(S.copies*p)) :=
  by
    intro n B positive paid
    exact calibrated_donor_history_at G t f g reset s a e K (s+3+(e+5)) le_rfl B positive paid

end Hierarchy.DescentSixParty.Chronology

end OAI
