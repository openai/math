import OAI.Computability.BorderVNP.DiagonalChosenReader
import OAI.Computability.BorderVNP.DiagonalFixedCube
import OAI.Computability.BorderVNP.DiagonalUniformResources

/-! # The final scale and quantifier inference of the border stretch theorem

The remaining program obligation has two concrete outputs on the same wired
signed machine. They are the exact polynomial expansion and the native live
column. The arithmetic branch independently rules out that pair of outputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial VPVNP Filter
open scoped Classical BigOperators

/-- Public physical sizes chosen for the stretch proof before the later field
and matrix pin. A team count is positive by construction. -/
structure StretchSchedule where
  /-- Exponent in the candidate gate count. -/
  σ : ℝ
  /-- Exponent in the number of processors per team. -/
  ρ : ℝ
  positive : 0 < σ
  separated : σ < ρ
  /-- One less than the number of teams. -/
  teamsPred : ℕ → ℕ
  /-- Bits on each direct exterior link per processor. -/
  link : ℕ → ℕ
  /-- Binary width of each table-entry occurrence count. -/
  multBits : ℕ → ℕ
  /-- Width of the transmitted global subtotals. -/
  tally : ℕ → ℕ
  /-- Word width of the physical RAM. -/
  word : ℕ → ℕ
  /-- Interior wire names of a single team of processors. -/
  Edge : ℕ → Type
  [finiteEdge : ∀ n, Fintype (Edge n)]
  resources : ∃ W e : ℕ, ∀ᶠ n : ℕ in atTop,
    teamsPred n + 1 + multBits n + tally n + word n ≤ W*(adviceScale σ ρ n+1)^e

attribute [instance] StretchSchedule.finiteEdge

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι]

/-- Native target for a fixed shortening and cube. For every sufficiently
large length, the actual packed layout, local programs and transmitted data
must produce a finite signed-path certificate. The chart and entry circuit
have a shared, length-independent polynomial resource estimate. -/
def NativeColumns (q : ℕ) (G : PaidIdentity K D m) (aux : ι → K) (S : StretchSchedule) : Prop :=
  ∀ f : ℕ → ℕ, PolynomiallyBounded f → ∀ A C : ℕ, ∀ᶠ n : ℕ in atTop,
    let r := stretch S.ρ n
    let s := stretch S.σ n
    let T := f (adviceScale S.σ S.ρ n)
    ∀ k, k+1 = n → ∀ (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
      (R : CommonField G aux q k s ord) (chart : AdvisedBranch R),
      letI : Fact R.p.Prime := ⟨R.prime⟩
      letI : Algebra (ZMod R.p) chart.E := ZMod.algebra _ _
      ReaderInputs chart (S.teamsPred n+1) r (S.multBits n) T →
      S.tally n ≤ T → S.word n ≤ T →
      ∀ reader : ChosenReader chart (S.teamsPred n+1) r (S.multBits n) (S.tally n) (S.word n) (T+6),
        reader.charge ≤ A*(T+1)^C →
        ∃ t inner, Nonempty (reader.Realization t (S.link n) inner (S.Edge n))

/-- Once the native construction supplies its physical column, the same
`σ` works for all fields of the given characteristic. -/
theorem stretch_of_native_columns (q : ℕ) [CharP K q] (G : PaidIdentity K D m)
    (aux : ι → K) (S : StretchSchedule) (run : NativeColumns q G aux S)
    (F : Type*) [Field F] [CharP F q] :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ)^((n : ℝ)^S.σ) ≤ borderSize n (map (Int.castRingHom F) (Pstar n)) := by
  obtain ⟨W,e,hphysical⟩ := S.resources
  let physical n := S.teamsPred n+1+S.multBits n+S.tally n+S.word n
  obtain ⟨f,hf,_,supply⟩ := eventually_reader_inputs q G aux S.positive S.separated physical hphysical
  obtain ⟨A,C,chooseReader⟩ := exists_chosen_reader G aux
  apply stretch_bound_of_exclusion
  filter_upwards [supply,run f hf A C,eventually_ge_atTop 1] with n provide execute hn
  intro small
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)) := (Fintype.equivFin _).trans
    (finCongr (by simp [Nat.mul_comm]))
  let n := k+1
  let r := stretch S.ρ n
  let s := stretch S.σ n
  let T := f (adviceScale S.σ S.ρ n)
  obtain ⟨room,charts⟩ := provide
  have ht : S.tally n ≤ T := (show S.tally n ≤ physical n by dsimp [physical]; omega).trans room
  have hw : S.word n ≤ T := (show S.word n ≤ physical n by dsimp [physical]; omega).trans room
  obtain ⟨R,chart,inputs⟩ := charts k rfl s le_rfl (S.teamsPred n+1) (by dsimp [physical,n]; omega)
    (S.multBits n) (by dsimp [physical,n]; omega) ord F small
  let : Fact R.p.Prime := ⟨R.prime⟩
  let : Algebra (ZMod R.p) chart.E := ZMod.algebra _ _
  obtain ⟨reader,cost,excluded⟩ := chooseReader chart (S.teamsPred n) r (S.multBits n)
    (S.tally n) (S.word n) T (S.link n) (S.Edge n) inputs ht hw
  obtain ⟨t,inner,col⟩ := execute k rfl ord R chart inputs ht hw reader cost
  exact (excluded t inner).false col.some

end Diagonal

end BorderVNP
end Computability
end OAI
