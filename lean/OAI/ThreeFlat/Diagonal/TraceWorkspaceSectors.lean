import OAI.ThreeFlat.Diagonal.TraceBitNetwork
import OAI.ThreeFlat.Diagonal.TraceBitParameterBudget
import OAI.ThreeFlat.Diagonal.TraceSeedVolume
import OAI.ThreeFlat.Diagonal.TickWorkspace
import OAI.ThreeFlat.Diagonal.DefectBudget

namespace OAI
/-! # Disjoint scratch sectors for virtual H addressing and its finite lookup tables -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open TraceStaticRow Computability.VPVNP.BurstRAM RAM
variable {F : Type} [Field F] [Fintype F] {u S f d xF xD : ℕ}
local notation "W" => 16*u^10

omit [Field F] in
/-- Every possible local trivalent coefficient table has a native library word. -/
theorem prototype_library (age : 8≤u) (hq : Fintype.card F≤u) :
    Fintype.card ((Fin 3→Bool)→F)≤2^W := by
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  change (Fintype.card F)^8≤_
  have square : u^2≤u^10 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (Nat.pow_le_pow_left hq 8).trans ((width_pow_le_two_pow_sq age).trans
    (Nat.pow_le_pow_right (by decide) (by omega)))

theorem virtual_sectors (hF : Fintype.card F≤2^W) (hw : 3≤W+1) (hp : u≤2^(W+1))
    (hBase xBase : ℕ) (stH stX : Word W) (hs : S≤2^W) (hf : f≤2^(W+1))
    (large : bitParameterConstant≤u) (hq : Fintype.card F≤u)
    (xh : xD≤15*u^10) (dh : d≤u^10+2*u^6) :
    let H := gateTable hF hw hp hBase f stH u u d
    let X := gateTable hF hw hp xBase xF stX u u xD
    let N := network hF hw hp hBase stH hs hf u u d
    let cap := TickWorkspace.stride u
    11*N.cells≤cap ∧ FixedTraceImage.count H≤cap ∧ FixedTraceImage.count X≤cap ∧
      2^d≤cap ∧ H.cells≤cap ∧ 1+(d+d)≤cap ∧ 2*(H.cells+2*(1+(d+d)))≤cap := by
  intro H X N cap
  have age : 20000≤u := (by decide : 20000≤bitParameterConstant).trans large
  have cost : 10^26*17^14≤u := (by decide : 10^26*17^14≤bitParameterConstant).trans large
  have up : 0<u := by omega
  have hexp : d≤2*u^10 := by
    have seven : u^7≤u^10 := Nat.pow_le_pow_right up (by decide)
    have twice := Nat.mul_le_mul_left (u^6) (show 2≤u by omega)
    rw [←pow_succ u 6] at twice
    change u^6*2≤u^7 at twice
    omega
  have upper : d≤15*u^10 := by omega
  have wpos : 0<W := by positivity
  have ht := diagonal_bitParameterLength_le_pow (by omega) hq upper hF hw hp hBase f stH large
  have xt := diagonal_bitParameterLength_le_pow (by omega) hq xh hF hw hp xBase xF stX large
  change W*FixedTraceImage.count H≤u^151 at ht
  change W*FixedTraceImage.count X≤u^151 at xt
  have hcount := (Nat.le_mul_of_pos_left (FixedTraceImage.count H) wpos).trans ht
  have xcount := (Nat.le_mul_of_pos_left (FixedTraceImage.count X) wpos).trans xt
  have powers : u^151≤u^152 := Nat.pow_le_pow_right up (by decide)
  have small : u^152≤2^(u^2) := width_pow_le_two_pow_sq (by omega)
  have square : u^2≤u^10 := Nat.pow_le_pow_right up (by decide)
  have safety : 2^(2*u^10+u^2)≤cap := by
    change 2^_≤(2^(u^10))^4
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsCap : u^152≤cap := small.trans ((Nat.pow_le_pow_right (by decide) (by omega : u^2≤2*u^10+u^2)).trans safety)
  have hgate : 11*H.cells≤FixedTraceImage.count H := by unfold FixedTraceImage.count; omega
  have row : 2^d≤2^(2*u^10) := Nat.pow_le_pow_right (by decide) hexp
  have raw : 11*N.cells≤cap := calc
    _ = 2^d*(11*H.cells) := by change 11*(2^d*H.cells)=_; ac_rfl
    _ ≤ 2^(2*u^10)*2^(u^2) := Nat.mul_le_mul row (hgate.trans (hcount.trans (powers.trans small)))
    _ ≤ cap := by rw [←pow_add]; exact safety
  have seed := seed_volume (f:=f) age cost hq upper hF hw hp hBase stH
  let n := H.cells+2*(1+(d+d))
  change 2*n*W+(2*n*(5*W+6)+6+(4+6*n))≤u^152 at seed
  have costSeed : 2*n≤u^152 := by
    have := Nat.le_mul_of_pos_right (2*n) wpos
    omega
  have seedCap := costSeed.trans hsCap
  change 2*(H.cells+2*(1+(d+d)))≤cap at seedCap
  exact ⟨raw,hcount.trans (powers.trans hsCap),xcount.trans (powers.trans hsCap),
    row.trans ((Nat.pow_le_pow_right (by decide) (by omega : 2*u^10≤2*u^10+u^2)).trans safety),
    by omega,by omega,seedCap⟩

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
