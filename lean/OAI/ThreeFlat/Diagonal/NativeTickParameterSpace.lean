import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace
import OAI.ThreeFlat.Diagonal.TraceBitParameterBudget
import OAI.ThreeFlat.RAM.TraceMountedParameters

namespace OAI
/-! # Capacity for the tick parameters before the H trace is constructed -/

namespace ThreeFlat.Diagonal.NavigationPass
open PhysicalStage RAM RAM.HistoryStageBody.Physical TraceStaticRow Computability.VPVNP.BurstRAM

variable {F : Type} [Field F] [Fintype F] (B : Block F) (p : Parameters)
variable {u d : ℕ}

/-- The grid library and the chronological directory, including every node header,
fit for every residual lane count. Only the fixed compressor contributes to the age threshold. -/
theorem navigation_parameter_bits (rem : ℕ) (age : 384000≤u)
    (tables : staticSize B+gridSize B≤u) (level : B.levels+1≤u) :
    (16*u^10)*((Parameters.gridWords B u)++p.staticWords B (u^8) rem (16*u^10)).length≤u^57 := by
  let W := 16*u^10
  have pos : 0<u := by omega
  have mono {a b : ℕ} (m : a≤b) : u^a≤u^b := Nat.pow_le_pow_right pos m
  have one (n : ℕ) : 1≤u^n := Nat.pow_pos pos
  have up (n : ℕ) : u*u^n=u^(n+1) := by rw [pow_succ,Nat.mul_comm]
  have word : W+1≤u^11 := by
    have h := Nat.mul_le_mul_right (u^10) (show 17≤u by omega)
    rw [up] at h
    change 17*u^10 ≤ u^11 at h
    dsimp only [W]
    have := one 10
    omega
  have fourth : 384000*(W+1)^4≤u^45 := calc
    _ ≤ u*(u^11)^4 := Nat.mul_le_mul age (Nat.pow_le_pow_left word _)
    _ = _ := by ring
  have twice : 2*(W+1)≤u^45 := calc
    _ ≤ u*u^11 := Nat.mul_le_mul (by omega) word
    _ = u^12 := up 11
    _ ≤ _ := mono (by decide)
  have cell : u≤u^45 := Nat.le_self_pow (by decide) _
  have library : libraryWords B W≤3*u^45 := by
    rw [libraryWords_eq]
    omega
  have stages : (B.repeat (u^8)).length≤u^9 := by
    rw [program_length,B.repeat_effects_length]
    exact (Nat.mul_le_mul_right _ level).trans_eq (up 8)
  have sts : (p.staticWords B (u^8) rem W).length≤u^45 := by
    rw [Parameters.staticWords_length]
    calc
      _ ≤ 254*u^9 := by have := one 9; omega
      _ ≤ u*u^9 := Nat.mul_le_mul_right _ (by omega)
      _ = u^10 := up 9
      _ ≤ _ := mono (by decide)
  rw [List.length_append,Parameters.gridWords_length]
  change W*(libraryWords B W+(p.staticWords B (u^8) rem W).length)≤u^57
  have total : libraryWords B W+(p.staticWords B (u^8) rem W).length ≤ 4*u^45 :=
    (Nat.add_le_add library sts).trans_eq (by omega)
  calc
    _ ≤ u^11*(4*u^45) := Nat.mul_le_mul ((Nat.le_succ W).trans word) total
    _ = 4*u^56 := by ring
    _ ≤ u*u^56 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := up 56

/-- With offset zero the real navigation library is followed immediately by the local
trace table in the physical tick parameter vector. Its length is chosen before any
executable, fold length, time, trace depth, or table entry is supplied. -/
theorem parameter_capacity (rem base fuel : ℕ) (st : Word (16*u^10))
    (large : bitParameterConstant≤u) (tables : staticSize B+gridSize B≤u) (level : B.levels+1≤u)
    (hq : Fintype.card F≤u) (hd : d≤15*u^10) (hF : Fintype.card F≤2^(16*u^10))
    (hw : 3≤16*u^10+1) (hp : u≤2^(16*u^10+1)) :
    let W := 16*u^10
    let len := ((Parameters.gridWords B u)++p.staticWords B (u^8) rem W).length
    let G := gateTable hF hw hp base fuel st u u d
    W*len+W*FixedTraceImage.count G≤u^152 ∧ u^3+u^6+u^152≤u^153 := by
  intro W len G
  have c : 384000≤bitParameterConstant := by norm_num [bitParameterConstant]
  have age := c.trans large
  have nav := navigation_parameter_bits B p rem age tables level
  have tab := diagonal_bitParameterLength_le_pow (by omega) hq hd hF hw hp base fuel st large
  change W*len≤u^57 at nav
  change W*FixedTraceImage.count G≤u^151 at tab
  have mono {a b : ℕ} (m : a≤b) : u^a≤u^b := Nat.pow_le_pow_right (by omega) m
  constructor
  · have a := mono (by decide : 57≤151)
    have b := Nat.mul_le_mul_right (u^151) (show 2≤u by omega)
    rw [pow_succ u 151]
    rw [Nat.mul_comm u] at b
    omega
  · have a := mono (by decide : 3≤152)
    have b := mono (by decide : 6≤152)
    have c := Nat.mul_le_mul_right (u^152) (show 3≤u by omega)
    rw [pow_succ u 152]
    rw [Nat.mul_comm u] at c
    omega


end ThreeFlat.Diagonal.NavigationPass

end OAI
