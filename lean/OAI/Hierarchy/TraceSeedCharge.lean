import OAI.Hierarchy.TraceNativeScale
import OAI.ThreeFlat.Diagonal.TraceSeedPriceTerm
import OAI.ThreeFlat.RAM.TraceStrideBound

namespace OAI
/-! # The physical seed charge of the native paired-input trace

The row stride includes all trace ports and private Boolean gates. Each low-row
bucket reserves this stride, the gate table, and the repeated routed slots. -/

namespace Hierarchy.TraceDistribution

open ThreeFlat Diagonal Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type} [Field F] [Fintype F] {w pc regs words S base d fuel : ℕ}
variable (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M S base d fuel)
    (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w))
private noncomputable abbrev chargeGrid :=
  TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d

private noncomputable abbrev chargeShape :=
  TraceSourceOwner.shape (64*w) pc regs words S fuel d (chargeGrid M fit hF st).internal

/-- The word addresses for an initial bucket are polynomial in the native word
width even when the number of rows and the time cap are exponential. -/
theorem native_stride (q : Fintype.card F ≤ 64*w) (p : pc ≤ 64*w) (r : regs ≤ 64*w)
    (a : words ≤ 64*w) (depth : d ≤ 64*w) :
    (chargeShape M fit hF st).stride ≤ (256+10^26)*(64*w+1)^14 := by
  let X := 64*w+1
  have pc' : pc ≤ 1*X^1 := by simpa [X] using p.trans (Nat.le_succ _)
  have regs' : regs ≤ 1*X^1 := by simpa [X] using r.trans (Nat.le_succ _)
  have words' : words ≤ 1*X^1 := by simpa [X] using a.trans (Nat.le_succ _)
  have port : TraceAddressRecord.portRowWords (64*w) pc regs words d ≤ 128*X^4 := by
    simpa only [Nat.reduceAdd,Nat.reduceMul] using
      TraceAddressRecord.portRowWords_polynomial (c:=1) (e:=1) depth pc' regs' words'
  have internal := (TraceStaticRow.table_internal_le_cells hF fit.width fit.labels base fuel st regs words d).trans
    (native_cells M fit hF st q p r a depth)
  have mono : X^4 ≤ X^14 := Nat.pow_le_pow_right (by dsimp [X]; omega) (by decide)
  calc
    (chargeShape M fit hF st).stride ≤ 2*TraceAddressRecord.portRowWords (64*w) pc regs words d+(chargeGrid M fit hF st).internal :=
      RAM.TraceBucketAtom.stride_le_ports ..
    _ ≤ 2*(128*X^14)+10^26*X^14 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (port.trans (Nat.mul_le_mul_left _ mono))) internal
    _ = _ := by dsimp only [X]; ring

private def seedCoefficient (copies : ℕ) :=
  1+2*(256+10^26)+10^26+24*(copies+1)*10^26

def seedRate (copies : ℕ) := seedCoefficient copies*64^15

theorem seedRate_pos (copies : ℕ) : 0 < seedRate copies := by
  unfold seedRate seedCoefficient
  positivity

/-- The seed scan includes all routed trivalent slots, including the first
copy. The same bound consequently controls the initial maximum arc width. -/
theorem seed_covers_arc (low stride cells copies d : ℕ) :
    2^low*((1+(d+d))*cells*3) ≤ TraceBitHeader.seedTraceWork low stride cells copies d := by
  have paid := Nat.mul_le_mul_right ((1+(d+d))*cells) (by omega : 3≤12*(copies+1))
  have row : (1+(d+d))*cells*3 ≤ 12*(copies+1)*(1+(d+d))*cells := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using paid
  have total := Nat.mul_le_mul_left (2^low) (row.trans
    (Nat.le_add_left _ (2*stride+cells)))
  unfold TraceBitHeader.seedTraceWork
  omega

/-- The exponent is fixed independently of the chosen compression block.
The number of parallel cursor copies affects the leading coefficient alone. -/
theorem native_seed_charge (low copies : ℕ) (q : Fintype.card F ≤ 64*w) (p : pc ≤ 64*w)
    (r : regs ≤ 64*w) (a : words ≤ 64*w) (depth : d ≤ 64*w) :
    TraceBitHeader.seedTraceWork low (chargeShape M fit hF st).stride (chargeGrid M fit hF st).cells copies d ≤
      2^low*(seedRate copies*(w+1)^15) := by
  let X := 64*w+1
  have pos : 0<X := by dsimp [X]; omega
  have width : X^14 ≤ X^15 := Nat.pow_le_pow_right pos (by decide)
  have cell : (chargeGrid M fit hF st).cells ≤ 10^26*X^14 := native_cells M fit hF st q p r a depth
  have stride : (chargeShape M fit hF st).stride ≤ (256+10^26)*X^14 := native_stride M fit hF st q p r a depth
  have off : 1+(d+d) ≤ 2*X := by dsimp [X]; omega
  have routed : 12*(copies+1)*(1+(d+d))*(chargeGrid M fit hF st).cells ≤
      (24*(copies+1)*10^26)*X^15 := by
    calc
      _ ≤ (12*(copies+1)*(2*X))*(10^26*X^14) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ off) cell
      _ = _ := by ring
  have row : 1+(2*(chargeShape M fit hF st).stride+(chargeGrid M fit hF st).cells+12*(copies+1)*(1+(d+d))*(chargeGrid M fit hF st).cells)
      ≤ seedCoefficient copies*X^15 := by
    calc
      _ ≤ X^15+(2*((256+10^26)*X^15)+10^26*X^15+(24*(copies+1)*10^26)*X^15) :=
        Nat.add_le_add (Nat.pow_pos pos)
          (Nat.add_le_add (Nat.add_le_add
            (Nat.mul_le_mul_left _ (stride.trans (Nat.mul_le_mul_left _ width)))
            (cell.trans (Nat.mul_le_mul_left _ width))) routed)
      _ = _ := by unfold seedCoefficient; ring
  have padded : X^15 ≤ (64*(w+1))^15 := Nat.pow_le_pow_left (by dsimp [X]; omega) _
  unfold TraceBitHeader.seedTraceWork
  calc
    _ ≤ 2^low*(1+(2*(chargeShape M fit hF st).stride+(chargeGrid M fit hF st).cells+12*(copies+1)*(1+(d+d))*(chargeGrid M fit hF st).cells)) := by
      let body:=2*(chargeShape M fit hF st).stride+(chargeGrid M fit hF st).cells+
        12*(copies+1)*(1+(d+d))*(chargeGrid M fit hF st).cells
      change 1+2^low*body≤2^low*(1+body)
      rw [Nat.mul_add (2^low) 1 body,Nat.mul_one]
      exact Nat.add_le_add_right (Nat.two_pow_pos _) _
    _ ≤ 2^low*(seedCoefficient copies*(64*(w+1))^15) :=
      Nat.mul_le_mul_left _ (row.trans (Nat.mul_le_mul_left _ padded))
    _ = _ := by rw [mul_pow]; unfold seedRate; ac_rfl

end Hierarchy.TraceDistribution

end OAI
