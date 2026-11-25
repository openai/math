import OAI.Hierarchy.TraceDistributionScale
import OAI.ThreeFlat.Diagonal.NativeTrace
import OAI.ThreeFlat.Diagonal.TraceStaticCost
import OAI.ThreeFlat.Diagonal.TracePortCardinality

namespace OAI
/-! # A universal programmed tick chosen before its instructions

The network reads the instruction table through ordinary exposed pins. Its
clock is rounded by a factor of at most two, and the circuit, all summed bits
and all input pins fit within the original volume. -/

namespace Hierarchy.UniversalTick
open ThreeFlat Diagonal Diagonal.TraceStaticRow
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open Filter
open scoped BigOperators

def saving := 18

def depth (w c : ℕ) := w-((w^c).log2+1)
def clock (w c : ℕ) := 2^(depth w c)

theorem rounded (w c : ℕ) (hw : 0 < w) (fits : (w^c).log2+1 ≤ w) :
    clock w c * w^c ≤ 2^w ∧ 2^w ≤ 2*(clock w c * w^c) := by
  have eqn : 2^w = clock w c * 2^((w^c).log2+1) := by
    rw [clock,depth,←pow_add,Nat.sub_add_cancel fits]
  rw [eqn]
  have h := Nat.log2_self_le (Nat.pow_pos hw (n:=c)).ne'
  constructor
  · exact Nat.mul_le_mul_left _ (Nat.lt_log2_self (n:=w^c)).le
  · rw [pow_succ]
    nlinarith only [Nat.mul_le_mul_left (clock w c) h]

theorem fits_round (c : ℕ) : ∀ᶠ w : ℕ in atTop, (w^c).log2+1 ≤ w := by
  filter_upwards [TraceDistribution.polynomial_room 1 c,eventually_ge_atTop 2] with w bound large
  have pos : 0<w := by omega
  apply (Nat.log2_lt (Nat.pow_pos pos (n:=c)).ne').2
  apply lt_of_le_of_lt ((Nat.pow_le_pow_left (Nat.le_succ w) c).trans (by simpa using bound))
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)

/-- This pin table depends only on the three architectural capacities and
scalar lengths, so the same network executes all later program headers. -/
noncomputable def tick {F : Type*} [Field F] [Fintype F] {w p S : ℕ}
    (hF : Fintype.card F ≤ 2^(64*w)) (hw : 3 ≤ 64*w+1)
    (hp : p ≤ 2^(64*w+1)) (base : ℕ) (st : Word (64*w))
    (input : S ≤ 2^(64*w)) (fuel : clock w saving ≤ 2^(64*w+1)) (r k : ℕ) :
    BitNetwork F S :=
  TraceBitHeader.network hF hw hp base st input fuel r k (depth w saving)

/-- Every component of the exposed tick is charged, including all local and
global hidden variables. The cutoff is independent of the program and exponential saving. -/
theorem size {F : Type*} [Field F] [Fintype F] {w p S : ℕ}
    (hF : Fintype.card F ≤ 2^(64*w)) (hw : 3 ≤ 64*w+1)
    (hp : p ≤ 2^(64*w+1)) (base : ℕ) (st : Word (64*w))
    (input : S ≤ 2^(64*w)) (fuel : clock w saving ≤ 2^(64*w+1)) (r k : ℕ)
    (large : 4*(10^26*65^14+400*66^3+1) ≤ w)
    (q : Fintype.card F ≤ 64*w) (pc : p≤64*w) (regs : r≤64*w) (words : k≤64*w)
    (room : (w^saving).log2+1 ≤ w) (cap : S ≤ clock w saving) :
    let N := tick hF hw hp base st input fuel r k
    N.cells+N.internal+S ≤ 2^w := by
  let d := depth w saving
  let m := clock w saving
  let G := gateTable hF hw hp base m st r k d
  have pos : 1≤w := by omega
  have wd : d≤64*w := by dsimp [d,depth]; omega
  have rows : G.cells ≤ (10^26*65^14)*w^14 := by
    apply ((gateTable_size hF hw hp base m st).trans
      (cellsBound_of_le q le_rfl pc regs words wd)).trans
    calc
      10^26*(64*w+1)^14 ≤ 10^26*(65*w)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have ports : portCount (64*w) p r k d ≤ (400*66^3)*w^14 := by
    apply (portCount_of_le le_rfl pc regs words wd).trans
    calc
      400*(64*w+2)^3 ≤ 400*(66*w)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = 400*66^3*w^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right pos (by decide))
  have hidden := table_internal_le_cells hF hw hp base m st r k d
  have shared := TraceVolume.shared_le (w:=64*w) (p:=p) (r:=r) (k:=k) (d:=d) (f:=m)
    (show m≤2*2^d by change m ≤ 2*m; omega)
  let rate := 2*(10^26*65^14)+400*66^3+1
  have rateRoom : rate*w^14 ≤ w^saving := by
    calc
      _ ≤ w*w^14 := Nat.mul_le_mul_right _ (by dsimp [rate]; omega)
      _ = w^15 := by ring
      _ ≤ _ := Nat.pow_le_pow_right pos (by decide)
  change m*G.cells+(TraceUniformRow.SharedCount (64*w) p r k d m+m*G.internal)+S ≤ 2^w
  apply le_trans _ (rounded w saving pos room).1
  apply le_trans _ (Nat.mul_le_mul_left m rateRoom)
  change m*G.cells+(TraceUniformRow.SharedCount _ _ _ _ _ _+m*G.internal)+S ≤ m*(rate*w^14)
  have sh := shared.trans (Nat.mul_le_mul_left m ports)
  have cell := Nat.mul_le_mul_left m rows
  have priv := Nat.mul_le_mul_left m (hidden.trans rows)
  dsimp [rate]
  nlinarith only [sh,cell,priv,cap,Nat.mul_le_mul_left m (show 1≤w^14 from Nat.pow_pos pos)]

/-- Installing an actual bounded program as data gives its authentic weighted
RAM value for any initial input tape. -/
theorem runs {F : Type*} [Field F] [Fintype F] {w p r k S base : ℕ}
    (M : Machine (64*w) p r k)
    (room : NativeTrace.Fits M S base (depth w saving) (clock w saving))
    (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w)) (input : ℕ → Bool) :
    (tick hF room.width room.labels base st room.header room.time r k).eval
        (TraceBitHeader.advicePins base (NativeTrace.executable M) input) =
      RAM.value (RAM.FieldCode.ofCardLe hF) M (clock w saving) st
        (RAM.memoryWithAdvice base (NativeTrace.executable M)
          (initialMemory S (fun j => TraceBitHeader.binaryWord (64*w) (input j)))) :=
  NativeTrace.installed M room hF st input

/-- This instruction table has exactly the same capacities as any selected
payload machine. Its native acceptance contributes a single unit on the idle
grid row in every characteristic. -/
def accept (w p r k : ℕ) (hp : 0<p) : Machine w p r k :=
  ⟨⟨0,hp⟩,fun _ => .accept,fun _ => 0⟩

theorem runs_one {F : Type*} [Field F] [Fintype F] {w p r k S base : ℕ}
    (hp : 0<p) (room : NativeTrace.Fits (accept (64*w) p r k hp)
      S base (depth w saving) (clock w saving))
    (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w)) (pin : ℕ → Bool) :
    (tick hF room.width room.labels base st room.header room.time r k).eval
        (TraceBitHeader.advicePins base (NativeTrace.executable (accept (64*w) p r k hp)) pin) = 1 := by
  rw [runs _ room]
  have pos : 0 < clock w saving := Nat.two_pow_pos _
  obtain ⟨f,hf⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  rw [hf]
  rfl

end Hierarchy.UniversalTick

end OAI
