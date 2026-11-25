import OAI.Computability.NearSquareRoot.PhysicalWalshParamLiterals
import OAI.Computability.NearSquareRoot.PhysicalWalshParamHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingSetup

/-! # A named effective padding command

The shared interpreter reads the radix and fanout alongside the two
width counters. Specialization emits those two constants before entering
the interpreter. Every template uses the same finite register set.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.PaddingCommand

open IntegerMultiplication Code Space Staff Strip Carry CommonRegisters GeneratorSyntax EffectiveBoundedTask
open PaddingHeader (extra)

private structure Descriptor where
  A : ℕ
  W : ℕ
  k : ℕ
  s : ℕ
  radix : 1 < A

private def scale (v : Descriptor) := v.A + v.W + v.k + v.s
private def params (v : Descriptor) := (tally v.A,tally v.W)
private def widths (v : Descriptor) := (tally v.k,tally v.s)
private def regime : Regime Descriptor where
  scale := scale
  header v := send (params v,widths v)
  gauge := by
    refine ⟨1,7,fun v => ?_⟩
    change size (params v,widths v) ≤ 7*(scale v+1)^1
    simp only [params,widths,scale,size_prod,size_tally,tally_length,pow_one]
    omega

private def num (v : Descriptor) := 2^v.k
private def surplus (v : Descriptor) := extra v.A v.W v.k v.s

private theorem count_task : ∃ d C : ℕ, let t v := C*(scale v+1)^d+surplus v+num v
    BoundedTask t t regime.header (fun v => send (tally (surplus v),tally (num v))) := by
  have input : regime.Has (fun v => (params v,widths v)) := Regime.self
  have A : Realizes regime Descriptor.A := input.ez (Easy.fst.compose Easy.fst)
  have W : Realizes regime Descriptor.W := input.ez (Easy.fst.compose Easy.snd)
  have k : Realizes regime Descriptor.k := input.ez (Easy.snd.compose Easy.fst)
  have s : Realizes regime Descriptor.s := input.ez (Easy.snd.compose Easy.snd)
  have m : Mint regime (fun v => (tally (surplus v),tally (num v))) :=
    (Mint.tally (ParamHeader.extra_figure A Descriptor.radix W k s)).pair (Mint.tally (PaddingHeader.total_figure k))
  obtain ⟨d,C,h⟩ := m.bounded
  refine ⟨d,C,h.bound 4 4 ?_ ?_⟩ <;> intro v <;>
    simp only [regime,size_prod,size_tally,tally_length] <;> omega

private structure Input extends Descriptor where
  w : ℕ
  xs : List (Dusk.Grain w)
  len : xs.length = 2^k
  sel : s ≤ k
  occ : extra A W k s ≤ 2^k

private def marks (v : Input) := v.xs.map Dusk.mark
private def start (v : Input) := (widths v.toDescriptor,marks v)
private def stop (v : Input) := (tally (num v.toDescriptor),Padding.padded (surplus v.toDescriptor) v.xs)
private def volume (v : Input) := num v.toDescriptor*(v.w+1)
private def budget (d C : ℕ) (v : Input) :=
  C*(scale v.toDescriptor+1)^d+size (params v.toDescriptor,start v)+volume v

private def associate (v : (Tally × Tally) × (Tally × Tally) × List Dusk.Pair) :=
  ((v.1,v.2.1),v.2.2)

private theorem easy_associate : Easy associate := by unfold associate; fun_prop

private theorem core_exists : ∃ c : Cmd, ∃ d C : ℕ, EffectiveBoundedTask.Runs c (budget d C) (budget d C)
    (fun v => send (params v.toDescriptor,start v)) (fun v => send (stop v)) := by
  obtain ⟨d,C,count⟩ := count_task
  have associateTask := BoundedTask.of_time (easy_associate.on (fun v : Input => (params v.toDescriptor,start v)))
  have header := (count.on Input.toDescriptor).left (fun v => send (marks v))
  have append := Padding.appendZeros Input.w (fun v => surplus v.toDescriptor) Input.xs (fun v e => by
    have h := v.len; rw [e,List.length_nil] at h; exact (Nat.two_pow_pos v.k).ne h)
  simp only [Input.len] at append
  have chain := (associateTask.compose header).compose append
  have joint : BoundedTask (budget d C) (budget d C)
      (fun v => send (params v.toDescriptor,start v)) (fun v => send (stop v)) := by
    apply chain.bound 10 10 <;> intro v
    all_goals
      let comp := C*(scale v.toDescriptor+1)^d
      let N := num v.toDescriptor
      let E := surplus v.toDescriptor
      let z := size (params v.toDescriptor,start v)
      have occ : E ≤ N := v.occ
      have pos : 0 < N := Nat.two_pow_pos v.k
      have len : N ≤ volume v := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have res : (N+E+1)*(v.w+1) ≤ 3*volume v :=
        (Nat.mul_le_mul_right (v.w+1) (show N+E+1 ≤ 3*N by omega)).trans_eq (Nat.mul_assoc ..)
      have saved : size (marks v) ≤ z := by dsimp only [z,start]; simp only [size_prod]; omega
    · change z+(comp+E+N)+(N+E+1)*(v.w+1)+1 ≤ 10*(comp+z+volume v+1)
      omega
    · change max (max (z+z) (comp+E+N+size (marks v))) ((N+E+1)*(v.w+1))+1 ≤ 10*(comp+z+volume v+1)
      omega
  obtain ⟨c,H⟩ := joint
  exact ⟨c,d,C,H⟩

private noncomputable def core := core_exists.choose

/-- Prefix the fixed interpreter with the two template literals. -/
noncomputable def padCmd (A W : ℕ) := ParamLiterals.command A W core

theorem effective : Effective ltr (fun aw : ℕ × ℕ => padCmd aw.1 aw.2) := ParamLiterals.effective core

theorem within : ∃ R, 0 < R ∧ ∀ A W, Within R (padCmd A W) := by
  obtain ⟨R,pos,room⟩ := ((Filter.eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually core)).exists
  exact ⟨R,pos,ParamLiterals.within pos room⟩

private theorem charge (d C A W : ℕ) : ∃ L, ∀ v : Input, v.A=A → v.W=W → budget d C v + 1 ≤ L*(volume v+1) := by
  obtain ⟨B,hB⟩ := polynomial_le_multiple_array_length d
  let M := C*(A+W+2)^d*B
  refine ⟨M+2*(A+W)+30,fun v hA hW => ?_⟩
  let N := num v.toDescriptor
  have nv : N ≤ volume v := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have positive : 0 < N := Nat.two_pow_pos v.k
  have kbound : v.k < N := Nat.lt_two_pow_self
  have sBound := v.sel
  have marksBound : size (marks v) ≤ 9*volume v := by
    change size (v.xs.map Dusk.mark) ≤ _
    rw [Padding.marks_size,v.len]
    have positive := Nat.two_pow_pos v.k
    dsimp only [volume,num]
    ring_nf
    omega
  have cost : C*(scale v.toDescriptor+1)^d ≤ M*volume v := by
    have hd : scale v.toDescriptor+1 ≤ (A+W+2)*(v.k+1) := by
      dsimp only [scale]; rw [hA,hW,Nat.mul_add,Nat.mul_one,Nat.add_mul]; omega
    calc
      C*(scale v.toDescriptor+1)^d ≤ C*((A+W+2)*(v.k+1))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)
      _ = C*(A+W+2)^d*(v.k+1)^d := by rw [mul_pow,Nat.mul_assoc]
      _ ≤ C*(A+W+2)^d*(B*N) := Nat.mul_le_mul_left _ (hB v.k)
      _ ≤ M*volume v := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ nv
  have inBound : size (params v.toDescriptor,start v) ≤ 2*(A+W)+15*volume v+8 := by
    simp only [params,start,widths,size_prod,size_tally,tally_length,hA,hW]
    omega
  change C*(scale v.toDescriptor+1)^d+size (params v.toDescriptor,start v)+volume v+1 ≤ _
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_add M, Nat.mul_add (2*(A+W))]
  omega

/-- The retained length and all padding records share the original record arena. -/
theorem runs {I : Type} (A W : ℕ) (hA : 1<A) (k s w : I → ℕ) (xs : (i : I) → List (Dusk.Grain (w i)))
    (len : ∀ i, (xs i).length = 2^k i) (sel : ∀ i, s i ≤ k i)
    (occ : ∀ i, extra A W (k i) (s i) ≤ 2^k i) :
    let V i := 2^k i*(w i+1)
    EffectiveBoundedTask.Runs (padCmd A W) V V (fun i => send ((tally (k i),tally (s i)),(xs i).map Dusk.mark))
      (fun i => send (tally (2^k i),Padding.padded (extra A W (k i) (s i)) (xs i))) := by
  intro V
  obtain ⟨d,C,h⟩ := core_exists.choose_spec
  let arg (i : I) : Input := ⟨⟨A,W,k i,s i,hA⟩,w i,xs i,len i,sel i,occ i⟩
  have entered := ParamLiterals.runs A W (core := core) (u := fun i => send (start (arg i))) (h.on arg)
    (fun i => by
      change size (start (arg i)) ≤ budget d C (arg i)
      unfold budget
      conv_rhs => rw [size_prod]
      dsimp only [Prod.fst, Prod.snd]
      omega)
  obtain ⟨L,b⟩ := charge d C A W
  exact entered.bound L L (fun i => b (arg i) rfl rfl) (fun i => b (arg i) rfl rfl)

end PhysicalWalsh.PaddingCommand

end NearSquareRoot
end Computability
end OAI
