import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRectSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapIdle
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryInterface
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps
import OAI.Computability.NearSquareRoot.InterchangeROMAddress

/-! # Specializing the named native rectangle to a Walsh packet

The header converts each spectator width to a list of binary radix rulers.
The underlying series is the physical ordinal stream, so the record data
passes directly to the native command. Empty wings use the identity branch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileRect
open IntegerMultiplication Code Strip Strip.Dims Loom Adic PhysicalWalsh
open PhysicalWalshNode PhysicalWalshNode.SlotSwap
open GeneratorSyntax CommonRegisters Filter Space
open private value input_bound idle from OAI.Computability.NearSquareRoot.PhysicalWalshSwapIdle

noncomputable def native (x : SlotSwap.Packet) : InterchangeROMBinary.Packet where
  P := field 2 x.geometry.pre
  G := field 2 x.geometry.gap
  B := []
  n := x.geometry.wing
  w := x.width
  admissible d mem := by
    simp only [List.append_nil,List.mem_append] at mem
    obtain ⟨lo,hi⟩ : 2 ≤ d ∧ d ≤ 2 := mem.elim (ivory (by decide) d) (ivory (by decide) d)
    exact ⟨lo,hi.trans Net.Shuttle.base_large.le⟩
  bits a := x.bits (x.geometry.grid.index a).val
  exactWidth _ := x.exactWidth _

private abbrev GeometryWire := Tally × Tally × Tally
private abbrev Wire := GeometryWire × List (List Bool)

private def nativeHeader (h : GeometryWire) : InterchangeROMBinary.Header :=
  (h.2.2,h.1.map (fun _ => tally 2),h.2.1.map (fun _ => tally 2),[])

private def prep (z : Wire) := (nativeHeader z.1,z.2)
private def flag (z : Wire) := (z.1.2.2.isEmpty,z)

private theorem prepEasy : Easy prep := by
  have digits : Easy (List.map (fun _ : Unit => tally 2)) := (Easy.const _).mapping
  have e : Easy nativeHeader := (Easy.snd.compose Easy.snd).pair
    ((Easy.fst.compose digits).pair (((Easy.snd.compose Easy.fst).compose digits).pair (Easy.const _)))
  exact (Easy.fst.compose e).pair Easy.snd

private theorem flagEasy : Easy flag :=
  ((Easy.fst.compose (Easy.snd.compose Easy.snd)).compose (Carry.vacant Unit)).pair Easy.identity

private theorem native_header (x : SlotSwap.Packet) :
    send (nativeHeader x.geometry.header) = (native x).description := by
  simp only [nativeHeader, Geometry.header, InterchangeROMAddress.shape_field]
  rfl

private theorem input_native (x : SlotSwap.Packet) : send (prep (value x)) = (native x).input := by
  change Tree.fork (send (nativeHeader x.geometry.header)) _ = Tree.fork (native x).description _
  rw [native_header]
  apply congrArg (Tree.fork _)
  rw [show (native x).bits = fun a => x.bits (x.geometry.grid.index a).val from rfl]
  change send ((List.range x.geometry.grid.count).map x.bits) = stripe x.geometry.grid (fun a => send (x.bits (x.geometry.grid.index a).val))
  rw [stripe_eq',SwapOrdinal.tab_range]

private theorem output_native (x : SlotSwap.Packet) : (native x).output = x.output := by
  change stripe (stock 2 _ _ [] _) (fun a => send (x.bits (x.geometry.grid.index (swapper _ _ _ a)).val)) = _
  rw [stripe_eq']
  exact congrArg send (SwapOrdinal.tab_swapped _ _ [] x.geometry.wing x.bits)

private theorem size_expand (l : Tally) : size (l.map (fun _ => tally 2)) = 6*l.length+1 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,size_cons,size_tally,tally_length,List.length_cons,ih];omega

private theorem header_size (x : SlotSwap.Packet) :
    (native x).description.count+1 ≤ 4*(size x.geometry.header+1) := by
  rw [← native_header];change size (nativeHeader x.geometry.header)+1 ≤ _
  simp only [nativeHeader,Geometry.header,size_prod,size_expand,size_tally,tally_length,size_nil];omega

private theorem mass_bound (D M : ℕ) (x : SlotSwap.Packet) (fit : (size x.geometry.header+1)^D ≤ M*x.width) :
    (native x).mass D ≤ (1+4^D*M)*x.volume := by
  have pow := Nat.pow_le_pow_left (header_size x) D
  rw [Nat.mul_pow] at pow
  have bound := pow.trans (Nat.mul_le_mul_left (4^D) fit)
  change x.geometry.grid.count*(x.width+((native x).description.count+1)^D) ≤ _
  apply (Nat.mul_le_mul_left _ (Nat.add_le_add_left bound x.width)).trans_eq
  unfold SlotSwap.Packet.volume;ring

noncomputable def command (c : Cmd) : Cmd :=
  flagEasy.choose.join (decodeBit (prepEasy.choose.join c) (Easy.snd (X:=GeometryWire) (Y:=List (List Bool))).choose)

/-- Literal command substitution leaves every layout and branch scanner fixed. -/
theorem effective {J : Type} [Primcodable J] {c : J → Cmd} (h : Effective ltr c) :
    Effective ltr (fun j => command (c j)) := by
  apply (effective_const ltr _).join
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  apply KernelEffectiveFamily.effective_splitRoot _ _ (effective_const _ _)
  intro b;cases b
  · exact (effective_const ltr _).join h
  · exact effective_const ltr _

theorem registers : ∀ᶠ R in atTop, ∀ c : Cmd, Within R c → Within R (command c) := by
  filter_upwards [eventually_gt_atTop 0,RegisterSelect.within_eventually flagEasy.choose,
    RegisterSelect.within_eventually prepEasy.choose,RegisterSelect.within_eventually (Easy.snd (X:=GeometryWire) (Y:=List (List Bool))).choose] with R pos flagOK prepOK idOK
  intro c valid
  exact ⟨flagOK,RegisterWitness.splitRoot_within.mpr ⟨pos,trivial,trivial,
    RegisterWitness.splitRoot_within.mpr ⟨pos,⟨prepOK,valid⟩,idOK,trivial⟩⟩⟩

private theorem issue {I : Type} (x : I → SlotSwap.Packet) (wide : ∀ i, 0 < (x i).width)
    (T S : I → ℕ) (cost : ∀ i, (x i).volume ≤ T i) (space : ∀ i, (x i).volume ≤ S i)
    {c : Cmd} (body : let I' := {i : I // (tally (x i).geometry.wing).isEmpty=false}
      EffectiveBoundedTask.Runs c (fun i : I' => T i) (fun i => S i)
        (fun i => (native (x i)).input) (fun i => (x i).output)) :
    ClosedRuns (command c) T S (SlotSwap.Packet.input ∘ x) (SlotSwap.Packet.output ∘ x) := by
  let tag i := (tally (x i).geometry.wing).isEmpty
  have scan {A : Type} [Codec A] {f : Wire → A} (ez : Easy f) {J : Type} (v : J → I) :
      EffectiveBoundedTask.Runs ez.choose (fun j => T (v j)) (fun j => S (v j))
        (fun j => send (value (x (v j)))) (fun j => send (f (value (x (v j))))) := by
    apply (AgendaOps.easy ez (fun j => value (x (v j)))).bound 18 18 <;> intro j
    all_goals have h := input_bound _ (wide (v j)); have t := cost (v j); have s := space (v j)
    all_goals omega
  have pre := scan prepEasy (Subtype.val : {i : I // tag i=false} → I)
  have nonempty := pre.sequence (AgendaOps.conform body (fun _ => rfl) (fun _ => rfl)
    (fun i => (input_native (x i)).symm) (fun _ => rfl))
  have empty := scan (Easy.snd (X:=GeometryWire) (Y:=List (List Bool))) (Subtype.val : {i : I // tag i=true} → I)
  have equal (i : {i : I // tag i=true}) : (x i).geometry.wing=0 := by
    simpa only [tag,List.isEmpty_iff_length_eq_zero,tally_length] using i.property
  have proj := AgendaOps.conform empty (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun i=>(idle _ (equal i)).symm)
  have test := EffectiveBoundedTask.Runs.control (t:=T) (s:=S) (u:=SlotSwap.Packet.input ∘ x) (v:=SlotSwap.Packet.output ∘ x)
    tag nonempty proj
  have clean := test.bound (t':=T) (s':=S) 1 10 (fun _ => by simp) (fun i => by
    have h := input_bound _ (wide i); have b := space i
    change S i+size (value (x i))+1 ≤ 10*(S i+1);omega)
  exact (scan flagEasy id).sequence clean

private theorem volume_time {ρ : ℝ} (rate : 0 ≤ ρ) (x : SlotSwap.Packet) :
    x.volume ≤ InterchangeROMBinary.time ρ x.volume x.geometry.wing := by
  apply (Nat.cast_le (α:=ℝ)).mp
  exact (le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow
    (by exact_mod_cast Nat.le_add_left 1 x.geometry.wing) rate)).trans (Nat.le_ceil _)

/-- Compact Walsh geometry uses the very same reserve degree as the native
binary command. The degree-dependent radix-header expansion is constant for
a fixed emitted program. -/
theorem rectRunsScaled {c : Cmd} {ρ : ℝ} {D : ℕ} (rate : 0 ≤ ρ) (nativeRun : InterchangeROMBinary.RectPhysical c ρ D) :
    ∀ {I : Type} (data : I → SlotSwap.Packet) (M : ℕ), (∀ i, 0 < (data i).width) →
      (∀ i, (data i).geometry.wing=0 ∨ (size (data i).geometry.header+1)^D ≤ M*(data i).width) →
      ClosedRuns (command c) (fun i => InterchangeROMBinary.time ρ (data i).volume (data i).geometry.wing)
        (SlotSwap.Packet.volume ∘ data) (SlotSwap.Packet.input ∘ data) (SlotSwap.Packet.output ∘ data) := by
  intro I data M wid fit
  let T i := InterchangeROMBinary.time ρ (data i).volume (data i).geometry.wing
  let S i := (data i).volume
  apply issue data wid T S (fun i => volume_time rate _) (fun _=>le_rfl)
  let Q := {i : I // (tally (data i).geometry.wing).isEmpty=false}
  let K : ℕ := 1+4^D*M
  have bound (q : Q) : (native (data q)).mass D ≤ K*S q := by
    apply mass_bound
    apply (fit q).resolve_left
    intro h
    have b := q.property;rw [h] at b; contradiction
  have widen (q : Q) : InterchangeROMBinary.time ρ ((native (data q)).mass D) (data q).geometry.wing ≤ K*T q := by
    apply Nat.ceil_le.mpr
    let r : ℝ := (((data q).geometry.wing+1 : ℕ):ℝ)^ρ
    have hm : (((native (data q)).mass D : ℕ):ℝ) ≤ (K:ℝ)*(S q:ℝ) := by exact_mod_cast bound q
    have hr := Nat.le_ceil ((S q:ℝ)*r)
    have pr : 0≤r := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc
      _ ≤ (K*(S q:ℝ))*r := mul_le_mul_of_nonneg_right hm pr
      _ = (K:ℝ)*((S q:ℝ)*r) := by ring
      _ ≤ K*(T q:ℝ) := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
      _ = _ := (Nat.cast_mul ..).symm
  have run : EffectiveBoundedTask.Runs c _ _ _ _ := nativeRun.on (fun q : Q => native (data q))
  exact AgendaOps.conform (run.bound (t':=fun q:Q=>T q) (s':=fun q:Q=>S q) (K+1) (K+1)
    (fun q => by have h := widen q; change InterchangeROMBinary.time ρ ((native (data q)).mass D) (data q).geometry.wing+1 ≤ (K+1)*(T q+1);rw [Nat.succ_mul,Nat.mul_succ];omega)
    (fun q => by have h := bound q;change (native (data q)).mass D+1 ≤ (K+1)*(S q+1);rw [Nat.succ_mul,Nat.mul_succ];omega))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun q => output_native _)

theorem rectRuns {c : Cmd} {ρ : ℝ} {D : ℕ} (rate : 0 ≤ ρ) (nativeRun : InterchangeROMBinary.RectPhysical c ρ D) :
    RectRuns (command c) ρ D := by
  intro I data wide fit
  exact rectRunsScaled rate nativeRun data 1 wide (by simpa only [one_mul] using fit)

/-- The same file still returns the right permutation for arbitrary positive
payload widths, before the setup cost is absorbed into their bit volume. -/
theorem total {c : Cmd} {I : Type} (data : I → SlotSwap.Packet) (wide : ∀ i, 0 < (data i).width)
    {T S : InterchangeROMBinary.Packet → ℕ}
    (core : ClosedRuns c T S InterchangeROMBinary.Packet.input InterchangeROMBinary.Packet.output) :
    ClosedRuns (command c) (fun i => max (data i).volume (T (native (data i))))
      (fun i => max (data i).volume (S (native (data i)))) (SlotSwap.Packet.input ∘ data) (SlotSwap.Packet.output ∘ data) := by
  apply issue data wide _ _ (fun _ => le_max_left ..) (fun _ => le_max_left ..)
  let Q := {i : I // (tally (data i).geometry.wing).isEmpty=false}
  have r : EffectiveBoundedTask.Runs c _ _ _ _ := core.on (fun q : Q => native (data q))
  exact AgendaOps.conform (r.mono (fun _ => le_max_right ..) (fun _ => le_max_right ..))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun q => output_native _)

end PhysicalWalshCompileRect

end NearSquareRoot
end Computability
end OAI
