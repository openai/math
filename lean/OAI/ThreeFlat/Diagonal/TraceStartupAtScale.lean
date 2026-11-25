import OAI.ThreeFlat.Diagonal.TraceBitPhysical
import OAI.ThreeFlat.Diagonal.TraceBitRecordAtScale
import OAI.ThreeFlat.Diagonal.TraceStartupVolume
import OAI.ThreeFlat.Diagonal.TraceFixedVolume

namespace OAI
/-! # Physical startup of the one-bit diagonal trace at its actual word and time scales -/

noncomputable section
namespace ThreeFlat.Diagonal.TraceStartupAtScale

open Computability.VPVNP BurstRAM RAM TraceStaticRow TraceVolume Filter
open scoped Fin.CommRing
set_option maxHeartbeats 1000000

abbrev cutoff := 10^26*17^14

variable {F : Type} [Field F] [Fintype F] {u e params : ℕ}
    (hu : cutoff ≤ u) (hq : Fintype.card F ≤ u) (he : e≤u) (hparams : params≤u^e)


include hu in
theorem large : 128 ≤ u := by unfold cutoff at hu; omega

include hu in
theorem volumeLarge : cm ≤ u := by unfold cutoff at hu; unfold cm; omega

theorem width (hu : cutoff≤u) : 3 ≤ (16*u^10)+1 := by
  have h := large hu
  have p := Nat.le_self_pow (by decide : 10 ≠ 0) u
  omega

theorem counter (hu : cutoff≤u) : u ≤ 2^((16*u^10)+1) :=
  (CapacityPadding.textFits_scale (large hu)).registers.trans (Nat.pow_le_pow_right (by decide) (by omega))

omit [Field F] in
theorem fieldBound (hu : cutoff≤u) (hq : Fintype.card F≤u) : Fintype.card F≤2^(16*u^10) :=
  hq.trans (CapacityPadding.textFits_scale (large hu)).registers

variable (base : ℕ) (st : Word (16*u^10))

abbrev table : BitNetwork F (Fintype.card (Port (16*u^10) u u u (depth u))) :=
  gateTable (fieldBound hu hq) (width hu) (counter hu) base (2^(depth u)) st u u (depth u)

abbrev inputs := TraceBitDescriptor.input (p := u) (r := u) (k := u) (d := (depth u)) (width hu)
  (tick_grid (volumeLarge hu) he hparams).1 (tick_grid (volumeLarge hu) he hparams).2.1 base

abbrev records := TraceBitDescriptor.records (p := u) (r := u) (k := u) (d := (depth u)) (width hu) base ((4*2^(u^10-u^4)+params)+2^(u^3)) (2^(depth u))

abbrev network : BitNetwork F ((4*2^(u^10-u^4)+params)+2^(u^3)) := TraceBitHeader.network (fieldBound hu hq) (width hu) (counter hu) base st
  (tick_grid (volumeLarge hu) he hparams).1 (tick_grid (volumeLarge hu) he hparams).2.1 u u (depth u)

/-- Number of bit-per-word cells needed for the fixed local gate and port metadata. -/
abbrev metadataLength := (16*u^10)*FixedTraceImage.count (table hu hq base st)


/-- The tape of gate and port parameter bits is polynomial in the scale,
uniformly in the base address and initial state. -/
theorem low_metadata : (16*u^10)*FixedTraceImage.count (table hu hq base st) ≤ u^152 := by
  have ub := large hu
  have hd : (depth u) ≤ 15*u^10 := by have := depth_le u; omega
  have gates : (table hu hq base st).cells ≤ u^141 := (diagonal_gateTable ub hq hd (fieldBound hu hq) (width hu) (counter hu) base (2^(depth u)) st).trans <| calc
    _ ≤ u*u^140 := Nat.mul_le_mul_right _ hu
    _ = u^141 := by ring
  have ports : (Fintype.card (Port (16*u^10) u u u (depth u))) ≤ u^141 := by
    rw [card_ports]
    exact (diagonal_ports_bound ub hd).trans <| calc
      _ ≤ u*u^30 := Nat.mul_le_mul_right _ (by unfold cutoff at hu; omega)
      _ = u^31 := by ring
      _ ≤ u^141 := Nat.pow_le_pow_right (by omega) (by decide)
  have add := Nat.add_le_add gates ports
  calc
    (16*u^10)*FixedTraceImage.count (table hu hq base st) ≤ (16*u^10)*(11*(u^141+u^141)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ add)
    _ = 352*u^151 := by ring
    _ ≤ u*u^151 := Nat.mul_le_mul_right _ (by unfold cutoff at hu; omega)
    _ = u^152 := by ring

include he hparams in
theorem work_bound :
    work (2^(depth u)) ((4*2^(u^10-u^4)+params)+2^(u^3)) (TraceUniformRow.SharedCount (16*u^10) u u u (depth u) (2^(depth u))) (table hu hq base st).internal
      (table hu hq base st).cells (Fintype.card (Port (16*u^10) u u u (depth u))) (16*u^10) (FixedTraceProgram.program (16*u^10)).binds ≤ 2^(u^10) := by
  rw [show ((4*2^(u^10-u^4)+params)+2^(u^3))=4*2^(u^10-u^4)+2^(u^3)+params by omega]
  exact fixed_tick_total hu hq he hparams base st

abbrev nativeCost := RawTickStartup.cost (w := (16*u^10)) (table hu hq base st) (inputs hu he hparams base)

theorem cost_le : RawTickStartup.cost (w := (16*u^10)) (table hu hq base st) (inputs hu he hparams base) ≤ 2^(u^10) :=
  (startup_cost (table hu hq base st) (inputs hu he hparams base)).trans (work_bound hu hq he hparams base st)

variable (code : FieldCode F (16*u^10)) (src : ℕ)
abbrev rawBase := src+(16*u^10)*FixedTraceImage.count (table hu hq base st)
abbrev packedBase := (rawBase hu hq base st src)+11*(PhysicalTraceSource.expanded (table hu hq base st) (inputs hu he hparams base)).cells
abbrev linkLayout := RawTickBuilder.contiguous (network hu hq he hparams base st) (rawBase hu hq base st src)

/-- Execution from the bit tape to the native rows and links at the generated addresses. -/
abbrev Prepared (budget : ℕ) :=
  let gates := table hu hq base st
  let sources := inputs hu he hparams base
  let image := network hu hq he hparams base st
  let raw := rawBase hu hq base st src
  let packed := packedBase hu hq he hparams base st src
  let addresses := linkLayout hu hq he hparams base st src
  let fields := records (params := params) hu base
  (RawTickStartup.procedure gates code sources src raw packed).Spec
    (fun m => ∀ i, m (src+i.val)=((FixedTraceImage.parameter gates code fields i).toNat : Word (16*u^10)))
    (fun start out =>
      let tmp := FixedTraceImage.packed gates code fields packed start
      let rawMem := fillSegment raw (11*image.cells) (PhysicalTraceSource.rowWord image code raw) tmp
      RawTickBuilder.loaded image code raw rawMem ∧
        RawTickBuilder.Result image raw addresses.lastBase addresses.prevBase addresses.dstBase rawMem out)
    budget

private theorem prepared_of_fit (hbase : base ≤ 4*2^(u^10-u^4)+params)
    (fit : RawTickStartup.Fits (w := (16*u^10)) (table hu hq base st) (inputs hu he hparams base) src (rawBase hu hq base st src) (packedBase hu hq he hparams base st src)) :
    Prepared hu hq he hparams base st code src (2^(u^10)) := by
  have small : 5120 ≤ u := by unfold cutoff at hu; omega
  have run : Prepared hu hq he hparams base st code src (nativeCost hu hq he hparams base st) :=
    TraceBitPhysical.startup (fieldBound hu hq) (width hu) (counter hu) (tick_grid (volumeLarge hu) he hparams).1 (tick_grid (volumeLarge hu) he hparams).2.1 base st code src (rawBase hu hq base st src) (packedBase hu hq he hparams base st src) fit
      (TraceAddressRecord.tick_bitRecords_fits small he hparams (width hu) hbase)
  dsimp only [Prepared]
  intro P R K M pc reg pub finish installed data cfg mem first bits
  obtain ⟨ticks, bound, result⟩ := run M pc reg pub finish installed data cfg mem first bits
  exact ⟨ticks,bound.trans (cost_le hu hq he hparams base st),result⟩

/-- The three native phases read the low metadata, emit the eleven words
per physical row, and build the trivalent predecessor links. -/
theorem startup (hbase : base ≤ 4*2^(u^10-u^4)+params) (hsrc : src ≤ 2^(u^10)) :
    Prepared hu hq he hparams base st code src (2^(u^10)) :=
  prepared_of_fit hu hq he hparams base st code src hbase
    (startup_fits (table hu hq base st) (inputs hu he hparams base) (u := u) (by have := large hu; omega) (Nat.two_pow_pos _) hsrc
      (work_bound hu hq he hparams base st))

/-- The native run also permits the metadata to follow the two outer indices
and the original input pins of the collapsed entry. -/
theorem startup_with_prefix (hbase : base ≤ 4*2^(u^10-u^4)+params) (hsrc : src ≤ 2^(2*u^10)) :
    Prepared hu hq he hparams base st code src (2^(u^10)) :=
  prepared_of_fit hu hq he hparams base st code src hbase
    (startup_fits_after_input (table hu hq base st) (inputs hu he hparams base) (u := u) (by have := large hu; omega) (Nat.two_pow_pos _) hsrc
      (work_bound hu hq he hparams base st))

theorem exponent_le (hu : cutoff ≤ u) : 152 ≤ u := by unfold cutoff at hu; omega

/-- Place the program and its private advice immediately after the four
replaceable strings. A fixed polynomial parameter area after the advice
contains the complete public metadata. All generated addresses start
beyond this input prefix. -/
theorem canonical :
    let programBase := 4*2^(u^10-u^4)
    let metadataBase := programBase+2^(u^3)
    metadataLength hu hq programBase st ≤ u^152 ∧
    Prepared (params := u^152) hu hq (exponent_le hu) le_rfl programBase st (FieldCode.ofCardLe (fieldBound hu hq))
      metadataBase (2^(u^10)) := by
  intro programBase metadataBase
  have pins := (pins_at_scale (params := u^152) (volumeLarge hu) (exponent_le hu) le_rfl).2
  have upper : 2^(u^10-2*u) ≤ 2^(u^10) := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  exact ⟨low_metadata hu hq programBase st,
    startup hu hq (exponent_le hu) (params := u^152) le_rfl programBase st (FieldCode.ofCardLe (fieldBound hu hq))
      metadataBase (by dsimp only [programBase]; omega) (by dsimp only [metadataBase,programBase]; omega)⟩

/-- At every sufficiently large scale, a single time volume suffices for
every allowed polynomial-sized public tape and every initial state. -/
theorem eventually_cost (F : Type) [Field F] [Fintype F] (e : ℕ) :
    ∀ᶠ u : ℕ in atTop, ∃ (hu : cutoff ≤ u) (hq : Fintype.card F ≤ u) (he : e ≤ u),
      ∀ (params : ℕ) (hparams : params ≤ u^e) (base : ℕ) (st : Word (16*u^10)),
        nativeCost hu hq he hparams base st ≤ 2^(u^10) := by
  filter_upwards [eventually_ge_atTop cutoff, eventually_ge_atTop (Fintype.card F),
    eventually_ge_atTop e] with u hu hq he
  exact ⟨hu,hq,he,fun _ hparams base st => cost_le hu hq he hparams base st⟩


end ThreeFlat.Diagonal.TraceStartupAtScale

end
end OAI
