import OAI.Computability.BorderVNP.DiagonalNativeUnitRate
import OAI.Computability.BorderVNP.TeamSiteEvents

/-! # The assembled, clocked processor tables give the complete unit column

A local unit contribution is selected by the true bit at the reference address of
the original processor input. The complete machine in each term uses the very same
table, public parameters, register state and private routines as its physical literal.
The product and sum share a single exterior assignment for every pair of endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open TeamScales Filter Diagonal.Layout
open scoped BigOperators Classical

/-- Public scratch intervals and the number of saved broadcast bits. -/
structure UnitAddresses where
  /-- Common prefix length. -/
  header : ℕ
  /-- Destination of the common broadcast. -/
  dst : ℕ
  /-- Substituted-column base. -/
  ibase : ℕ
  /-- Live-column base. -/
  hbase : ℕ
  /-- Reference-column base in the gathered advice. -/
  starbase : ℕ
  /-- Processor-literal gather parameters. -/
  advice : AdviceLayout

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- The advertised operands and disjoint, word-sized physical ranges at a single
team. These conditions do not depend on the exterior assignment or the chosen live pin. -/
structure UnitAddresses.Fitted (a : UnitAddresses) (G : Wiring R r t d link inner n Edge) (u : Fin (R+1))
    (p : ReferencePacket w d) (pub : Arg → Word w) (offset : ℕ) : Prop where
  /-- Broadcast, pin and packet fields in the pinned public arguments. -/
  operands : PacketFrame (G.pinLayout u a.ibase a.hbase a.starbase) (G.transferFrame u a.header a.dst)
    a.advice p.entry.length w (fun _ => 0) (operand pub)
  /-- Physical inputs precede the broadcast frame. -/
  physical : (G.transferFrame u a.header a.dst).Fits w (pub 0).val
  /-- The designated literal position and advice output fit the physical allocation. -/
  gather : a.advice.Fits (G.transferFrame u a.header a.dst) w (pub 0).val
  /-- The 81-word suffix can be decoded into the extended frame. -/
  extended : ExtendedFrame.Fits w (pub 0).val a.advice.dst p.entry.length
  /-- The gather reads the actual prescribed advice position in each literal. -/
  literalOffset : a.advice.offset = offset
  /-- The full encoded packet fits the literal advice-bit gather. -/
  packet : p.bits.length ≤ a.advice.count
  /-- H* begins immediately after the packed words. -/
  reference : a.starbase = a.advice.dst+p.offset
  /-- Broadcast scratch and the reference slice are disjoint. -/
  apart : a.starbase+d ≤ a.dst ∨ a.dst+a.header ≤ a.starbase

/-- The live secondary positions, literal divisions and reference reads all fit
at the real word width. The ordinary packet and gather allocation implies these bounds. -/
theorem UnitAddresses.Fitted.pinRoom {a : UnitAddresses} {G : Wiring R r t d link inner n Edge}
    {u : Fin (R+1)} {p : ReferencePacket w d} {pub : Arg → Word w} {off : ℕ}
    (h : a.Fitted G u p pub off) :
    let L := G.pinLayout u a.ibase a.hbase a.starbase
    L.stride < 2^w ∧ L.count < 2^w ∧ L.width ≤ L.count ∧ IdentityFits L w := by
  intro L
  let f := G.transferFrame u a.header a.dst
  have physical : f.Fits w (pub 0).val := h.physical
  have stride : L.stride = f.stride := by
    simp [L,f,Wiring.pinLayout,Wiring.transferFrame,Layout.stride,Layout.offset,BroadcastFrame.stride]
    omega
  have procs : 0 < L.processors := physical.procs
  have total : L.processors*L.stride ≤ (pub 0).val := stride ▸ physical.input
  have hs := ((Nat.le_mul_of_pos_left L.stride procs).trans total).trans_lt (pub 0).isLt
  have lit : 0 < L.literal := (Nat.zero_le _).trans_lt h.gather.literal
  have hc : L.count ≤ L.processors*L.stride :=
    Nat.mul_le_mul_left _ (show L.literal ≤ L.stride by simp [Layout.stride])
  have hd : L.width ≤ L.count := (p.dimensions_le h.packet).2.trans
    (h.gather.count.trans (Nat.le_mul_of_pos_right _ lit))
  have hp := h.packet
  rw [ReferencePacket.bits_length] at hp
  have endStar : a.starbase+d ≤ 2^w := by
    have out := h.gather.dest
    rw [h.reference,Nat.add_assoc]
    exact (Nat.add_le_add_left hp a.advice.dst).trans out
  exact ⟨hs,(hc.trans total).trans_lt (pub 0).isLt,hd,lit,fun i hi =>
    ((livePinAddress_lt L (hi.trans_le hd)).trans_le total).trans (pub 0).isLt,
    fun i hi => (Nat.add_lt_add_left hi a.starbase).trans_le endStar⟩

/-- A successful logical unit assignment gives the zero tag at the reference address
in the original, unbooted physical processor memory. -/
theorem UnitAddresses.tag_zero_of_local {a : UnitAddresses} (G : Wiring R r t d link inner n Edge)
    (u : Fin (R+1)) (pin advised : Fin d → Bool) (ext : Exterior R r link → Bool)
    {base : ℕ} (fit : (G.transferFrame u a.header a.dst).Fits w base) (ok : LocalUnit u pin advised ext) :
    let f := G.transferFrame u a.header a.dst
    let F := G.processorFields u pin ext a.ibase a.hbase a.starbase
    readings (processorMemory F w) (f.addr f.partner 0) = 0 := by
  intro f F
  have hw : 0 < w := by by_contra! hz; obtain rfl := Nat.eq_zero_of_le_zero hz; have := fit.frame; have := fit.out; simp at *; omega
  have partner := f.partner_spec fit.three
  let v : Fin (R+1) := ⟨f.partner,partner.2⟩
  have ne : u ≠ v := fun he => partner.1 (congrArg Fin.val he.symm)
  let pos : Fin (r*link) := ⟨0,Nat.mul_pos fit.procs fit.width⟩
  have read := G.read_exterior_val hw u v ne pin ext a.ibase a.hbase a.starbase
    (processorMemory F w) (F.containsInput_initial w) pos
  exact read.trans (by rw [ok.1 v ne _ _]; rfl)

variable {m g a : ℕ} {Q Γ : Type} [Fintype Q]

/-- The unit-tag part of one local native value. The tag is read from the genuine
exterior input of the machine before startup. -/
noncomputable def wiredUnitValueWith (physical : UniversalMachine.Program) (eval : Code) (mac : TeamOpcode.Macros w 8)
    (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (link n e : ℕ) (fit : fitsWith physical 64 32 r w a R link n e)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1)) (args : UnitAddresses) : ℤ :=
  let G := wiringWith physical (withStartup eval).program (S.withPacket pack) d link n e fit
  let f := G.transferFrame u args.header args.dst
  let F := G.processorFields u pin ext args.ibase args.hbase args.starbase
  if readings (processorMemory F w) (f.addr f.partner 0) = 0 then
    nativeValue (processorMachine (withStartup eval) (S.publicWords u) mac
      (S.registers u) F) S.limit.val S.burst.val (n^25)
  else 0

/-- Unit-tag value specialized to the ordinary signed processor. -/
noncomputable def wiredUnitValue (eval : Code) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
    (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
    (link n e : ℕ) (fit : Fits (withStartup eval).program lib r w a R link n e)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1)) (args : UnitAddresses) (fuel : ℕ) : ℤ :=
  wiredUnitValueWith (TeamSite.Processor.machine (withStartup eval).program lib) eval (TeamSiteEvents.macros lib fuel)
    S pack link n e fit pin ext u args

/-- For every sufficiently large processor length, summing the full initialized native
tables on the unit branch over the one shared exterior assignment gives the basis column
at the advised H* of team zero. Both program and macro library are the ones encoded in
the processor literals; the clock and burst parameters are read from those same literals. -/
theorem eventually_wired_unit_columnWith {ξ η : ℝ} (hξ : 0 < ξ) (hξ' : ξ ≤ 1) (hη : η ≤ 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (physical : UniversalMachine.Program) (R r w a d e : ℕ) (eval : Code) (mac : TeamOpcode.Macros w 8)
      (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
      (fit : fitsWith physical 64 32 r w a R (TeamScales.link ξ (R+1) n) n e)
      (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool), eval.withoutAccept = true →
      R+1 ≤ width n η → ticks ξ r n ≤ S.limit.val →
      (let G := wiringWith physical (withStartup eval).program (S.withPacket pack) d (TeamScales.link ξ (R+1) n) n e fit
       ∀ u, (args u).Fitted G u (pack u) (S.publicWords u) (adviceOffsetWith physical r 32 64 w n)) →
      (∑ ext : Exterior R r (TeamScales.link ξ (R+1) n) → Bool, ∏ u : Fin (R+1),
        wiredUnitValueWith physical eval mac S pack _ n e fit pin ext u (args u)) =
        if pin = (pack 0).reference then 1 else 0 := by
  filter_upwards [eventually_packetUnitBudget_le_ticks hξ hξ' hη] with n budget
  intro physical R r w a d e eval mac S pack fit args pin hc hteams hlimit ready
  let P := (withStartup eval).program
  let l := TeamScales.link ξ (R+1) n
  let G := wiringWith physical P (S.withPacket pack) d l n e fit
  have localValue (ext : Exterior R r l → Bool) (u : Fin (R+1)) :
      wiredUnitValueWith physical eval mac S pack l n e fit pin ext u (args u) =
        if LocalUnit u pin (pack 0).reference ext then 1 else 0 := by
    let a := args u
    let p := pack u
    let f := G.transferFrame u a.header a.dst
    let L := G.pinLayout u a.ibase a.hbase a.starbase
    let F := G.processorFields u pin ext a.ibase a.hbase a.starbase
    have h : a.Fitted G u p (S.publicWords u) (adviceOffsetWith physical r 32 64 w n) := ready u
    have same : LocalUnit u pin p.reference ext ↔ LocalUnit u pin (pack 0).reference ext := by
      by_cases hu : u = 0
      · subst u; rfl
      · simp [LocalUnit,hu]
    by_cases zero : readings (processorMemory F w) (f.addr f.partner 0) = 0
    · unfold wiredUnitValueWith
      rw [ite_eq_left zero,←propext same]
      have team : (f.teams:ℝ) ≤ (n:ℝ)^η :=
        (Nat.cast_le.mpr hteams).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have time := budget w d ((S.publicWords u) 0).val p a.advice f L h.physical rfl team h.packet h.gather.count rfl
      obtain ⟨hs,hn,hd,ids⟩ := h.pinRoom
      exact jointPacket_unit_valueWith physical P S pack l n e fit u pin ext a.header a.dst a.ibase a.hbase a.starbase
        (S.publicWords u) mac (S.registers u) a.advice eval hc
        S.limit.val S.burst.val (n^25) h.operands h.physical h.gather h.extended h.literalOffset
        h.packet h.reference zero hs hn hd h.apart (fun _ => ids) (time.trans hlimit)
    · have fail : ¬ LocalUnit u pin (pack 0).reference ext := fun ok =>
        zero (UnitAddresses.tag_zero_of_local G u pin _ ext h.physical (same.mpr ok))
      unfold wiredUnitValueWith
      rw [ite_eq_right zero,ite_eq_right fail]
  refine Eq.trans ?_ (unit_column (R := R) (r := r) (link := l) pin (pack 0).reference)
  apply Finset.sum_congr rfl
  intro ext _
  exact Finset.prod_congr rfl (fun u _ => localValue ext u)

/-- Complete unit column for the ordinary signed processor literal. -/
theorem eventually_wired_unit_column {ξ η : ℝ} (hξ : 0 < ξ) (hξ' : ξ ≤ 1) (hη : η ≤ 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d e : ℕ) (eval : Code) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
      (S : SiteData R r 64 32 w a) (pack : Fin (R+1) → ReferencePacket w d)
      (fit : Fits (withStartup eval).program lib r w a R (TeamScales.link ξ (R+1) n) n e)
      (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool) (fuel : ℕ), eval.withoutAccept = true →
      R+1 ≤ width n η → ticks ξ r n ≤ S.limit.val →
      (let G := wiring (withStartup eval).program lib (S.withPacket pack) d (TeamScales.link ξ (R+1) n) n e fit
       ∀ u, (args u).Fitted G u (pack u) (S.publicWords u) (adviceOffset (withStartup eval).program lib r w n)) →
      (∑ ext : Exterior R r (TeamScales.link ξ (R+1) n) → Bool, ∏ u : Fin (R+1),
        wiredUnitValue eval lib S pack _ n e fit pin ext u (args u) fuel) =
        if pin = (pack 0).reference then 1 else 0 := by
  filter_upwards [eventually_wired_unit_columnWith hξ hξ' hη] with n uniform
  intro R r w a d e eval lib S pack fit args pin fuel
  exact uniform (TeamSite.Processor.machine (withStartup eval).program lib) R r w a d e eval
    (TeamSiteEvents.macros lib fuel) S pack fit args pin

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
