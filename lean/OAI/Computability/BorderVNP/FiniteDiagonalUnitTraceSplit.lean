import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceDispatch

/-! # Partition of the field-weighted native tuples by their common physical tag -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {eval : Code}

/-- A successful ordinary or wide dispatch cannot halt early if its startup
and evaluation branch fall through. -/
theorem dispatchTable_withoutAccept {boot : Code} (hb : boot.withoutAccept = true)
    (he : eval.withoutAccept = true) : (dispatchTable boot eval).withoutAccept = true := by
  simp only [dispatchTable,Code.withoutAccept,hb,select,he,
    show unit.withoutAccept = true by decide,show readBroadcast.withoutAccept = true by decide,
    Bool.and_self]

/-- A common bit partitions the nonzero-weight original tuples, without changing the
underlying tuple or any of its private chronological events. -/
noncomputable def splitOnTag {X : Type*} (tag : Fin (R+1) → ℕ)
    (common : X → ∃ v : Bool, ∀ u, tag u = v.toNat) :
    X ≃ ({_x : X // ∀ u, tag u = 0} ⊕ {_x : X // ∀ u, tag u = 1}) := by
  classical
  refine (Equiv.sumCompl (fun _ : X => ∀ u, tag u = 0)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun x => ?_))
  constructor
  · intro h
    obtain ⟨v,hv⟩ := common x
    cases v with
    | false => exact (h hv).elim
    | true => exact hv
  · intro h h'
    have a := h 0
    have b := h' 0
    omega

/-- The actual finite-field evaluator's nonzero trace tuples split into its unit
and evaluation fibers. A mixed zero/one reference input has no successful tuple. -/
noncomputable def wideTupleTagEquiv {K : Type*} [Field K]
    (ibase hbase starbase header dst : Fin (R+1) → ℕ) (pub : Fin (R+1) → Arg → Word w)
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (bank : Fin (R+1) → Bank w)
    (snap : ∀ u, BootSnapshot G u pin ext (ibase u) (hbase u) (starbase u) (header u) (dst u)
      wideStartup (pub u) (mac u) (bank u)) (he : eval.withoutAccept = true) :
    let f (u) := G.transferFrame u (header u) (dst u)
    let tag (u) := readings (snap u).mem ((f u).addr (f u).partner 0)
    let M (u) := processorMachine (dispatchTable wideStartup eval) (pub u) (mac u) (bank u)
      (G.processorFields u pin ext (ibase u) (hbase u) (starbase u))
    ∀ (bnd : ∀ u, Bounds r (M u).inputSize) (weight : NativeTuple M bnd → K),
      let Paths := {p : NativeTuple M bnd // weight p ≠ 0}
      Paths ≃ ({_p : Paths // ∀ u, tag u = 0} ⊕ {_p : Paths // ∀ u, tag u = 1}) := by
  intro f tag M bnd weight Paths
  apply splitOnTag tag
  intro x
  exact acceptedTuple_commonTag ibase hbase starbase header dst pub mac bank snap (by decide)
    (dispatchTable_withoutAccept (by decide) he) bnd x.val

/-- The actual wide-boot tuple on the zero tag reindexes onto the one unit summand.
The startup snapshots may come from any field-machine prefix and batch size. -/
theorem wide_unitTuple {K ι : Type*} [Field K] {Q Γ : Type} {m g : ℕ}
    (ibase hbase starbase header dst : Fin (R+1) → ℕ) (pub : Fin (R+1) → Arg → Word w)
    (bank : Fin (R+1) → Bank w) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
    (ret : FieldProcessor.Returns Q Γ K m 8) (fuel : ℕ)
    (snap : ∀ u, BootSnapshot G u pin ext (ibase u) (hbase u) (starbase u) (header u) (dst u)
      wideStartup (pub u) (TeamSiteEvents.macros lib fuel) (bank u)) (he : eval.withoutAccept = true)
    (ref : Fin (R+1) → Fin d → Bool) :
    let f (u) := G.transferFrame u (header u) (dst u)
    let L (u) := G.pinLayout u (ibase u) (hbase u) (starbase u)
    let M (u) := processorMachine (dispatchTable wideStartup eval) (pub u) (TeamSiteEvents.macros lib fuel) (bank u)
      (G.processorFields u pin ext (ibase u) (hbase u) (starbase u))
    ∀ bnd : ∀ u, Bounds r (M u).inputSize,
      (∀ u, (∀ i : Fin d, (snap u).mem (starbase u+i.val) = TeamTapeInputEmit.word w (ref u i).toNat) ∧
        readings (snap u).mem ((f u).addr (f u).partner 0) = 0 ∧
        Frame (L u) (readings (pub u)) (readings (snap u).mem) ∧
        (L u).stride < 2^w ∧ (L u).count < 2^w ∧ (L u).width ≤ (L u).count ∧
        ((L u).starbase+(L u).width ≤ (f u).dst ∨ (f u).dst+(f u).header ≤ (L u).starbase) ∧
        ((L u).team = 0 → IdentityFits (L u) w) ∧
        traceCost (snap u).events + ((f u).readTicks+(2+unitBudget (f u) (L u))) ≤ (bnd u).ticks) →
      let weight (u) (p : NativePath (M u) (bnd u).ticks (bnd u).burst (bnd u).privateClock) :=
        FieldProcessor.pathProduct (dispatchTable wideStartup eval).program (pub u) lib ret fuel ⟨0,bank u⟩ p.val
      ∃ E : {p : NativeTuple M bnd // tuplePathWeight (M := M) (b := bnd) weight p ≠ 0} ≃
        {tag : Option ι // tag = none ∧ ext = (fun _ => false) ∧ pin = ref 0},
        ∀ p, (E p).val = none ∧ tuplePathWeight (M := M) (b := bnd) weight p.val = 1 := by
  intro f L M bnd h weight
  apply unitTuple_decode M bnd weight pin ref ext
  intro u
  obtain ⟨href,hzero,hframe,hs,hc,hr,ha,hi,ht⟩ := h u
  exact (snap u).unitTrace (ref u) lib ret fuel eval (dispatchTable_withoutAccept (by decide) he)
    (bnd u).ticks (bnd u).burst (bnd u).privateClock href hzero hframe hs hc hr ha hi ht

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
