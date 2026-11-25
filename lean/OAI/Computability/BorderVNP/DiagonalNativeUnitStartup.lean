import OAI.Computability.BorderVNP.DiagonalNativeValue
import OAI.Computability.BorderVNP.DiagonalNativeUnitWiring
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame

/-! # Joining the actual startup, broadcast and unit selector

The finite table boots its public frame, gathers the processor advice, installs the
extended frame and checks the common header. On a zero tag every returning path
then runs the unit check. Even when the other branch calls private machines, each
return here has empty choice tapes, zero burst charges and positive sign.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction Pins

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The three fixed startup fragments preceding the first exterior broadcast. -/
def unitStartup : Code := .block [bootFrame,readLiteralAdvice,ExtendedFrame.install]

/-- The true startup and broadcast followed by the selected body. Instantiating
the evaluation body with the static evaluator gives its assembled program. -/
def withStartup (eval : Code) : Code :=
  .block [bootFrame,readLiteralAdvice,ExtendedFrame.install,readBroadcast,select eval]

/-- The generic evaluation body uses the exact assembler order. -/
theorem withStartup_evaluate (epochs groups arguments occurrences : Code) :
    withStartup (evaluate epochs groups arguments occurrences) =
      assemble ExtendedFrame.install epochs groups arguments occurrences := rfl

private theorem linked_iff {eval : Code} {s m es t mt} :
    Runs pub mac (withStartup eval) s m es t mt ↔
      Runs pub mac (.seq unitStartup (.seq readBroadcast (select eval))) s m es t mt :=
  Runs.block_append_iff (a := [bootFrame,readLiteralAdvice,ExtendedFrame.install])
    (b := [readBroadcast,select eval]) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

private theorem withoutAccept {eval : Code} (he : eval.withoutAccept = true) :
    (withStartup eval).withoutAccept = true := by
  have h : (withStartup unit).withoutAccept = true := by decide
  simpa only [withStartup,select,Code.block,Code.withoutAccept,he,
    show unit.withoutAccept = true by decide] using h

/-- An actual completed startup followed by the physical broadcast and unit test has
the indicated bounded successful run exactly on that test. -/
theorem startup_unit_test (f : BroadcastFrame) (L : Layout) (eval : Code)
    {s m fs a ma} (startRun : Runs pub mac unitStartup s m fs a ma) {ct : ℕ} (cost : traceCost fs ≤ ct)
    (image : f.At (readings pub) (readings ma)) (fit : f.Fits w (pub 0).val)
    (bits : f.ReferenceBits (readings ma)) (zero : readings ma (f.addr f.partner 0) = 0)
    (frame : Frame L (readings pub) (readings ma)) (hs : L.stride < 2^w) (hc : L.count < 2^w)
    (room : L.width ≤ L.count) (apart : L.starbase+L.width ≤ f.dst ∨ f.dst+f.header ≤ L.starbase)
    (pins : L.team = 0 → IdentityFits L w) :
    TestRun pub mac (withStartup eval) s m (ct+(f.readTicks+(2+unitBudget f L)))
      (UnitTest f L ma) (fun z => z.mem = f.copied (readings ma) f.header) := by
  have tail := broadcast_unit f L eval pub mac a ma image fit bits zero frame hs hc room apart pins
  constructor
  · intro ok
    obtain ⟨gs,z,mz,body,bc,image'⟩ := tail.complete ok
    exact ⟨fs++gs,z,mz,linked_iff.mpr (startRun.seq body),
      (Transmission.cost_append fs gs).trans_le (Nat.add_le_add cost bc),image'⟩
  · intro es z mz r
    obtain ⟨t,mt,_,_,_,start,body⟩ := Runs.seq_iff.mp (linked_iff.mp r)
    obtain ⟨_,rfl,rfl⟩ := start.unique_of_deterministic (by decide) startRun
    exact tail.sound body

/-- For the zero reference tag the complete assembled table has exactly the same
returns as replacing its unused evaluation branch by the unit check. -/
theorem startup_zero_runs_iff (f : BroadcastFrame) (eval : Code)
    {s m fs a ma} (startRun : Runs pub mac unitStartup s m fs a ma)
    (image : f.At (readings pub) (readings ma)) (fit : f.Fits w (pub 0).val)
    (bits : f.ReferenceBits (readings ma)) (zero : readings ma (f.addr f.partner 0) = 0)
    {es z mz} :
    Runs pub mac (withStartup eval) s m es z mz ↔ Runs pub mac (withStartup unit) s m es z mz := by
  have pass (e e' : Code) (run : Runs pub mac (withStartup e) s m es z mz) :
      Runs pub mac (withStartup e') s m es z mz := by
    obtain ⟨t,mt,xs,ys,joined,first,tail⟩ := Runs.seq_iff.mp (linked_iff.mp run)
    obtain ⟨_,ht,hm⟩ := first.unique_of_deterministic (by decide) startRun
    subst t
    subst mt
    obtain ⟨u,mu,bs,qs,tails,bc,branch⟩ := Runs.seq_iff.mp tail
    obtain ⟨_,stable,copy⟩ := (readBroadcast_test f pub mac a ma image fit bits).sound bc
    have at0 : (mu f.dst).val = 0 := by
      change readings mu f.dst = _
      change readings mu = f.copied (readings ma) f.header at copy
      rw [copy,←Nat.add_zero f.dst,f.copied_at _ fit.branch,zero]
    obtain ⟨gs,eq,inside⟩ := (select_iff f e u mu stable).mp branch
    have same : Runs pub mac (select e') u mu qs z mz :=
      (select_iff f e' u mu stable).mpr ⟨gs,eq,by simpa only [at0,ite_true] using inside⟩
    exact linked_iff.mpr (Runs.seq_iff.mpr ⟨_,_,xs,ys,joined,first,
      Runs.seq_iff.mpr ⟨_,_,bs,qs,tails,bc,same⟩⟩)
  exact ⟨pass eval unit,pass unit eval⟩

private theorem noBurst {es : List (TeamRAM.Event w)} (h : traceCost es = es.length) :
    ∀ e ∈ es, e.action.extra = 0 := by
  change RAMBuckets.cost _ es = es.length at h
  rw [RAMBuckets.cost_eq_length_add_probes] at h
  have zero : RAMBuckets.probeCount (fun e : TeamRAM.Event w => e.action.extra) es = 0 := by omega
  clear h
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [RAMBuckets.probeCount,Nat.add_eq_zero_iff] at zero
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact zero.1
    · exact ih zero.2 f hf

private theorem positiveWeight {es : List (TeamRAM.Event w)} (h : ∀ e ∈ es, e.sign = .plus) :
    pathWeight es = 1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.sign.value * pathWeight es = 1
    rw [h e (by simp),ih (fun e he => h e (by simp [he]))]
    rfl

/-- Every accepting trace of the zero-tag unit path obeys the genuine native cutoffs:
the proved tick bound, no external bursts, and zero private choice bits. Its integer
weight is one. -/
theorem startup_unit_effects (eval : Code) {s m ct} {ok : Prop} {P : NatState → Prop}
    (test : TestRun pub mac (withStartup eval) s m ct ok P)
    (zero : ∀ {es z mz}, Runs pub mac (withStartup eval) s m es z mz →
      Runs pub mac (withStartup unit) s m es z mz)
    (x : Returns (withStartup eval) pub mac s m) : Within ct 0 0 x.val.1 ∧ pathWeight x.val.1 = 1 := by
  have r := zero x.property
  obtain ⟨ys,t,mt,run,cap,_⟩ := test.complete (test.sound x.property).1
  have same := (r.unique_of_deterministic (by decide) (zero run)).1
  have unsigned := r.unsigned_events (by decide)
  refine ⟨⟨same ▸ cap,fun e he => ?_,fun e he => ?_⟩,positiveWeight (fun e he => (unsigned e he).2)⟩
  · exact (noBurst (r.deterministic_cost (by decide)) e he).le
  · rw [(unsigned e he).1]; rfl

/-- With a genuine zero-tag dispatch, the signed charged machine value on its actual
processor-header initialization is the zero-one indicator of its complete test. -/
theorem startup_unit_nativeValue {L : Layout} (fields : ProcessorFields L) (eval : Code)
    (hc : eval.withoutAccept = true) (s : Bank w) {ct ticks burst clock : ℕ} (tickFit : ct ≤ ticks) {ok : Prop} [Decidable ok]
    {P : NatState → Prop}
    (test : TestRun pub mac (withStartup eval) s (processorMemory fields w) ct ok P)
    (zero : ∀ {es z mz}, Runs pub mac (withStartup eval) s (processorMemory fields w) es z mz →
      Runs pub mac (withStartup unit) s (processorMemory fields w) es z mz) :
    nativeValue (processorMachine (withStartup eval) pub mac s fields) ticks burst clock =
      if ok then 1 else 0 := by
  let T := Returns (withStartup eval) pub mac s (processorMemory fields w)
  have lim (x : T) : Within ticks burst clock x.val.1 := by
    have h := (startup_unit_effects eval test zero x).1
    exact ⟨h.cost.trans tickFit,fun e he => (h.length e he).trans (Nat.zero_le _),
      fun e he => (h.choices e he).trans (Nat.zero_le _)⟩
  have sub : Subsingleton T := by
    constructor
    intro x y
    obtain ⟨he,ht,hm⟩ := (zero x.property).unique_of_deterministic (by decide) (zero y.property)
    exact Subtype.ext (Prod.ext he (Prod.ext ht hm))
  let := Fintype.ofFinite T
  rw [nativeValue_eq_return_sum (withStartup eval) pub mac s fields ticks burst clock (withoutAccept hc) lim]
  change (∑ x : T, pathWeight x.val.1) = _
  simp only [(fun x : T => (startup_unit_effects eval test zero x).2),
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  by_cases yes : ok
  · obtain ⟨es,t,mt,r,_,_⟩ := test.complete yes
    let : Unique T := ⟨⟨⟨(es,t,mt),r⟩⟩,fun _ => Subsingleton.elim _ _⟩
    simp [yes,Fintype.card_unique]
  · have : IsEmpty T := ⟨fun x => yes (test.sound x.property).1⟩
    simp [yes]

end RoutingISA.Evaluator

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

variable {w R r t d link inner n : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (u : Fin (R+1)) (pin advised : Fin d → Bool)
    (ext : Exterior R r link → Bool) (header dst ibase hbase starbase : ℕ)

/-- On a genuine wired processor input whose reference branch tag is zero, a returning
concrete startup that installed H* and retained the input and frame suffices to compute
the charged value of the complete table. The surviving path tests every incident wire and
the true secondary pin. All counts are at the indicated physical word and clock widths. -/
theorem Wiring.startup_unit_value (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (eval : Code) (fallsThrough : eval.withoutAccept = true) (ct ticks burst clock : ℕ) :
    let f := G.transferFrame u header dst
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    let initial := processorMemory F w
    ∀ {es a ma}, Runs pub mac unitStartup s initial es a ma → traceCost es ≤ ct →
      F.ContainsInput ma → (∀ i : Fin d, ma (starbase+i.val) = TeamTapeInputEmit.word w (advised i).toNat) →
      f.At (readings pub) (readings ma) → Frame L (readings pub) (readings ma) → f.Fits w (pub 0).val →
      readings initial (f.addr f.partner 0) = 0 → L.stride < 2^w → L.count < 2^w → L.width ≤ L.count →
      (L.starbase+L.width ≤ f.dst ∨ f.dst+f.header ≤ L.starbase) → (L.team = 0 → IdentityFits L w) →
      ct+(f.readTicks+(2+unitBudget f L)) ≤ ticks →
      nativeValue (processorMachine (withStartup eval) pub mac s F) ticks burst clock =
        if LocalUnit u pin advised ext then 1 else 0 := by
  intro f L F initial es a ma startRun cost physical reference image frame fit initZero hs hc room apart pins tickFit
  have hw : 0 < w := by by_contra! hz; obtain rfl := Nat.eq_zero_of_le_zero hz; have := fit.frame; have := fit.out; simp at *; omega
  have partner := f.partner_spec fit.three
  let v : Fin (R+1) := ⟨f.partner,partner.2⟩
  have ne : u ≠ v := fun eq => partner.1 (congrArg Fin.val eq.symm)
  have bits : f.ReferenceBits (readings ma) := by
    intro j hj
    have cap := hj.trans_le fit.cap
    let pos : Fin (r*link) := ⟨j,by simpa [f,Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm] using cap⟩
    exact (G.read_exterior_val hw u v ne pin ext ibase hbase starbase ma physical pos).trans_lt (Bool.toNat_lt _)
  have zero : readings ma (f.addr f.partner 0) = 0 := by
    have hi := f.addr_lt_input fit partner.2 partner.1 (fit.branch.trans_le fit.cap)
    have lt : f.addr f.partner 0 < F.header.length := by
      rw [F.header_length]
      simpa [f,F,Wiring.transferFrame,Wiring.pinLayout,Layout.stride,Layout.offset,BroadcastFrame.stride,
        Nat.two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi
    exact (congrArg Fin.val ((physical _ lt).trans ((F.containsInput_initial w) _ lt).symm)).trans initZero
  have check := startup_unit_test f L eval startRun cost image fit bits zero frame hs hc room apart pins
  have logical := check.mono le_rfl (G.unitTest_iff u pin advised ext header dst ibase hbase starbase
    ma physical reference hw room) (fun _ h => h)
  exact startup_unit_nativeValue F eval fallsThrough s tickFit logical
    (fun run => (startup_zero_runs_iff f eval startRun image fit bits zero).mp run)

end TeamContraction

end BorderVNP
end Computability
end OAI
