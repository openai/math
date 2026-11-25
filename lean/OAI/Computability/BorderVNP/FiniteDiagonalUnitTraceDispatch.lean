import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceWideBoot

/-! # The unit path with the all-batch finite-field startup

After any deterministic unsigned prefix delivering the actual physical words, the
zero-tag selector enters the unit check. The trace bijection uses the full fetched
program with this prefix, so it also applies to the wide field-valued startup.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped Classical

variable {w m g : ℕ} {Q Γ : Type} {K : Type*} [Field K]

private theorem deterministic_branch_trace {L : Layout} (fields : ProcessorFields L)
    (pub : Arg → Word w) (bank : Bank w) (actual alt : Code)
    (fallsThrough : actual.withoutAccept = true) (det : alt.deterministic = true)
    (unsigned : alt.unsigned = true)
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ K m 8) (fuel : ℕ)
    {ct ticks burst clock : ℕ} (budget : ct ≤ ticks) {ok : Prop} {post : NatState → Prop}
    (test : TestRun pub (TeamSiteEvents.macros lib fuel) actual bank (processorMemory fields w) ct ok post)
    (mirror : ∀ {es t mt}, Runs pub (TeamSiteEvents.macros lib fuel) actual bank (processorMemory fields w) es t mt →
      Runs pub (TeamSiteEvents.macros lib fuel) alt bank (processorMemory fields w) es t mt) :
    let M := processorMachine actual pub (TeamSiteEvents.macros lib fuel) bank fields
    Nonempty (NativePath M ticks burst clock ≃ PLift ok) ∧
      ∀ p : NativePath M ticks burst clock,
        FieldProcessor.pathProduct actual.program pub lib ret fuel ⟨0,bank⟩ p.val = 1 := by
  intro M
  have runs (p : NativePath M ticks burst clock) : ∃ t mt, Runs pub (TeamSiteEvents.macros lib fuel)
      actual bank (processorMemory fields w) p.val t mt := ((Code.execute_iff_runs fallsThrough).mp p.property.1).1
  have yes (p : NativePath M ticks burst clock) : ok := by
    obtain ⟨_,_,h⟩ := runs p
    exact (test.sound h).1
  refine ⟨⟨Equiv.ofBijective (fun p => (⟨yes p⟩ : PLift ok)) ⟨?_,?_⟩⟩,?_⟩
  · intro p q _
    obtain ⟨_,_,hp⟩ := runs p
    obtain ⟨_,_,hq⟩ := runs q
    exact Subtype.ext ((mirror hp).unique_of_deterministic det (mirror hq)).1
  · intro h
    obtain ⟨es,t,mt,run,ct',_⟩ := test.complete h.down
    have hAlt := mirror run
    have extra (e) (he : e ∈ es) : e.action.extra = 0 := by
      obtain ⟨probe,hp⟩ := ordinary_of_deterministic hAlt det e he
      rw [hp]; rfl
    refine ⟨⟨es,run.execute,ct'.trans budget,fun e he => (extra e he).le.trans (Nat.zero_le _),?_⟩,Subsingleton.elim ..⟩
    intro e he
    rw [(hAlt.unsigned_events unsigned e he).1]
    exact Nat.zero_le _
  · intro p
    obtain ⟨_,_,run⟩ := runs p
    have hAlt := mirror run
    exact pathProduct_ordinary_positive _ _ _ _ _ _ _ (TeamRAM.execute_spec run.execute).1
      (ordinary_of_deterministic hAlt det) (fun e he => (hAlt.unsigned_events unsigned e he).2)

variable {R r t d link inner n : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {u : Fin (R+1)} {pin : Fin d → Bool} {ext : Exterior R r link → Bool}
  {ibase hbase starbase header dst : ℕ} {pub : Arg → Word w} {bank : Bank w}

/-- The local trace index for a full wide-boot field machine, at its zero header bit.
The numerical field outputs of all private routines are arbitrary. -/
theorem BootSnapshot.unitTrace (advised : Fin d → Bool)
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ K m 8) (fuel : ℕ)
    (b : BootSnapshot G u pin ext ibase hbase starbase header dst wideStartup pub (TeamSiteEvents.macros lib fuel) bank)
    (eval : Code) (fallsThrough : (dispatchTable wideStartup eval).withoutAccept = true)
    (ticks burst clock : ℕ) :
    let f := G.transferFrame u header dst
    let L := G.pinLayout u ibase hbase starbase
    let fields := G.processorFields u pin ext ibase hbase starbase
    (∀ i : Fin d, b.mem (starbase+i.val) = TeamTapeInputEmit.word w (advised i).toNat) →
    readings b.mem (f.addr f.partner 0) = 0 → Frame L (readings pub) (readings b.mem) →
    L.stride < 2^w → L.count < 2^w → L.width ≤ L.count →
    (L.starbase+L.width ≤ f.dst ∨ f.dst+f.header ≤ L.starbase) → (L.team = 0 → IdentityFits L w) →
    traceCost b.events + (f.readTicks+(2+unitBudget f L)) ≤ ticks →
    let M := processorMachine (dispatchTable wideStartup eval) pub (TeamSiteEvents.macros lib fuel) bank fields
    Nonempty (NativePath M ticks burst clock ≃ PLift (LocalUnit u pin advised ext)) ∧
      ∀ p : NativePath M ticks burst clock,
        FieldProcessor.pathProduct (dispatchTable wideStartup eval).program pub lib ret fuel ⟨0,bank⟩ p.val = 1 := by
  intro f L fields ref zero frame stride count room apart pins budget
  let mac : TeamOpcode.Macros w 8 := TeamSiteEvents.macros lib fuel
  have hw : 0 < w := by
    by_contra! hn
    obtain rfl := Nat.eq_zero_of_le_zero hn
    have := b.fit.frame; have := b.fit.out; simp at *; omega
  have bits := (G.broadcast_input u pin ext ibase hbase starbase header dst b.mem b.input b.fit).1
  have localTest := broadcast_unit f L eval pub mac b.registers b.mem b.frame b.fit bits zero frame
    stride count room apart pins
  have tailTest := localTest.mono le_rfl (G.unitTest_iff u pin advised ext header dst ibase hbase starbase b.mem
    b.input ref hw room) (fun _ h => h)
  have test : TestRun pub mac (dispatchTable wideStartup eval) bank (processorMemory fields w)
      (traceCost b.events+(f.readTicks+(2+unitBudget f L))) (LocalUnit u pin advised ext)
      (fun _ => True) := by
    constructor
    · intro ok
      obtain ⟨es,z,mz,go,cost,_⟩ := tailTest.complete ok
      exact ⟨b.events++es,z,mz,b.run.seq go,(Transmission.cost_append ..).trans_le
        (Nat.add_le_add_left cost _),trivial⟩
    · intro es z mz run
      obtain ⟨s,m,_,_,_,boot,tail⟩ := Runs.seq_iff.mp run
      obtain ⟨_,rfl,rfl⟩ := boot.unique_of_deterministic (by decide) b.run
      exact ⟨(tailTest.sound tail).1,trivial⟩
  apply deterministic_branch_trace fields pub bank _ (dispatchTable wideStartup unit) fallsThrough
    (by decide) (by decide) lib ret fuel budget test
  intro es z mz run
  obtain ⟨s,m,fs,gs,joined,pre,tail⟩ := Runs.seq_iff.mp run
  obtain ⟨_,rfl,rfl⟩ := pre.unique_of_deterministic (by decide) b.run
  obtain ⟨bb,mm,hs,qs,rfl,bc,branch⟩ := Runs.seq_iff.mp tail
  obtain ⟨_,stable,copy⟩ := (readBroadcast_test f pub mac _ _ b.frame b.fit bits).sound bc
  have at0 : (mm f.dst).val = 0 := by
    change readings mm f.dst = _
    change readings mm = f.copied (readings b.mem) f.header at copy
    rw [copy,←Nat.add_zero f.dst,f.copied_at _ b.fit.branch,zero]
  obtain ⟨body,eq,inside⟩ := (select_iff f eval bb mm stable).mp branch
  exact Runs.seq_iff.mpr ⟨_,_,fs,hs++qs,joined,pre,Runs.seq_iff.mpr ⟨_,_,hs,qs,rfl,bc,
    (select_iff f unit bb mm stable).mpr ⟨body,eq,by simpa only [at0,ite_true] using inside⟩⟩⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
