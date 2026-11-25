import OAI.Computability.BorderVNP.TeamSiteProcessorSort
import OAI.Computability.BorderVNP.TeamSiteWork

/-! # Shared processor stacks after parsing the physical input

Time-zero initialization writes directly to the same record buffer used by ordinary
instructions and private calls. The fixed literal fills the public words and clock
limits. The incident handoff decoder then fills the initially empty ISA registers and
elapsed clock, without changing the sorter metadata or comparison wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Bank

open VPVNP BurstRAM RAMTape Layout TeamTapeSorting
open RAMSerialization (WordRecord)

variable {r k d w : ℕ}

/-- All of the raw parser's retained stacks, with the processor work area still empty. -/
def fromEntry (s : Stacks TeamTapeInput.Entry.Port) : Stacks (Layout.Port r k d)
  | .route (.inr (.entry p)) => s p
  | _ => []

/-- Public and constant words loaded before the incident handoff is decoded.
Architectural registers and the incoming elapsed time have empty destinations. -/
def preClock (pub : Fin k → Word w) (H limit max : Word w) : Stacks (TeamLocalClock.Port r k)
  | .isa (.pub i) => wordBits (pub i)
  | .isa .persistent | .meter .persistent => wordBits (0 : Word w)
  | .meter (.reg i) => ![wordBits H,wordBits limit,[],wordBits (0 : Word w),
      wordBits (1 : Word w),wordBits (0 : Word w)] i
  | .maxBurst => wordBits max
  | _ => []

/-- Loaded clock words, unary frame geometry and the unconsumed portions of the physical
streams. All other input-parser stacks, including the actual record buffer, are retained. -/
def loaded (s : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w) (H limit max : Word w)
    (literalTail wires marks ingress egress : List Bool) : Stacks (Layout.Port r k d)
  | .route (.inr (.entry (.inl (.peek .input)))) => literalTail
  | .route (.inr (.entry (.inl (.cut .incident)))) => wires
  | .work (.clock u) => preClock pub H limit max u
  | .width => List.replicate w true
  | .frameWidth => marks
  | .incoming => ingress
  | .outgoing => egress
  | u => fromEntry s u


variable (s : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w) (H limit max : Word w)
    (literalTail wires marks ingress egress : List Bool)

/-- The three subprograms see the same pre-decoding bank. In particular the PC, each
architectural register, and the elapsed clock are empty until the frame is read. -/
theorem startup_view :
    (loaded (r := r) (d := d) s pub H limit max literalTail wires marks ingress egress ∘ endpoint ∘
      Endpoint.startup) = TeamLocalClock.Startup.input pub H limit max ingress := by
  symm
  apply installStacks_frame TeamLocalClock.Startup.codecPorts_injective
  · intro i
    cases i with
    | field i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.lastCases ?_ (fun j => ?_) j <;>
          simp [TeamLocalClock.Startup.codecPorts, TeamLocalClock.Startup.fieldPort,
            Function.comp_def, Endpoint.startup, endpoint, site, loaded, preClock,
            TeamTapeHandoff.Codec.incoming]
    | _ => rfl
  · intro u hu
    cases u with
    | wire => exact (hu .wire rfl).elim
    | width => exact (hu .width rfl).elim
    | tmp => exact (hu .tmp rfl).elim
    | tag => exact (hu .tag rfl).elim
    | pc => exact (hu (.field 0) rfl).elim
    | clock x =>
      cases x with
      | isa v =>
        cases v with
        | reg j =>
          exact (hu (.field j.castSucc.succ) (by simp [TeamLocalClock.Startup.codecPorts,
            TeamLocalClock.Startup.fieldPort])).elim
        | logPort j => cases j <;> rfl
        | _ => rfl
      | meter v =>
        cases v with
        | reg j =>
          have ne : j ≠ 2 := by
            rintro rfl
            exact hu (.field (Fin.last r).succ) (by simp [TeamLocalClock.Startup.codecPorts,
              TeamLocalClock.Startup.fieldPort])
          fin_cases j <;> first | rfl | contradiction
        | logPort j => cases j <;> rfl
        | pub j => exact Fin.elim0 j
        | _ => rfl
      | _ => rfl

/-- The initial word records emitted from this site's own input tape are the starting
prefix for all subsequent read, write, and private-burst operations. -/
theorem workReady {hw : 2 ≤ w+1} {capacity a : ℕ} {bits : List Bool}
    {rs : List (WordRecord (w+1))}
    (ready : TeamTapeInputEmit.Ready hw capacity a bits rs
      (s ∘ TeamTapeInput.Entry.setupPort ∘ TeamTapeInputEmit.Setup.Port.emit)) :
    Work.Ready hw capacity rs
      (loaded (r := r) (d := d) s pub H limit max literalTail wires marks ingress egress ∘ site) := by
  refine ⟨fun _ => Nat.zero_le _, rfl, fun _ => Nat.zero_le _, ready.buffer,
    ready.fields, ?_, rfl, rfl, fun _ => rfl⟩
  intro i
  cases i <;> exact Nat.zero_le _

variable {m g n e D : ℕ}

/-- The retained sorter geometry and parser scratch prepare both virtual lanes on
the physical owner. The public and wire streams may have arbitrary unused suffixes. -/
theorem routeReady (f : Fields D e (w+1)) (v : Word D) (other : Option (Word D))
    (literal : ∃ t, literalTail = TeamTapeInputRoute.metadataBits n e (w+1) v other ++ t)
    (incident : ∃ t, wires = TeamTapeInputRoute.ownerBits f v other ++ t)
    (width : (s (.inr .start)).length = w+1) (bucket : (s (.inr .bucket)).length = 2^e)
    (bits : s (.inl .bits) = []) (high : s (.inl .high) = []) (scratch : s (.inl .scratch) = []) :
    RouteReady n f v other (loaded (r := r) (d := m*g) s pub H limit max literalTail wires marks ingress egress) :=
  ⟨literal,incident,width,bucket,rfl,bits,high,scratch,rfl,rfl,fun _ _ => rfl,fun _ => rfl⟩

end TeamSite.Processor.Bank

namespace TeamSite.Processor

open VPVNP BurstRAM RAMTape Layout TeamTapeSorting

variable {r k m g d e w n : ℕ}

/-- Endpoint work can write the record buffer but cannot change the sorter's raw
comparison wires, parameters, or parsing workspace. -/
theorem RouteReady.installEndpoint {f : Fields d e w} {v other}
    {s : Stacks (Layout.Port r k (m*g))} (ready : RouteReady n f v other s)
    (out : Stacks (Endpoint.Port r k (m*g))) :
    RouteReady n f v other (installStacks endpoint s out) := by
  have eq (u : TeamTapeInputRoute.Verify.Port) (outside : ∀ i, buffer (r := r) (k := k) (d := m*g) i ≠ Layout.Port.route u) :
      installStacks endpoint s out (.route u) = s (.route u) := by
    apply installStacks_outside
    intro j
    cases j with
    | site v =>
      cases v with
      | burst b =>
        cases b with
        | probe p =>
          cases p with
          | buffer i => exact outside i
          | _ => simp [endpoint,site]
        | _ => simp [endpoint,site]
      | _ => simp [endpoint,site]
    | _ => simp [endpoint]
  rcases ready.literal with ⟨t,ht⟩; rcases ready.wires with ⟨z,hz⟩
  refine ⟨⟨t,(eq _ (by simp)).trans ht⟩, ⟨z,(eq _ (by simp)).trans hz⟩, ?_, ?_,
    (eq _ (by simp)).trans ready.suffix, (eq _ (by simp)).trans ready.bits,
    (eq _ (by simp)).trans ready.high, (eq _ (by simp)).trans ready.tmp,
    (eq _ (by simp)).trans ready.count, (eq _ (by simp)).trans ready.scratch,
    fun b i => (eq _ (by simp)).trans (ready.post b i), fun i => (eq _ (by simp)).trans (ready.guard i)⟩
  · rw [eq _ (by simp)]; exact ready.width
  · rw [eq _ (by simp)]; exact ready.bucket

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
