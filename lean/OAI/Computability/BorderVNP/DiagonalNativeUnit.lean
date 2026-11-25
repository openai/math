import OAI.Computability.BorderVNP.RoutingISAEvaluator
import OAI.Computability.BorderVNP.RoutingISAPaddingProof
import OAI.Computability.BorderVNP.TransmissionPinsIdentity
import OAI.Computability.BorderVNP.TransmissionPinsPositive
import Mathlib.SetTheory.Cardinal.Finite

/-! # The unit branch of the native diagonal evaluator

The branch first checks every incident exterior word and then, on team zero, compares
the true secondary pin with the advised distinguished column. It contributes one
positive accepting trace precisely when both physical tests hold.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Compose two actual read-only checks. The second starts in the registers returned
by the first and sees the same complete physical memory. -/
theorem NativeLinkCheck.seq {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {a b : Code} {s : Bank w} {m : Memory w} {ca cb : ℕ} {A B : Prop}
    (ha : NativeLinkCheck pub macros a s m ca A)
    (hb : ∀ t, NativeLinkCheck pub macros b t m cb B) :
    NativeLinkCheck pub macros (.seq a b) s m (ca+cb) (A ∧ B) := by
  constructor
  · rintro ⟨hA,hB⟩
    obtain ⟨fs,u,r,ct⟩ := ha.complete hA
    obtain ⟨gs,v,r',ct'⟩ := (hb u).complete hB
    exact ⟨_,v,r.seq r', (Transmission.cost_append fs gs).trans_le (Nat.add_le_add ct ct')⟩
  · intro es t mt r
    obtain ⟨u,mu,fs,gs,_,first,next⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,hA⟩ := ha.sound first
    obtain ⟨hm,hB⟩ := (hb u).sound next
    exact ⟨hm,hA,hB⟩

namespace Evaluator

open Pins

/-- The actual physical condition checked on the unit branch. -/
def UnitTest (f : BroadcastFrame) (L : Layout) (m : Memory w) : Prop :=
  (∀ i < f.teams, i ≠ f.team → f.ZeroFrom (readings m) 0 i) ∧ IdentityMatches L m

/-- Charged ticks for the exterior scan and the pin comparison. -/
def unitBudget (f : BroadcastFrame) (L : Layout) : ℕ :=
  f.linkCheckTicks (headerSetup.slots+1) 1 + (pinSetup.slots + 2 + L.width*(1+identityPinStep.slots))

/-- The entire unit branch validates the incident link blocks and the advised H* test in
the actual RAM image, with a concrete tick budget and exact memory preservation. -/
theorem unit_check (f : BroadcastFrame) (L : Layout) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (frame : Frame L (readings pub) (readings m)) (hframe : readings pub 0 + 24 < 2^w)
    (ht : 0 < L.teams) (hs : L.stride < 2^w) (hc : L.count < 2^w)
    (pins : L.team = 0 → IdentityFits L w) :
    NativeLinkCheck pub macros unit s m (unitBudget f L) (UnitTest f L m) := by
  apply (unitLinks_check f pub macros s m image fit).seq
  intro t
  constructor
  · exact checkIdentityPins_run L pub macros m t frame hframe ht hs hc pins
  · intro fs u mu r
    exact ⟨(checkIdentityPins_effects L pub macros m t frame hframe ht hs hc pins r).1,
      (checkIdentityPins_iff L pub macros m t frame hframe ht hs hc pins).mp ⟨fs,u,mu,r⟩⟩

/-- Actual accepting native paths, including the chronological word used by each fetch. -/
def NativeAccepts (c : Code) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :=
  {z : List (List Bool) × List (TeamRAM.Event w) //
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m z.1 = some z.2}

/-- A deterministic table with a single final accepting continuation has at most
one actual accepting tape and event list at fixed input registers and memory. -/
theorem nativeAccepts_subsingleton {c : Code} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} (det : c.deterministic = true) (ha : c.withoutAccept = true) :
    Subsingleton (NativeAccepts c pub macros s m) := by
  constructor
  rintro ⟨⟨b,fs⟩,hb⟩ ⟨⟨b',fs'⟩,hb'⟩
  obtain ⟨⟨u,mu,rr⟩,be⟩ := (Code.execute_iff_runs ha).mp hb
  change fs.map TeamRAM.Event.choices = b at be
  obtain ⟨⟨v,mv,rr'⟩,be'⟩ := (Code.execute_iff_runs ha).mp hb'
  change fs'.map TeamRAM.Event.choices = b' at be'
  subst b; subst b'
  have same : fs = fs' := (rr.unique_of_deterministic det rr').1
  exact Subtype.ext (by simp only [same])

/-- The cardinality of a deterministic native check is its zero-one acceptance indicator. -/
theorem native_check_card {c : Code} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s : Bank w} {m : Memory w} {bound : ℕ} {test : Prop} [Decidable test]
    (chk : NativeLinkCheck pub macros c s m bound test)
    (det : c.deterministic = true) (ha : c.withoutAccept = true) :
    Nat.card (NativeAccepts c pub macros s m) = if test then 1 else 0 := by
  have sub : Subsingleton (NativeAccepts c pub macros s m) := nativeAccepts_subsingleton det ha
  by_cases ht : test
  · rw [ite_eq_left ht, Nat.card_eq_one_iff_unique]
    obtain ⟨bs,es,run⟩ := (chk.execute_iff ha).mpr ht
    exact ⟨sub, ⟨⟨⟨bs,es⟩,run⟩⟩⟩
  · rw [ite_eq_right ht]
    have : IsEmpty (NativeAccepts c pub macros s m) :=
      ⟨fun z => ht ((chk.execute_iff ha).mp ⟨z.val.1,z.val.2,z.property⟩)⟩
    simp

/-- The returning unit trace carries no private choices and every event has positive sign. -/
theorem unit_trace {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m es t mt} (r : Runs pub macros unit s m es t mt) :
    es.flatMap TeamRAM.Event.choices = [] ∧ ∀ e ∈ es, e.sign = .plus :=
  ⟨Pins.noChoices r (by decide),r.positive (by decide)⟩

/-- The native selector on a saved zero tag has exactly the returns of the unit branch.
The selected evaluation code is arbitrary. -/
theorem select_zero_check (f : BroadcastFrame) (eval : Code) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (stable : f.Stable (readings s))
    (zero : (m f.dst).val = 0) {b : ℕ} {ok : Prop}
    (h : NativeLinkCheck pub macros unit (Function.update s 10 (m f.dst)) m b ok) :
    NativeLinkCheck pub macros (select eval) s m (2+b) ok := by
  constructor
  · intro yes
    obtain ⟨es,t,r,ct⟩ := h.complete yes
    refine ⟨_,t,(select_iff f eval s m stable).mpr ⟨es,rfl, by simpa [zero] using r⟩,?_⟩
    change 1+(1+traceCost es) ≤ 2+b
    omega
  · intro es t mt r
    obtain ⟨fs,_,rr⟩ := (select_iff f eval s m stable).mp r
    simp only [zero, ite_true] at rr
    exact h.sound rr

end Evaluator
end RoutingISA

end BorderVNP
end Computability
end OAI
