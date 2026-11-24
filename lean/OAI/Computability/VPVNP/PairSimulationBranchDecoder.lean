import OAI.Computability.VPVNP.PairSimulationSelectorReindex

/-! # Decoding the physical term bursts along a compression branch

A packet at one level consists of one full native burst per motif, in
worker order. The worker executes those bursts in its advised memory.
Its accepted choice determines the next state and the decoder of the
remaining levels. The final state consumes exactly the empty suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords NetworkKernel BurstRAM

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w : ℕ} {X : State a g} {p : StatePass A X b n} {o : PassOrigin B f hf p}

private def packetRows {m : ℕ} (ts : List (List Bool)) (h : ts.length = m) (i : Fin m) : List Bool :=
  ts.get (Fin.cast h.symm i)

private theorem ofFn_packetRows {m : ℕ} (ts : List (List Bool)) (h : ts.length = m) :
    List.ofFn (packetRows ts h) = ts := by
  subst m
  exact List.ofFn_get ts

/-- Check the number of bursts and the actual ordinal worker execution
before using the worker's proved inverse to recover the term. -/
noncomputable def WorkerInput.decodePacket (I : WorkerInput o w) (ts : List (List Bool)) :
    Option p.step.Choice :=
  if h : ts.length = o.motifCount then
    let rows := packetRows ts h
    if ok : (I.run rows).isSome then some (I.termEquiv.symm ⟨rows, ok⟩) else none
  else none

theorem WorkerInput.decodePacket_iff (I : WorkerInput o w) (ts : List (List Bool)) (i : p.step.Choice) :
    I.decodePacket ts = some i ↔ List.ofFn (I.termEquiv i).val = ts := by
  classical
  constructor
  · intro h
    unfold decodePacket at h
    split at h
    next hlen =>
      dsimp only at h
      split at h
      next ok =>
        have same := I.termEquiv.symm_apply_eq.mp (Option.some.inj h)
        rw [← same]
        exact ofFn_packetRows ts hlen
      next => contradiction
    next => contradiction
  · rintro rfl
    let rows := (I.termEquiv i).val
    have hlen : (List.ofFn rows).length = o.motifCount := List.length_ofFn
    have same : packetRows (List.ofFn rows) hlen = rows := by
      funext j
      simp [packetRows]
    have ok : (I.run rows).isSome := (I.termEquiv i).prop
    change I.decodePacket (List.ofFn rows) = some i
    rw [decodePacket, dite_eq_left hlen]
    change (if h : (I.run (packetRows (List.ofFn rows) hlen)).isSome then
      some (I.termEquiv.symm ⟨packetRows (List.ofFn rows) hlen,h⟩) else none) = some i
    simp only [same,dite_eq_left ok]
    exact congrArg some (I.termEquiv.symm_apply_apply i)

/-- Decode an arbitrary list of chronological level packets. The order
of subsequent workers depends on the term recovered at each level. -/
noncomputable def decodeOrdinalTapes {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X) :
    (origin : PassOrigins B f hf E) → WorkerInputs E origin w → List (List (List Bool)) → Option E.Choices :=
  match E with
  | .done _ => fun _ _ ts => match ts with | [] => some () | _ :: _ => none
  | .more _ tail => fun origin inputs ts => match ts with
    | [] => none
    | packet :: rest => (inputs.1.decodePacket packet).bind fun i =>
        (decodeOrdinalTapes (tail i) (origin.2 i) (inputs.2 i) rest).map (Sigma.mk i)

variable {a' g' b' n' : ℕ} {Y : State a' g'} (E : StateExecution A b' n' Y)
  (origin : PassOrigins B f hf E) (inputs : WorkerInputs E origin w)

theorem decodeOrdinalTapes_encode (z : E.Choices) :
    decodeOrdinalTapes E origin inputs (ordinalTapes E origin inputs z) = some z := by
  induction E with
  | done => cases z; rfl
  | more p tail ih =>
    obtain ⟨i,z⟩ := z
    simp only [ordinalTapes, decodeOrdinalTapes,
      (inputs.1.decodePacket_iff _ i).mpr rfl, Option.bind_some,
      ih i (origin.2 i) (inputs.2 i) z]
    rfl

/-- Exact inverse on all inputs, including empty executions, malformed
bursts, missing motifs and surplus level packets. -/
theorem decodeOrdinalTapes_iff (ts : List (List (List Bool))) (z : E.Choices) :
    decodeOrdinalTapes E origin inputs ts = some z ↔ ordinalTapes E origin inputs z = ts := by
  constructor
  · induction E generalizing ts with
    | done =>
      cases ts <;> cases z <;> simp [decodeOrdinalTapes, ordinalTapes]
    | more p tail ih =>
      cases ts with
      | nil => simp [decodeOrdinalTapes]
      | cons packet rest =>
        intro hz
        simp only [decodeOrdinalTapes] at hz
        obtain ⟨i,hi,ht⟩ := Option.bind_eq_some_iff.mp hz
        obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp ht
        exact congrArg₂ List.cons ((inputs.1.decodePacket_iff packet i).mp hi)
          (ih i (origin.2 i) (inputs.2 i) rest u hu)
  · rintro rfl
    exact decodeOrdinalTapes_encode E origin inputs z

theorem decodeOrdinalTapes_isSome_iff (ts : List (List (List Bool))) :
    (decodeOrdinalTapes E origin inputs ts).isSome ↔ ∃! z, ordinalTapes E origin inputs z = ts := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨z,hz⟩
    have e := (decodeOrdinalTapes_iff E origin inputs ts z).mp hz
    exact ⟨z,e,fun u hu => ordinalTapes_injective E origin inputs (hu.trans e.symm)⟩
  · rintro ⟨z,e,_⟩
    exact ⟨z,(decodeOrdinalTapes_iff E origin inputs ts z).mpr e⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
