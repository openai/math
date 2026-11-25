import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.TickStageSpec
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # Linking native compressor passes with malformed-input rejection -/

namespace ThreeFlat.RAM.TickStageSpec
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure ContinuationLink TickFuel

variable {w : ℕ} {F : Type*} [Semiring F]

theorem prepare_of_spec (A : Procedure w) {pre : Memory w → Prop}
    {post : Memory w → Memory w → Prop} {t : ℕ} (proof : A.Spec pre post t) :
    Prepare A.block A.publicData pre post t := by
  intro p r k M P R pub exit installed words c m pc ok
  obtain ⟨n,hn,d,y,run,atExit,h⟩ := proof M P R pub exit installed words c m pc ok
  exact ⟨n,hn,d,y,atExit,h,run⟩

theorem admission_of_spec (field : FieldCode F w) (A : Procedure w) {pre : Memory w → Prop}
    {post : Memory w → Memory w → Prop} {t : ℕ} (proof : A.Spec pre post t) :
    Admission field A.block A.publicData pre (fun _ => True) post t := by
  intro p r k M P R pub exit installed words c m pc ok
  exact ⟨fun _ => prepare_of_spec A proof M P R pub exit installed words c m pc ok,
    fun h => (h trivial).elim⟩

/-- A pass may reject before its successor starts. On its successful path
the caller identifies which proposals the next pass accepts from its actual
output memory. Both prefix lengths are charged, including on rejected runs. -/
theorem admission_seq (field : FieldCode F w) (A B : Procedure w)
    {pre good leftGood rightPre rightGood : Memory w → Prop}
    {left right : Memory w → Memory w → Prop} {ka kb : ℕ}
    (a : Admission field A.block A.publicData pre leftGood left ka)
    (b : Admission field B.block B.publicData rightPre rightGood right kb)
    (needed : ∀ m, pre m → good m → leftGood m)
    (next : ∀ m o, pre m → leftGood m → left m o → rightPre o ∧ (rightGood o ↔ good m)) :
    Admission field (A.seq B).block (A.seq B).publicData pre good
      (fun m o => ∃ tmp, left m tmp ∧ right tmp o) (ka+kb) := by
  intro p r k M pc reg pub exit installed data c m start hp
  obtain ⟨ia,ib⟩ := (Block.seq_installed _ _ M pc reg pub exit).mp installed
  have da (i : Fin A.slots) : M.publicData (pub (i.castAdd B.slots)) = A.publicData i := by
    simpa [Procedure.seq] using data (i.castAdd B.slots)
  have db (i : Fin B.slots) : M.publicData (pub (Fin.natAdd A.slots i)) = B.publicData i := by
    simpa [Procedure.seq] using data (Fin.natAdd A.slots i)
  obtain ⟨yes,no⟩ := a M ((Fin.castAddEmb B.labels).trans pc)
    ((Fin.castAddEmb B.registers).trans reg) (pub ∘ Fin.castAdd B.slots)
    (pc (Fin.natAdd A.labels B.block.first)) ia da c m start hp
  by_cases h : leftGood m
  · obtain ⟨t,ht,c₁,m₁,hpc,hl,adv⟩ := yes h
    have forward := next m m₁ hp h hl
    obtain ⟨pass,reject⟩ := b M ((Fin.natAddEmb A.labels).trans pc)
      ((Fin.natAddEmb A.registers).trans reg) (pub ∘ Fin.natAdd A.slots) exit ib db c₁ m₁ hpc forward.1
    constructor
    · intro ok
      obtain ⟨u,hu,c₂,m₂,hpc₂,hr,advance₂⟩ := pass (forward.2.mpr ok)
      exact ⟨t+u,Nat.add_le_add ht hu,c₂,m₂,hpc₂,⟨m₁,hl,hr⟩,advance_trans adv advance₂⟩
    · intro bad
      have halted : Returns field M.program kb c₁ m₁ 0 := reject (fun yes => bad (forward.2.mp yes))
      exact (halted.prefix adv).later (by omega)
  · constructor
    · intro yes
      exact (h (needed m hp yes)).elim
    · intro _
      have halted : Returns field M.program ka c m 0 := no h
      exact halted.later (by omega)

end ThreeFlat.RAM.TickStageSpec

end OAI
