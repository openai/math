import OAI.Hierarchy.DescentTerminalEpochHeader

namespace OAI
/-! # Physical profile/seed/exterior admission of the reached history -/
namespace Hierarchy.DescentTerminalEpochHeader
open DescentTerminalEpochBits DescentTerminalEpochChart DescentTerminalEpochFlags
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

theorem admission_run {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}
    (b : Chart bits ok src) (z : b.Pin→Bool) (lo low terminal seedAddr : ℕ) (prev m : Memory w)
    (ctrl : Shelf b.Pin → Controls) (seed : m seedAddr=0 ↔ ok (z∘b.seed))
    (wide : ∀p∈directory lo b.layout,width p.source.C ≤ w)
    (hold : ∀p∈directory lo b.layout,∀i:Fin p.source.seats,
      m (p.codes.base+i.val)=memory lo b.layout z prev (p.codes.base+i.val))
    (counters : List.IsPrefix ((b.rows z).map Observation.count)
      ((directory lo b.layout).map fun p=>(m (ctrl p).count).val))
    (spaces : Spaced w low terminal seedAddr ((directory lo b.layout).map (issued ctrl)))
    (archive : ∀a∈(directory lo b.layout).map (issued ctrl),Archived w low a)
    (tables : ∀a∈(directory lo b.layout).map (issued ctrl),HasROM a.C a.rom m) :
    let ts := (directory lo b.layout).map (issued ctrl)
    (foldProgram w terminal seedAddr ts).Spec (·=m)
      (fun _ o=> o terminal=(if (∃t,b.read z=some t) ∧ ∀a∈ts,m a.exterior=0 then 0 else 1) ∧
        ∀i < low,o i=m i) (foldTime terminal seedAddr ts) ∧ CheapCode (foldProgram w terminal seedAddr ts) := by
  let ts := (directory lo b.layout).map (issued ctrl)
  have issued_ := fold_run low terminal seedAddr ts spaces archive m tables
  have survive := physical_survives b z lo seedAddr prev m ctrl seed wide hold counters
  have eql : (m seedAddr=0 ∧ ∀a∈ts,a.Valid m) ↔ (∃t,b.read z=some t) ∧ ∀a∈ts,m a.exterior=0 := by
    constructor
    · rintro ⟨base,rows⟩
      exact ⟨survive.mp ⟨base,fun e he=>(rows e he).2⟩,fun e he=>(rows e he).1⟩
    · rintro ⟨some_,ext⟩
      obtain ⟨base,fields⟩:=survive.mpr some_
      exact ⟨base,fun e he=>⟨ext e he,fields e he⟩⟩
  have flag_eq :
      (if m seedAddr=0 ∧ ∀a∈ts,a.Valid m then (0:Word w) else 1) =
      (if (∃t,b.read z=some t) ∧ ∀a∈ts,m a.exterior=0 then (0:Word w) else 1) := by
    by_cases h : m seedAddr=0 ∧ ∀a∈ts,a.Valid m
    · rw [ite_eq_left h,ite_eq_left (eql.mp h)]
    · rw [ite_eq_right h,ite_eq_right (fun h' => h (eql.mpr h'))]
  let spec (flag : Word w) := (foldProgram w terminal seedAddr ts).Spec (·=m)
    (fun _ o=>o terminal=flag ∧ ∀i<low,o i=m i) (foldTime terminal seedAddr ts)
  exact ⟨(congrArg spec flag_eq).mp issued_.1,issued_.2⟩

end
end Hierarchy.DescentTerminalEpochHeader

end OAI
