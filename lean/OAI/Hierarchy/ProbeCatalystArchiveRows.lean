import OAI.Hierarchy.ProbeCatalystArchiveGeometry
import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # Padded reserve records on a full mixed repair calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe Calendar ColumnWires
open scoped BigOperators Classical

variable {C H E G R : Type*} [Fintype C] [Fintype H] [Fintype E]
    {k balls D count : ℕ}

/-- The original owner of an occupied ball and catalyst field. Padded fields,
non-catalyst roles, and unused balls have no source on this board. -/
def decode (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (cell : Fin balls × Fin D) : Option (R × (C × Fin k)) :=
  if h : ∃z,portCell ballsAt bound z=cell then some h.choose else none

theorem decode_at (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (z : R × (C × Fin k)) : decode ballsAt bound (portCell ballsAt bound z)=some z := by
  have hit : ∃y,portCell ballsAt bound y=portCell ballsAt bound z := ⟨z,rfl⟩
  rw [decode,dite_eq_left hit]
  exact congrArg some ((portCell ballsAt bound).injective hit.choose_spec)

theorem decode_spec (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    {cell : Fin balls × Fin D} {z : R × (C × Fin k)} (read : decode ballsAt bound cell=some z) :
    portCell ballsAt bound z=cell := by
  unfold decode at read
  split at read
  next h =>
    exact (Option.some.inj read) ▸ h.choose_spec
  next => contradiction

/-- Every event contributes its actual rectangular array. The owner and
number of charged bits may be read directly by the two-word reserve archive. -/
structure Entry (count payload : ℕ) where
  rows : ℕ
  owner : Fin rows→Fin count
  bits : Fin rows→ℕ
  fits : ∀ v,bits v≤payload
  separate : ∀ v u, 0 < bits v → 0 < bits u → owner v = owner u → v = u

def noneEntry (count payload : ℕ) : Entry count payload :=
  ⟨0,Fin.elim0,Fin.elim0,fun v=>v.elim0,fun v=>v.elim0⟩

/-- The hardware may store an arbitrary in-range destination beside a zero
amount. A positive read identifies the physical owner uniquely. -/
def Entry.withOwners {payload : ℕ} (e : Entry count payload) (native : Fin e.rows→Fin count)
    (read : ∀j,0<e.bits j→native j=e.owner j) : Entry count payload :=
  {e with owner:=native, separate:=fun i j hi hj eq=>
    e.separate i j hi hj ((read i hi).symm.trans (eq.trans (read j hj)))}

def repairEntry {payload : ℕ} (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count) (idle : Fin count)
    (readBits : Fin balls × Fin D→ℕ)
    (bounded : ∀z,readBits (portCell ballsAt bound z)≤payload) : Entry count payload :=
  let slots := finProdFinEquiv (m:=balls) (n:=D)
  let original := fun v : Fin (balls*D)=>decode ballsAt bound (slots.symm v)
  let key := (physical (k:=k) columns).trans keys
  { rows := balls*D
    owner := fun v=>(original v).elim idle key
    bits := fun v=>(original v).elim 0 (fun _=>readBits (slots.symm v))
    fits := by
      intro v
      cases hz : original v with
      | none => exact Nat.zero_le _
      | some z =>
        have val := decode_spec ballsAt bound hz
        exact val ▸ bounded z
    separate := by
      intro v u hv hu eq
      cases hz : original v with
      | none => simp [hz] at hv
      | some z =>
        cases hy : original u with
        | none => simp [hy] at hu
        | some y =>
          have same : z=y := key.injective (by simpa only [hz,hy,Option.elim_some] using eq)
          apply slots.symm.injective
          exact (decode_spec ballsAt bound hz).symm.trans (same ▸ decode_spec ballsAt bound hy) }

def fuel (c : Mesh) :=
  (c.inject+c.cool)*(c.outerFuel*(1+c.reserveSteps*(c.innerFuel+1))+1)

/-- The native signed debit column may be used verbatim once each of its
positive entries is identified with a live physical ball and catalyst field.
Nothing is assumed about the destination of a zero-valued word. -/
theorem repair_bits {payload : ℕ} (ballsAt : R ↪ Fin balls)
    (bound : Fintype.card (Role C H E k)≤D) (columns : R × C ↪ G)
    (keys : G × Fin k ↪ Fin count) (idle : Fin count) (read : Fin balls × Fin D→ℕ)
    (bounded : ∀z,read (portCell ballsAt bound z)≤payload)
    (positive : ∀ cell,0<read cell→∃z,portCell ballsAt bound z=cell) (cell : Fin balls × Fin D) :
    (repairEntry ballsAt bound columns keys idle read bounded).bits (finProdFinEquiv cell)=read cell := by
  change (decode ballsAt bound (finProdFinEquiv.symm (finProdFinEquiv cell))).elim 0
    (fun _=>read (finProdFinEquiv.symm (finProdFinEquiv cell)))=read cell
  rw [Equiv.symm_apply_apply]
  by_cases h : 0<read cell
  · obtain ⟨z,rfl⟩ := positive cell h
    rw [decode_at]
    rfl
  · have zero : read cell=0 := Nat.eq_zero_of_not_pos h
    cases decode ballsAt bound cell <;> simp [zero]

theorem repair_owner {payload : ℕ} (ballsAt : R ↪ Fin balls)
    (bound : Fintype.card (Role C H E k)≤D) (columns : R × C ↪ G)
    (keys : G × Fin k ↪ Fin count) (idle : Fin count) (read : Fin balls × Fin D→ℕ)
    (bounded : ∀z,read (portCell ballsAt bound z)≤payload) (z : R × (C × Fin k)) :
    (repairEntry ballsAt bound columns keys idle read bounded).owner
      (finProdFinEquiv (portCell ballsAt bound z))=keys (physical columns z) := by
  change (decode ballsAt bound (finProdFinEquiv.symm (finProdFinEquiv _))).elim idle _=_
  rw [Equiv.symm_apply_apply,decode_at]
  rfl

def eventEntry {payload : ℕ} (issued : Attempt→Entry count payload) :
    Event→Entry count payload
  | .attempt a => issued a
  | .feed _ => noneEntry count payload

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
