import OAI.Hierarchy.ProtocolRAMControl
import OAI.Hierarchy.ProtocolConflictCheap

namespace OAI
/-! # Chronological advice, conflict selection and replacement passes -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

noncomputable section

/-- All ordinals in the currently loaded conflict list come from this same tape.
The bounds check permits the addressed greedy scan to compare its current row to
already emitted earlier decisions. A row supplies the proof that n is positive. -/
def peers {w : ℕ} (base n d : ℕ) (m : Memory w) (i : Fin n) (j : Fin d) : Fin n :=
  ⟨(m (base+n+j.val*n+i.val)).val % n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def failure {w : ℕ} (base n : ℕ) (m : Memory w) (i : Fin n) : Bool := decide (m (base+i.val)≠0)

def ConflictInput {w : ℕ} (base n d : ℕ) (m : Memory w) : Prop :=
  (∀ i : Fin n, m (base+i.val)=0 ∨ m (base+i.val)=1) ∧
  (∀ (i : Fin n) (j : Fin d), (m (base+n+j.val*n+i.val)).val<n)

theorem peers_packed {w : ℕ} (base n d : ℕ) (m : Memory w) (input : ConflictInput base n d m) :
    ProtocolConflictPack.Native.Packed base (failure base n m) (peers base n d m) m := by
  constructor
  · intro i
    obtain zero | one := input.1 i
    · simp [failure,zero]
    · by_cases nonzero : (1:Word w)=0
      · simp [failure,one,nonzero]
      · simp [failure,one,nonzero]
  · intro i j
    simp [peers,Nat.mod_eq_of_lt (input.2 i j)]

inductive Stage where
  | column (p : Pass)
  | conflicts (base candidates degree : ℕ)

def Stage.image {w : ℕ} : Stage → Memory w → Memory w
  | .column p,m => p.apply m
  | .conflicts b n d,m =>
    let out := ProtocolConflictPack.Native.dst b n d
    fillSegment out n (ProtocolConflictPack.Native.output out (failure b n m) (peers b n d m)) m

def Stage.procedure (w : ℕ) : Stage → Procedure w
  | .column p => p.procedure w
  | .conflicts b n d => ProtocolConflictPack.Native.scan w b n d

def Stage.Ready {w : ℕ} : Stage → Memory w → Prop
  | .column p,_ => p.Fits w
  | .conflicts b n d,m => ProtocolConflictPack.Native.dst b n d+n < 2^w ∧ ConflictInput b n d m

def Stage.clock : Stage → ℕ
  | .column p => p.clock
  | .conflicts _ n d => 4+n*(22+48*d)

theorem Stage.exec {w : ℕ} (s : Stage) (m : Memory w) (ok : s.Ready m) :
    (s.procedure w).Exec m (s.image m) s.clock := by
  cases s with
  | column p => exact scan_exec _ _ _ _ ok.1 ok.2
  | conflicts b n d =>
    intro P R K M pc reg pub exit rom data cfg start entry same
    subst start
    exact ProtocolConflictPack.Native.scan_spec b (failure b n m) (peers b n d m) ok.1
      M pc reg pub exit rom data cfg m entry (peers_packed b n d m ok.2)

def stages (w : ℕ) : List Stage → Procedure w
  | [] => program w []
  | s::ss => (s.procedure w).seq (stages w ss)

def stageResult {w : ℕ} : List Stage → Memory w → Memory w
  | [],m => m
  | s::ss,m => stageResult ss (s.image m)

def stageClock : List Stage → ℕ
  | [] => 4
  | s::ss => s.clock+stageClock ss

def StageInputs {w : ℕ} : List Stage → Memory w → Prop
  | [],_ => True
  | s::ss,m => s.Ready m ∧ StageInputs ss (s.image m)

theorem stages_exec {w : ℕ} (ss : List Stage) (m : Memory w) (input : StageInputs ss m) :
    (stages w ss).Exec m (stageResult ss m) (stageClock ss) := by
  induction ss generalizing m with
  | nil => exact program_exec [] m (by simp)
  | cons s ss ih =>
    apply Procedure.Exec.then (s.exec m input.1)
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact ih (s.image m) input.2 M pc reg pub exit rom data cfg start entry same

theorem stages_cheap (w : ℕ) (ss : List Stage) : CheapCode (stages w ss) := by
  induction ss with
  | nil => exact program_cheap w []
  | cons s ss ih =>
    refine cheap_seq (A:=s.procedure w) (B:=stages w ss) ?_ @ih
    cases s with
    | column p => exact scan_cheap w p.out p.rows p.term
    | conflicts b n d => exact ProtocolConflictPack.Native.scan_cheap w b n d

/-- Execute live conflict selection, update inventories, and project actual terminal
link and gate descriptors. No acceptance predicate on the final memory is a premise. -/
theorem staged_controller {w : ℕ} (ss : List Stage) (src dst n : ℕ) (owners : Bank)
    (fields : Fin 7 → Expr) (m : Memory w) (input : StageInputs ss m)
    (wide : 3<w) (dir : Owners owners n (stageResult ss m)) (banks : (packed owners fields).Fits w src)
    (source : src+8*n<2^w) (target : dst+9*n<2^w) (apart : src+8*n≤dst ∨ dst+9*n≤ src) :
    ((stages w ss).seq (controller w src dst n owners [] fields)).Exec m
      (finalMemory src dst n owners [] fields (stageResult ss m))
      (stageClock ss + ((4+(report src n owners fields).clock)+(27+117*n))) := by
  apply Procedure.Exec.then (stages_exec ss m input)
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact controller_exec src dst n owners [] fields _ (by simp) wide dir banks source target apart
    M pc reg pub exit rom data cfg start entry same


end
end Hierarchy.ProtocolRAM

end OAI
