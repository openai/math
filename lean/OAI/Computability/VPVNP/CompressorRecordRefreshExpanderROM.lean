import OAI.Computability.VPVNP.CompressorRecordRefreshAllSlots

/-!
# Initializing the fixed expander incidence table

The fixed expander supplies one finite schedule row per outgoing port and
local slot. Each row carries the port and local slot of its reverse edge as
public words. A native call writes the two columns read by the degree-refresh
slot writer. These public values depend only on the expander.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.ExpanderROM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM NewSlots SpectralGeometry

variable {w D dH : ℕ}

/-- Public words are row ID, reverse port, reverse slot, port column base, and
slot column base. The call returns the successor row ID. -/
def put : List (Op 6 5) :=
  [.publicWord 0 0, .publicWord 1 3, .binary .add 1 1 0, .publicWord 2 1, .write 1 2,
   .publicWord 3 4, .binary .add 3 3 0, .publicWord 4 2, .write 3 4,
   .constant 5 1, .binary .add 0 0 5]

/-- The 11 events that publish an expander edge's destination port and reverse slot at its
fixed ordinal. -/
def events (p : Fin 5 → W w) : List (Event w) :=
  [.tick,.tick,.tick,.tick,.write (p 3+p 0) (p 1),.tick,.tick,.tick,.write (p 4+p 0) (p 2),.tick,.tick]

theorem events_work (p : Fin 5 → W w) : (events p).length = 11 ∧ countProbes (events p) = 2 :=
  ⟨rfl,rfl⟩

theorem events_after (p : Fin 5 → W w) (m : Memory w) :
    after m (events p) = writeMemory (writeMemory m (p 3+p 0) (p 1)) (p 4+p 0) (p 2) := rfl

private theorem put_trace (p : Fin 5 → W w) (state : W w) (m : Memory w) (regs : Regs w 6) :
    ∃ rs, trace p state put regs m = some (events p,rs,after m (events p)) ∧ rs 0 = p 0+1 := by
  simp (config := {decide := true}) [put,events,trace,Op.effect,BinaryOp.eval,Function.update]
  exact ⟨rfl,rfl⟩

theorem native (p : Fin 5 → W w) (state : W w) (m : Memory w) :
    let M := (template put 0).instantiate w p
    execute M.program 12 (M.program.start state) m [] = some ⟨events p,some (p 0+1)⟩ := by
  obtain ⟨rs,hr,hret⟩ := put_trace p state m (fun _ => 0)
  let M := (template put 0).instantiate w p
  change execute M.program (1 + put.length) ⟨M.entry,state,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace,hr]
  simp [hret]

variable (E : RegularArcGraph (Fin D) dH) (I : AllSlots.Tables w)

/-- Public schedule data for the edge with row-major ID `i`. -/
def words (i : Fin (D*dH)) : Fin 5 → W w :=
  let target := E.reverse (finProdFinEquiv.symm i)
  ![word i.val,word target.1.val,word target.2.val,I.targetPort,I.reverseSlot]

/-- The report of one fixed expander row, including its two writes and the next edge ordinal. -/
def report (i : Fin (D*dH)) : Report w :=
  ⟨events (words E I i),some (word i.val + 1)⟩

/-- Execute each hardwired row from the state and memory returned by the
previous call, collecting the actual reports. -/
def runRows : Option (W w) → Memory w → List (Fin (D*dH)) → Option (List (Report w))
  | _, _, [] => some []
  | none, _, _::_ => none
  | some state, m, i::is =>
    let M := (template put 0).instantiate w (words E I i)
    match execute M.program 12 (M.program.start state) m [] with
    | none => none
    | some r => (runRows r.result (after m r.events) is).map (r :: ·)

theorem schedule_run (state : W w) (m : Memory w) (is : List (Fin (D*dH))) :
    runRows E I (some state) m is = some (is.map (report E I)) := by
  induction is generalizing m state with
  | nil => rfl
  | cons i is ih =>
    rw [runRows,native]
    change (runRows E I (some (word i.val+1)) (after m (events (words E I i))) is).map (report E I i :: ·) = _
    rw [ih]
    rfl

/-- Both output regions fit, and their intervals are disjoint. -/
structure Regions (I : AllSlots.Tables w) (n : ℕ) : Prop where
  ports : I.targetPort.val+n ≤ 2^w
  slots : I.reverseSlot.val+n ≤ 2^w
  apart : I.targetPort.val+n ≤ I.reverseSlot.val ∨ I.reverseSlot.val+n ≤ I.targetPort.val

private def address (port : Bool) (i : Fin (D*dH)) : W w :=
  (if port then I.targetPort else I.reverseSlot) + word i.val

private def value (port : Bool) (i : Fin (D*dH)) : W w :=
  let dst := E.reverse (finProdFinEquiv.symm i)
  if port then word dst.1.val else word dst.2.val

private theorem address_val (reg : Regions I (D*dH)) (c : Bool) (i : Fin (D*dH)) :
    (address I c i).val = (if c then I.targetPort.val else I.reverseSlot.val) + i.val := by
  have fit : (if c then I.targetPort.val else I.reverseSlot.val) + D*dH ≤ 2^w := by
    cases c <;> first | exact reg.ports | exact reg.slots
  have hi := i.isLt
  have haddr : (if c then I.targetPort.val else I.reverseSlot.val) + i.val < 2^w := by omega
  rw [address,Fin.val_add]
  have hb : (if c then I.targetPort else I.reverseSlot).val = (if c then I.targetPort.val else I.reverseSlot.val) :=
    by cases c <;> rfl
  rw [hb,show (word (bits := w) i.val).val = i.val from Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt haddr]

private theorem address_inj (reg : Regions I (D*dH)) {c b : Bool} {i j : Fin (D*dH)}
    (he : address I c i = address I b j) : c=b ∧ i=j := by
  have h := congrArg Fin.val he
  rw [address_val I reg,address_val I reg] at h
  have hi := i.isLt
  have hj := j.isLt
  have ha := reg.apart
  cases c <;> cases b
  all_goals first | exact ⟨rfl,Fin.ext (Nat.add_left_cancel h)⟩ | simp at h; omega

private theorem written (reg : Regions I (D*dH)) (i : Fin (D*dH)) (m : Memory w) (c : Bool) :
    after m (report E I i).events (address I c i).val = value (w := w) E c i := by
  have ne : (address I true i).val ≠ (address I false i).val :=
    fun h => Bool.noConfusion (address_inj I reg (Fin.ext h)).1
  change (I.targetPort+word i.val).val ≠ (I.reverseSlot+word i.val).val at ne
  change writeMemory (writeMemory m (I.targetPort+word i.val) (value E true i))
    (I.reverseSlot+word i.val) (value E false i) (address I c i).val = _
  cases c with
  | false => exact ite_eq_left rfl
  | true =>
    change (if (I.targetPort+word i.val).val = (I.reverseSlot+word i.val).val then _ else _) = _
    rw [ite_eq_right ne]
    exact ite_eq_left rfl

private theorem frame (i : Fin (D*dH)) (m : Memory w) (addr : ℕ)
    (miss : ∀ c, addr ≠ (address I c i).val) : after m (report E I i).events addr = m addr := by
  have hp := miss true
  have hs := miss false
  change addr ≠ (I.targetPort + word i.val).val at hp
  change addr ≠ (I.reverseSlot + word i.val).val at hs
  change writeMemory (writeMemory m (I.targetPort+word i.val) (value E true i))
    (I.reverseSlot+word i.val) (value E false i) addr = _
  rw [writeMemory,ite_eq_right hs,writeMemory,ite_eq_right hp]

private theorem rows (reg : Regions I (D*dH)) (is : List (Fin (D*dH))) (m : Memory w) :
    let final := after m (eventLog (is.map (report E I)))
    (∀ i ∈ is, ∀ c, final (address I c i).val = value E c i) ∧
      ∀ addr, (∀ i ∈ is, ∀ c, addr ≠ (address I c i).val) → final addr = m addr := by
  induction is generalizing m with
  | nil => exact ⟨by simp,fun _ _ => rfl⟩
  | cons i is ih =>
    let mid := after m (report E I i).events
    have hm : after m (eventLog ((i::is).map (report E I))) = after mid (eventLog (is.map (report E I))) := by
      change List.foldl BurstRAM.update m ((report E I i).events ++ eventLog _) = _
      rw [List.foldl_append]; rfl
    obtain ⟨ht,hf⟩ := ih mid
    dsimp only
    rw [hm]
    constructor
    · intro j hj c
      by_cases already : j ∈ is
      · exact ht j already c
      have eq := (List.mem_cons.mp hj).resolve_right already
      subst j
      rw [hf _ (fun j hj b he => already ((address_inj I reg (c := c) (b := b) (i := i) (j := j) (Fin.ext he)).2.symm ▸ hj))]
      exact written E I reg i m c
    · intro addr outside
      rw [hf addr (fun j hj => outside j (List.mem_cons_of_mem _ hj))]
      exact frame E I i m addr (outside i List.mem_cons_self)

private theorem cost (is : List (Fin (D*dH))) :
    RAMBuckets.cost Report.probes (is.map (report E I)) = 3*is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have h : (report E I i).probes = 2 := (events_work _).2
    rw [List.map_cons,RAMBuckets.cost,h,ih,List.length_cons,Nat.mul_succ]
    omega

private theorem numbered_edge (e : Fin D × Fin dH) :
    (finProdFinEquiv e).val = e.1.val*dH+e.2.val := by
  change e.2.val + dH*e.1.val = _
  ring

/-- The values in the two cells are the actual port and slot of the reverse
edge, at exactly the addresses used by the slot writer. -/
structure Ready (m : Memory w) : Prop where
  targetPort : ∀ e : Fin D × Fin dH, (m (I.targetPort + word (e.1.val*dH+e.2.val)).val).val = (E.reverse e).1.val
  reverseSlot : ∀ e : Fin D × Fin dH, (m (I.reverseSlot + word (e.1.val*dH+e.2.val)).val).val = (E.reverse e).2.val

/-- Initialize the fixed expander from arbitrary incoming memory. The finite
schedule makes one call with two writes per edge, preserving all addresses
outside the two reserved intervals. -/
theorem initialize_expander (reg : Regions I (D*dH)) (m : Memory w) :
    let order := List.finRange (D*dH)
    let rs := order.map (report E I)
    let final := after m (eventLog rs)
    runRows E I (some 0) m order = some rs ∧ Ready E I final ∧
      (∀ addr, (addr < I.targetPort.val ∨ I.targetPort.val+D*dH ≤ addr) →
        (addr < I.reverseSlot.val ∨ I.reverseSlot.val+D*dH ≤ addr) → final addr = m addr) ∧
      RAMBuckets.cost Report.probes rs = 3*(D*dH) := by
  intro order rs final
  obtain ⟨values,preserve⟩ := rows E I reg order m
  have hfit : D*dH ≤ 2^w := by have := reg.ports; omega
  refine ⟨schedule_run E I 0 m order, ?_, ?_, by simpa [rs,order] using cost E I order⟩
  · constructor <;> intro e
    · have h := congrArg Fin.val (values (finProdFinEquiv e) (List.mem_finRange _) true)
      change (final (I.targetPort+word (finProdFinEquiv e).val).val).val =
        (word (bits := w) (E.reverse (finProdFinEquiv.symm (finProdFinEquiv e))).1.val).val at h
      rw [numbered_edge,Equiv.symm_apply_apply] at h
      exact h.trans (Nat.mod_eq_of_lt ((E.reverse e).1.isLt.trans_le
        ((Nat.le_mul_of_pos_right D (Nat.zero_lt_of_lt e.2.isLt)).trans hfit)))
    · have h := congrArg Fin.val (values (finProdFinEquiv e) (List.mem_finRange _) false)
      change (final (I.reverseSlot+word (finProdFinEquiv e).val).val).val =
        (word (bits := w) (E.reverse (finProdFinEquiv.symm (finProdFinEquiv e))).2.val).val at h
      rw [numbered_edge,Equiv.symm_apply_apply] at h
      exact h.trans (Nat.mod_eq_of_lt ((E.reverse e).2.isLt.trans_le
        ((Nat.le_mul_of_pos_left dH (Nat.zero_lt_of_lt e.1.isLt)).trans hfit)))
  · intro addr op os
    apply preserve
    intro i _ c
    rw [address_val I reg]
    have := i.isLt
    cases c <;> simp <;> omega

end CompressorRecords.PortRefresh.ExpanderROM

end VPVNP
end Computability
end OAI
