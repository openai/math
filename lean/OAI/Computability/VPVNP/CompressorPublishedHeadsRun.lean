import OAI.Computability.VPVNP.CompressorBlockHeaderPacket

/-!
# Native publication of consecutive DFS header words

Each published head executes one fixed six-instruction write and returns its
cursor at one. The following source packet evaluates its operands on the
memory left by that write. The frame and readback proofs ensure that each
value is the one computed from the original graph and its arena pointers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PublishedHeads

open BurstRAM DescriptorSpace PhaseRecipe BlockPlanner BlockHeaderRun SourceTransport SourceOnline
open scoped Fin.CommRing

variable {w N : ℕ}

/-- Native six-event report for publishing one word at a specified address and returning cursor
one. -/
def report (dest value : Word w) : Report w :=
  ⟨[.tick,.tick,.tick,.write dest value,.tick,.tick],some 1⟩

theorem one (L : Layout) (pub : Fin 5 → Word w) (s : Word w) (dest val : Expr) (m : Memory w)
    (hw : 1 < 2^w) (hd : levelStart L 0 ≤ (dest.eval pub s m).val) :
    let d := dest.eval pub s m
    let x := val.eval pub s m
    HeaderPacket.Run L pub s (publish dest val) m [report d x] 7 [[]] ∧
      after m (eventLog [report d x]) = writeMemory m d x := by
  intro d x
  let par : Fin 2 → Word w := ![d,x]
  have raw : rawCall (publish dest val) pub s m 7 = some (report d x) := by
    have eq : (fun i ↦ ((publish dest val).params i).eval pub s m) = par := by
      funext i; fin_cases i <;> rfl
    unfold rawCall
    rw [eq]
    have h := (publish_native dest val par 0 m).1
    have i₀ : (publish dest val).initial.eval pub s m = 0 := Nat.cast_zero
    have p₀ : par 0 = d := rfl
    have p₁ : par 1 = x := rfl
    simpa only [i₀,p₀,p₁,report,zero_add] using h
  refine ⟨HeaderPacket.singleton (by decide) raw ?_ ?_ ?_ ?_,rfl⟩
  · apply Fin.lt_def.mpr
    change 0 % 2^w < 1 % 2^w
    simp [Nat.mod_eq_of_lt hw]
  · change some (1 : Word w) = some ((1 : ℕ) : Word w); simp
  · intro a v hv; simp [report] at hv
  · intro a v hv; simp [report] at hv; exact hv.1 ▸ hd

/-- Memory after the fixed ordered publication, expressed solely using the
original graph operands and the destination block. -/
def image (pub : Fin 5 → Word w) (state : Word w) (original : Memory w) (base : ℕ) (rhs : Fin N → Expr) :=
  after original (eventLog (List.ofFn fun j : Fin N ↦ report ((base+j.val : ℕ) : Word w)
    ((rhs j).eval pub state original)))

/-- All addresses outside a contiguous field block retain their old words. -/
def Outside (base count a : ℕ) := a < base ∨ base+count ≤ a

variable (L : Layout) (pub : Fin 5 → Word w) (state : Word w) (original : Memory w)
    (base : ℕ) (dst rhs : Fin N → Expr)

local notation "stage" => (fun j ↦ publish (dst j) (rhs j))
local notation "packet" => (fun j : Fin N ↦ report ((base + Fin.val j : ℕ) : Word w) (Expr.eval pub state original (rhs j)))
local notation "kernel" => (fun v m rs ↦ HeaderPacket.Run L pub state v m rs 7 [[]])

variable (hw : 1 < 2^w) (data : levelStart L 0 ≤ base) (fit : base+N ≤ 2^w)
    (stable : ∀ m, Agree (Outside base N) m original → ∀ j : Fin N,
      (dst j).eval pub state m = ((base+j.val : ℕ) : Word w) ∧
      (rhs j).eval pub state m = (rhs j).eval pub state original)

include hw data fit stable in
private theorem run_list (js : List (Fin N)) (nd : js.Nodup) (mem : Memory w)
    (frame : Agree (Outside base N) mem original) :
    let rs := js.map packet
    SourceWalk kernel (js.map stage) mem rs ∧
      (∀ j ∈ js, after mem (eventLog rs) (base+j.val) = (rhs j).eval pub state original) ∧
      ∀ a, (∀ j ∈ js, a ≠ base+j.val) → after mem (eventLog rs) a = mem a := by
  induction js generalizing mem with
  | nil =>
    refine ⟨.done _,?_,fun _ _ ↦ rfl⟩
    intro j hj; cases hj
  | cons j js ih =>
    let addr : Word w := ((base+j.val : ℕ) : Word w)
    let x := (rhs j).eval pub state original
    let mid := writeMemory mem addr x
    have atAddr : addr.val = base+j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
    obtain ⟨dval,xval⟩ := stable mem frame j
    have hmin : levelStart L 0 ≤ ((dst j).eval pub state mem).val := by
      rw [dval]; change _ ≤ addr.val; rw [atAddr]; omega
    obtain ⟨call,update⟩ := one L pub state (dst j) (rhs j) mem hw hmin
    rw [dval,xval] at call update
    have midFrame : Agree (Outside base N) mid original := by
      intro a ha
      have neq : a ≠ base+j.val := by have := j.isLt; unfold Outside at ha; omega
      change (if a = addr.val then _ else _) = _
      rw [atAddr,ite_eq_right neq]
      exact frame _ ha
    obtain ⟨tail,read,keep⟩ := ih (List.nodup_cons.mp nd).2 mid midFrame
    have eq : after mem (eventLog ((j::js).map packet)) = after mid (eventLog (js.map packet)) := by
      exact (SourceWalk.after_append mem [packet j] (js.map packet)).trans
        (congrArg (fun m ↦ after m (eventLog (js.map packet))) update)
    have tail' : SourceWalk kernel (js.map stage) (after mem (eventLog [packet j])) (js.map packet) := by
      rw [update]; exact tail
    refine ⟨SourceWalk.next call tail',?_,?_⟩
    · intro k hk
      rw [eq]
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [keep _ (fun l hl e ↦ (List.nodup_cons.mp nd).1 (by
          rw [show k = l from Fin.ext (Nat.add_left_cancel e)]; exact hl))]
        simp [mid,writeMemory,atAddr,x]
      · exact read k hk
    · intro a ha
      rw [eq,keep _ (fun k hk ↦ ha k (List.mem_cons_of_mem _ hk))]
      simp [mid,writeMemory,atAddr,ha j (List.mem_cons_self ..)]

/-- A complete contiguous publication supplies a chronological native source
walk, the fourteen/four/one-word readback and the frame of every other cell. -/
structure Published : Prop where
  walk : SourceWalk kernel (List.ofFn stage) original (List.ofFn packet)
  stored (j : Fin N) : after original (eventLog (List.ofFn packet)) (base+j.val) =
    (rhs j).eval pub state original
  outside (a : ℕ) : Outside base N a → after original (eventLog (List.ofFn packet)) a = original a

include hw data fit stable in
theorem run : Published L pub state original base dst rhs := by
  obtain ⟨walk,read,keep⟩ := run_list L pub state original base dst rhs hw data fit stable
    (List.finRange N) (List.nodup_finRange _) original (fun _ _ ↦ rfl)
  have ofFn {α : Type} (f : Fin N → α) : (List.finRange N).map f = List.ofFn f := by
    apply List.ext_getElem <;> simp
  rw [ofFn stage,ofFn packet] at walk
  rw [ofFn packet] at read keep
  refine ⟨walk,fun j ↦ read j (List.mem_finRange _),fun a ha ↦ keep _ (fun j _ ↦ ?_)⟩
  have := j.isLt
  unfold Outside at ha
  omega

/-- Specialize the consecutive destinations to fields of the old level
header. Its physical pitch survives every publication. -/
theorem run_fields (L : Layout) (first step offset : ℕ) (pub : Fin 5 → Word w) (state : Word w)
    (original : Memory w) (rhs : Fin N → Expr) (entry : LevelFields.Entry L first pub state original)
    (hw : 1 < 2^w) (fit : levelStart L (first+step)+offset+N ≤ 2^w)
    (pitch : Outside (levelStart L (first+step)+offset) N (pub 1-1).val)
    (stable : ∀ m, Agree (Outside (levelStart L (first+step)+offset) N) m original →
      ∀ j, (rhs j).eval pub state m = (rhs j).eval pub state original) :
    Published L pub state original (levelStart L (first+step)+offset)
      (fun j ↦ LevelFields.address step (offset+j.val)) rhs := by
  apply run _ _ _ _ _ _ _ hw _ fit
  · intro m frame j
    have e : LevelFields.Entry L first pub state m := ⟨entry.pointer,(frame _ pitch).trans entry.pitch⟩
    refine ⟨?_, stable m frame j⟩
    rw [LevelFields.eval_address e]
    simp only [Nat.add_assoc]
  · unfold levelStart; omega

theorem Published.source (h : Published L pub state original base dst rhs) :
    SourceWalk (OneCall pub state) (List.ofFn stage) original (List.ofFn packet) := by
  have weaken {js : List BlockPlanner.Visit} {m : Memory w} {rs : List (Report w)}
      (walk : SourceWalk kernel js m rs) : SourceWalk (OneCall pub state) js m rs := by
    induction walk with
    | done => exact .done _
    | next head _ ih => exact .next ⟨7,head.execute⟩ ih
  exact weaken h.walk

/-- The chronological packets have the exact execution, progress and source
footprints required by the online scheduler. -/
theorem Published.packets (h : Published L pub state original base dst rhs) :
    ∃ ps : List (SourceWalk.Packet BlockPlanner.Visit w),
      ps.map SourceWalk.Packet.stage = List.ofFn stage ∧
      ps.flatMap SourceWalk.Packet.reports = List.ofFn packet ∧
      SourceWalk.Chronological kernel original ps := h.walk.packets

theorem packet_cost : RAMBuckets.cost Report.probes (List.ofFn packet) = 2*N := by
  generalize h : List.ofFn packet = rs
  have lens : rs.length = N := h ▸ List.length_ofFn
  have cap (r : Report w) (hr : r ∈ rs) : r.probes = 1 :=  by
    rw [← h,List.mem_ofFn] at hr
    obtain ⟨i,rfl⟩ := hr; rfl
  rw [← lens]
  clear h lens
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change 1+r.probes+RAMBuckets.cost Report.probes rs = _
    rw [cap r (List.mem_cons_self ..),ih (fun z hz ↦ cap z (List.mem_cons_of_mem _ hz)),List.length_cons]
    omega

end CompressorRecords.PublishedHeads

end VPVNP
end Computability
end OAI
