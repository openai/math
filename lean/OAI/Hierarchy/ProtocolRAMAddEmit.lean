import OAI.Hierarchy.ProtocolRAMFieldLoop
import OAI.Hierarchy.ProtocolRAMEmit
import OAI.Hierarchy.TaggedShorterCheapCPU
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Cheap-opcode emission from the padded accepted board -/

namespace Hierarchy.ProtocolRAMAddEmit
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMEmit
open scoped Fin.CommRing

variable {w n : ℕ}

/-- Each source row occupies eight words. The seven descriptor fields are consecutive. -/
def Packed (src : ℕ) (rows : Fin n → Row) (m : Memory w) : Prop :=
  ∀ i j, m (src+8*i.val+j.val) = ((rows i).field j:Word w)

private def lane (src dst n : ℕ) (f : Fin 3 → Fin 7) (j : Fin 3) (m : Memory w) :=
  ProtocolRAMFieldLoop.image (src+(f j).val) (dst+j.val) n m

private theorem retain (src dst : ℕ) (f : Fin 3 → Fin 7) (j : Fin 3) (rows : Fin n → Row)
    (m : Memory w) (packed : Packed src rows m) (apart : src+8*n≤ dst ∨ dst+3*n≤ src) :
    Packed src rows (lane src dst n f j m) := by
  intro i t
  apply Eq.trans (ProtocolRAMFieldLoop.image_frame _ _ _ _ _ ?_) (packed i t)
  intro k
  have := i.isLt
  have := k.isLt
  have := j.isLt
  have := t.isLt
  omega

private theorem hit (src dst : ℕ) (f : Fin 3 → Fin 7) (j : Fin 3) (rows : Fin n → Row)
    (m : Memory w) (packed : Packed src rows m) (i : Fin n) :
    lane src dst n f j m (dst+3*i.val+j.val) = ((rows i).field (f j):Word w) := by
  unfold lane
  rw [show dst+3*i.val+j.val=dst+j.val+3*i.val by omega,ProtocolRAMFieldLoop.image_read,
    show src+(f j).val+8*i.val=src+8*i.val+(f j).val by omega, packed]

private theorem miss (src dst : ℕ) (f : Fin 3 → Fin 7) (j t : Fin 3) (m : Memory w)
    (i : Fin n) (ne : j≠t) :
    lane src dst n f j m (dst+3*i.val+t.val) = m (dst+3*i.val+t.val) := by
  apply ProtocolRAMFieldLoop.image_frame
  intro k eq
  apply ne
  apply Fin.ext
  have := t.isLt
  have := j.isLt
  omega

def table (w src dst n : ℕ) (f : Fin 3 → Fin 7) : Procedure w :=
  let pass (j : Fin 3) := ProtocolRAMFieldLoop.procedure w (src+(f j).val) (dst+j.val) n
  ((pass 0).seq (pass 1)).seq (pass 2)

private theorem table_exec (src dst : ℕ) (f : Fin 3 → Fin 7) (rows : Fin n → Row)
    (m : Memory w) (packed : Packed src rows m)
    (srcFit : src+8*n<2^w) (dstFit : dst+3*n<2^w)
    (apart : src+8*n≤ dst ∨ dst+3*n≤ src) :
    (table w src dst n f).Exec m (fillSegment dst (3*n) (tripleWord rows f dst) m) (9+39*n) := by
  have run (j : Fin 3) (o : Memory w) :
      (ProtocolRAMFieldLoop.procedure w (src+(f j).val) (dst+j.val) n).Exec
        o (lane src dst n f j o) (3+13*n) := by
    refine Procedure.Spec.exec (ProtocolRAMFieldLoop.run (src+(f j).val) (dst+j.val) n (by omega) ?_ ?_ ?_) o trivial
    · intro i;have:=i.isLt;have:=(f j).isLt;omega
    · intro i;have:=i.isLt;have:=j.isLt;omega
    · intro i k;have:=i.isLt;have:=k.isLt;have:=j.isLt;have:=(f j).isLt;omega
  let m₀ := lane src dst n f 0 m
  let m₁ := lane src dst n f 1 m₀
  have pack₀ := retain src dst f 0 rows m packed apart
  have pack₁ := retain src dst f 1 rows m₀ pack₀ apart
  have eq : lane src dst n f 2 m₁ = fillSegment dst (3*n) (tripleWord rows f dst) m := by
    funext a
    by_cases inside : dst≤a ∧ a<dst+3*n
    · let i : Fin n := ⟨(a-dst)/3,by omega⟩
      let j : Fin 3 := ⟨(a-dst)%3,Nat.mod_lt _ (by decide)⟩
      have slot : a=dst+3*i.val+j.val := by dsimp [i,j];omega
      rw [slot,read_triple]
      have casesJ : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases casesJ with eqJ | eqJ | eqJ <;> rw [eqJ]
      · rw [miss _ _ _ 2 0 _ i (by decide)]
        change lane src dst n f 1 m₀ _ = _
        rw [miss _ _ _ 1 0 _ i (by decide)]
        exact hit _ _ f 0 rows m packed i
      · rw [miss _ _ _ 2 1 _ i (by decide)]
        exact hit _ _ f 1 rows m₀ pack₀ i
      · exact hit _ _ f 2 rows m₁ pack₁ i
    · have frame (j : Fin 3) (o : Memory w) : lane src dst n f j o a = o a := by
        apply ProtocolRAMFieldLoop.image_frame
        intro z eq
        have := z.isLt
        have := j.isLt
        omega
      unfold m₁ m₀
      rw [frame,frame,frame]
      simp [fillSegment,inside]
  rw [←eq,show 9+39*n=(3+13*n)+(3+13*n)+(3+13*n) by omega]
  unfold table
  intro P R K
  exact Procedure.Exec.then (Procedure.Exec.then (run 0 m) (run 1 m₀)) (run 2 m₁)

def emit (w src dst n : ℕ) : Procedure w :=
  ((table w src dst n endpointFields).seq (table w src (dst+3*n) n metricFields)).seq
    (table w src (dst+6*n) n gateFields)

private theorem packed_fill (src dst : ℕ) (rows : Fin n → Row) (m : Memory w) (v : ℕ → Word w)
    (packed : Packed src rows m) (apart : src+8*n≤ dst ∨ dst+3*n≤ src) :
    Packed src rows (fillSegment dst (3*n) v m) := by
  intro i j
  have := i.isLt
  have := j.isLt
  have away : ¬ (dst≤ src+8*i.val+j.val ∧ src+8*i.val+j.val<dst+3*n) := by omega
  simpa [fillSegment,away] using packed i j

theorem emit_exec (src dst : ℕ) (rows : Fin n → Row) (m : Memory w) (packed : Packed src rows m)
    (srcFit : src+8*n<2^w) (dstFit : dst+9*n<2^w) (apart : src+8*n≤ dst ∨ dst+9*n≤ src) :
    (emit w src dst n).Exec m (emitted dst rows m) (27+117*n) := by
  have a : (table w src dst n endpointFields).Exec m _ _ := table_exec src dst endpointFields rows m packed srcFit (by omega) (by omega)
  have h₀ := packed_fill src dst rows m (tripleWord rows endpointFields dst) packed (by omega)
  have b : (table w src (dst+3*n) n metricFields).Exec _ _ _ := table_exec src (dst+3*n) metricFields rows _ h₀ srcFit (by omega) (by omega)
  have h₁ := packed_fill src (dst+3*n) rows _ (tripleWord rows metricFields (dst+3*n)) h₀ (by omega)
  have c : (table w src (dst+6*n) n gateFields).Exec _ _ _ := table_exec src (dst+6*n) gateFields rows _ h₁ srcFit (by omega) (by omega)
  rw [show 27+117*n=(9+39*n)+(9+39*n)+(9+39*n) by omega]
  unfold emit emitted
  intro P R K
  exact Procedure.Exec.then (Procedure.Exec.then a b) c

theorem emit_size (w src dst n : ℕ) :
    (emit w src dst n).labels = 135 ∧ (emit w src dst n).registers=54 ∧ (emit w src dst n).slots=27 :=
  ⟨rfl,rfl,rfl⟩

theorem emit_cheap (w src dst n : ℕ) : ProtocolRAMFieldLoop.CheapCode (emit w src dst n) := by
  unfold emit table
  repeat' apply ProtocolRAMFieldLoop.cheap_seq
  all_goals exact ProtocolRAMFieldLoop.procedure_cheap _ _ _ _

theorem cheapCPU {P R K : ℕ} (instr : Instr w P R K) (h : ProtocolRAMFieldLoop.Cheap instr) :
    TaggedShorterCheapCPU.Cheap instr := by
  cases instr <;> simp_all [ProtocolRAMFieldLoop.Cheap,TaggedShorterCheapCPU.Cheap]

theorem installed_cheap {w src dst n P R K : ℕ} (M : Machine w P R K)
    (pc : Fin (emit w src dst n).labels ↪ Fin P) (reg : Fin (emit w src dst n).registers ↪ Fin R)
    (pub : Fin (emit w src dst n).slots → Fin K) (exit : Fin P)
    (installed : (emit w src dst n).block.Installed M pc reg pub exit) (i : Fin (emit w src dst n).labels) :
    TaggedShorterCheapCPU.Cheap (M.code (pc i)) := by
  rw [installed i]
  exact cheapCPU _ (emit_cheap w src dst n pc reg pub exit i)

end Hierarchy.ProtocolRAMAddEmit

end OAI
