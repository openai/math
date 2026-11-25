import OAI.Hierarchy.DescentRotorScheduler
import OAI.Hierarchy.DescentPackedWords
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Canonical packet ROM coordinates for an actual integer bundle matrix -/

namespace Hierarchy.DescentRotor.Scheduler
open scoped BigOperators
variable {Y w L : ℕ}

theorem groups_integer (hw : 0<w) (n : ℕ) : groups w n = n ⌈/⌉ w := by
  refine eq_of_forall_ge_iff fun z => ?_
  rw [groups,Nat.ceil_le,div_le_iff₀ (by exact_mod_cast hw : 0<(w:ℝ)),ceilDiv_le_iff_le_mul hw,mul_comm w z]
  exact_mod_cast (Iff.rfl : n≤z*w ↔ n≤z*w)

abbrev NativePacket (w : ℕ) (a : Fin Y → Fin Y → ℕ) := Σ i : Fin Y, Σ j : Fin Y,Fin (a i j ⌈/⌉ w)
def packetCount (w : ℕ) (a : Fin Y → Fin Y → ℕ) := ∑i,∑j,a i j ⌈/⌉ w

/-- Prefix addresses first enumerate source, then destination, then the
contiguous packet serial in that matrix entry. -/
def nativeIDs (a : Fin Y → Fin Y → ℕ) : NativePacket w a ≃ Fin (packetCount w a) :=
  (Equiv.sigmaCongrRight (fun _=>finSigmaFinEquiv)).trans finSigmaFinEquiv

noncomputable def encoded (a : Fin Y → Fin Y → ℕ) (hw : 0<w) : Packet w a ≃ NativePacket w a :=
  Equiv.sigmaCongrRight (fun i=>Equiv.sigmaCongrRight (fun j=>finCongr (groups_integer hw (a i j))))

noncomputable def packetIDs (a : Fin Y → Fin Y → ℕ) (hw : 0<w) : Packet w a ≃ Fin (packetCount w a) :=
  (encoded a hw).trans (nativeIDs a)

def source (a : Fin Y → Fin Y → ℕ) (u : Fin (packetCount w a)) := ((nativeIDs a).symm u).1
def target (a : Fin Y → Fin Y → ℕ) (u : Fin (packetCount w a)) := ((nativeIDs a).symm u).2.1

@[simp] theorem source_id (a : Fin Y → Fin Y → ℕ) (hw : 0<w) (p : Packet w a) :
    source a (packetIDs a hw p)=p.1 := by simp [source,packetIDs,encoded]
@[simp] theorem target_id (a : Fin Y → Fin Y → ℕ) (hw : 0<w) (p : Packet w a) :
    target a (packetIDs a hw p)=p.2.1 :=
  congrArg (fun t : NativePacket w a => t.2.1) ((nativeIDs a).symm_apply_apply (encoded a hw p))

/-- Cache both endpoint IDs after decoding the single linear ordinal. -/
def endpointRows (a : Fin Y → Fin Y → ℕ) : Vector (Fin Y × Fin Y) (packetCount w a) :=
  Vector.ofFn fun u=>let p := (nativeIDs a).symm u;(p.1,p.2.1)

def matrixRun (w L : ℕ) (a : Fin Y → Fin Y → ℕ) : State (packetCount w a) Y L :=
  let rows := endpointRows a
  compile (fun u=>(rows.get u).1) (fun u=>(rows.get u).2) L

theorem matrixRun_eq (a : Fin Y → Fin Y → ℕ) :
    matrixRun w L a=compile (source (w:=w) a) (target a) L := by
  have row (i : Fin (packetCount w a)) : (endpointRows a).get i = (source a i, target a i) := by
    change (endpointRows a)[i.val] = _
    exact Vector.getElem_ofFn (f := fun u => (source a u, target a u)) i.isLt
  simp only [matrixRun, row]

/-- The original two row incidences of every real packet, computed by the
fixed address formulas, agree with the raster rows used by the scheduler. -/
theorem matrix_correct (a : Fin Y → Fin Y → ℕ) (hw : 0<w)
    (row : ∀v,(Finset.univ.filter (fun p : Packet w a=>p.1=v)).card≤L)
    (col : ∀v,(Finset.univ.filter (fun p : Packet w a=>p.2.1=v)).card≤L) :
    let r := matrixRun w L a
    (∀j, Function.Bijective (rotate r j)) ∧
    (∀p : Packet w a,rotate r (color r (packetIDs a hw p)) p.1=p.2.1) ∧
    ∀p q : Packet w a,color r (packetIDs a hw p)=color r (packetIDs a hw q) → p.1=q.1 → p=q := by
  classical
  let id := packetIDs a hw
  have measure (f : Fin (packetCount w a)→ Fin Y) (v : Fin Y) :
      (Finset.univ.filter fun n=>f n=v).card =
      (Finset.univ.filter fun p : Packet w a=>f (id p)=v).card := by
    rw [←Finset.card_map (f:=id.toEmbedding),Finset.map_filter]
    simp []
  have hr (v) : (Finset.univ.filter fun n=>source (w:=w) a n=v).card≤L := by
    rw [measure];simpa only [id,source_id] using row v
  have hc (v) : (Finset.univ.filter fun n=>target (w:=w) a n=v).card≤L := by
    rw [measure];simpa only [id,target_id] using col v
  have law := compile_correct (source (w:=w) a) (target a) hr hc
  dsimp only
  rw [matrixRun_eq]
  refine ⟨law.1,fun p=>by simpa only [source_id,target_id] using law.2.1 (packetIDs a hw p),?_⟩
  intro p q eq same
  exact id.injective (law.2.2 (id p) (id q) eq (by simpa only [id,source_id] using same))

theorem matrix_cost (a : Fin Y → Fin Y → ℕ) :
    (matrixRun w L a).work≤packetCount w a*((2*L+1)*(packetCount w a*3)+2*Y+3) := by
  rw [matrixRun_eq]
  exact compile_cost ..

/-- Padded packets also fit the actual combined per-row quota. -/
theorem packetCount_bound (a : Fin Y → Fin Y → ℕ) (hw : 0<w)
    (row : ∀v,(Finset.univ.filter (fun p : Packet w a=>p.1=v)).card≤L) :
    packetCount w a≤Y*L := by
  have each (v : Fin Y) : (∑j,a v j ⌈/⌉ w)≤L := by
    simpa only [packet_rows,groups_integer hw] using row v
  simpa [packetCount] using Finset.sum_le_sum (s:=Finset.univ) (fun v _=>each v)

end Hierarchy.DescentRotor.Scheduler

end OAI
