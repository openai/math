import OAI.ThreeFlat.RAM.RawTickBuilder

namespace OAI
/-! # Logical word memory for on-demand raw trace records -/
namespace ThreeFlat.RAM.TraceRawOverlay
open Computability.VPVNP.BurstRAM
variable {F : Type*} {w p : ℕ} (N : BitNetwork F p) (code : FieldCode F w) (raw : ℕ)

/-- The read-only view used in the correctness proof of the virtual raw accessor. -/
def memory (m : Memory w) (a : ℕ) : Word w :=
  if h : raw≤a ∧ (a-raw)/11<N.cells then
    BitLayout.record N code ⟨_,h.2⟩ ⟨(a-raw)%11,Nat.mod_lt _ (by decide)⟩
  else m a

theorem loaded (m : Memory w) : RawTickBuilder.loaded N code raw (memory N code raw m) := by
  intro i j
  have parts : (raw+11*i.val+j.val-raw)/11=i.val ∧ (raw+11*i.val+j.val-raw)%11=j.val :=
    by have:=j.isLt;omega
  simp only [memory,parts.1,parts.2,i.isLt,and_true,show raw≤raw+11*i.val+j.val by omega,dite_eq_left]

theorem outside (m : Memory w) {a : ℕ} (h : a<raw ∨ raw+11*N.cells≤a) :
    memory N code raw m a=m a := by
  apply dite_eq_right
  omega

theorem congr_at {m m' : Memory w} {a : ℕ} (h : m a=m' a) :
    memory N code raw m a=memory N code raw m' a := by
  unfold memory
  split <;> simp_all

/-- A disjoint physical interval is visible unchanged through the virtual memory. -/
theorem span (m : Memory w) {start len : ℕ} (away : start+len≤raw ∨ raw+11*N.cells≤start)
    {i : ℕ} (hi : i<len) : memory N code raw m (start+i)=m (start+i) :=
  outside N code raw m (by omega)

end ThreeFlat.RAM.TraceRawOverlay

end OAI
