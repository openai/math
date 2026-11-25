import OAI.Hierarchy.DescentLaneProgram

namespace OAI
/-! # Consecutive complete payload bundles covering each strided rotor operand -/

namespace Hierarchy.DescentLaneGates.Lane
open DescentKernelHistory
variable {A : Type} {p : ℕ} {width : A→ℕ} (l : Lane p width)
variable (units : A→ℕ) (multiple : ∀a,width a=units a*p) (hp : 0<p)

def bundleStart := l.start/p
def residue := l.start%p
def count := min (l.stride+1) (units l.port-l.bundleStart)

theorem count_le : l.count units≤l.stride+1 := min_le_left _ _

include multiple hp in
theorem start_lt : l.bundleStart<units l.port := by
  apply (Nat.div_lt_iff_lt_mul hp).2
  simpa [multiple] using l.fits ⟨0,hp⟩

def index (d : Fin p) := (l.residue+l.stride*d.val)/p
def offset (d : Fin p) : Fin p := ⟨(l.residue+l.stride*d.val)%p,Nat.mod_lt _ hp⟩

include hp in
theorem index_eq (d : Fin p) : l.bundleStart+l.index d=(l.start+l.stride*d.val)/p := by
  have decomp : l.start=l.residue+l.bundleStart*p := (Nat.mod_add_div' ..).symm
  conv_rhs=>rw [decomp]
  rw [show l.residue+l.bundleStart*p+l.stride*d.val=l.residue+l.stride*d.val+l.bundleStart*p by omega,
    Nat.add_mul_div_right _ _ hp]
  simp [index,Nat.add_comm]

include multiple hp in
theorem index_lt (d : Fin p) : l.index d<l.count units := by
  apply lt_min
  · apply (Nat.div_lt_iff_lt_mul hp).2
    have left : l.residue<p := Nat.mod_lt l.start hp
    have right := Nat.mul_le_mul_left l.stride (Nat.le_of_lt d.isLt)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · have occupy : (l.start+l.stride*d.val)/p<units l.port :=
      (Nat.div_lt_iff_lt_mul hp).2 ((multiple l.port) ▸ l.fits d)
    rw [←l.index_eq hp d] at occupy
    omega

include multiple hp in
def block (j : Fin (l.count units)) : Fin (units l.port) :=
  ⟨l.bundleStart+j.val,by
    have hj : j.val<units l.port-l.bundleStart := j.isLt.trans_le (min_le_right _ _)
    have := l.start_lt units multiple hp
    omega⟩

/-- Only the local residue and stride are needed by the immutable decoder.
The physical address of each supplied argument is a complete aligned word. -/
def reconstruct (args : Fin (l.count units)→Word p) : Word p :=
  fun d=>args ⟨l.index d,l.index_lt units multiple hp d⟩ (l.offset hp d)

def blockBit (j : Fin (l.count units)) (d : Fin p) : BitRef width :=
  ⟨l.port,(l.block units multiple hp j).val*p+d.val,by
    rw [multiple]
    calc
      _ < (l.block units multiple hp j).val*p+p := Nat.add_lt_add_left d.isLt _
      _ = ((l.block units multiple hp j).val+1)*p := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (l.block units multiple hp j).isLt⟩

theorem reconstruct_read (x : BitRef width→Bool) :
    l.reconstruct units multiple hp (fun j d=>x (l.blockBit units multiple hp j d))=l.word x := by
  funext d
  apply congrArg x
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Fin.ext
  change (l.bundleStart+l.index d)*p+(l.residue+l.stride*d.val)%p=l.start+l.stride*d.val
  have h := Nat.mod_add_div' (l.residue+l.stride*d.val) p
  have h₀ := Nat.mod_add_div' l.start p
  unfold index residue bundleStart
  unfold residue at h
  rw [Nat.add_mul]
  omega

end Hierarchy.DescentLaneGates.Lane

end OAI
