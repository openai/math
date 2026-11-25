import OAI.ThreeFlat.RAM.TickReadFields
import OAI.ThreeFlat.RAM.TickBitRelation

namespace OAI
/-! # Reading the four boundary vectors of a physical tick -/

namespace ThreeFlat.RAM.TickBoundaryFields

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Diagonal.ApproximateImage
open scoped Fin.CommRing

inductive Segment | oldAux | newAux | oldChunk | newChunk

def Segment.number : Segment → ℕ
  | .oldAux => 0 | .newAux => 1 | .oldChunk => 2 | .newChunk => 3

def Segment.select {α : Type*} (s : Segment) (oa na oc nc : α) : α :=
  match s with | .oldAux => oa | .newAux => na | .oldChunk => oc | .newChunk => nc

variable {d nt ns np a w S off : ℕ}

private def tail (s : Segment) (i : Fin a) : Fin (a+(a+(a+a))) :=
  match s with
  | .oldAux => i.castAdd (a+(a+a))
  | .newAux => Fin.natAdd a (i.castAdd (a+a))
  | .oldChunk => Fin.natAdd a (Fin.natAdd a (i.castAdd a))
  | .newChunk => Fin.natAdd a (Fin.natAdd a (Fin.natAdd a i))

private def pin (d nt ns np : ℕ) (s : Segment) (i : Fin a) : Fin (pinCount d nt ns np a) :=
  Fin.natAdd d (Fin.natAdd nt (Fin.natAdd ns (Fin.natAdd np (tail s i))))

def base (off d nt ns np a : ℕ) (s : Segment) := off+d+nt+ns+np+s.number*a

theorem boundary_bit (s : Segment) (i : Fin a)
    {D : Fin d → Bool} {params : Fin np → Bool} {oa na oc nc : Fin a → Bool}
    {team step : ℕ} {hdr : ℕ → Word w}
    (loc : TickReadFields.HasFields (nt:=nt) (ns:=ns) D params oa na oc nc team step hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) :
    initialMemory S hdr (base off d nt ns np a s+i.val) =
      TickBitRelation.bitWord w ((s.select oa na oc nc) i) := by
  let j := pin d nt ns np s i
  have read : initialMemory S hdr (off+j.val) = Fin.ofNat _ ((fields D (digits team nt)
      (digits step ns) params oa na oc nc j).toNat) := by
    have ht := j.isLt
    rw [initialMemory, ite_eq_left (show off+j.val < S by omega)]
    exact loc j
  have addr : off+j.val = base off d nt ns np a s+i.val := by
    cases s <;> simp [j,pin,tail,base,Segment.number,Fin.val_natAdd,Fin.val_castAdd] <;> omega
  rw [← addr,read]
  have val : fields D (digits team nt) (digits step ns) params oa na oc nc j = (s.select oa na oc nc) i := by
    cases s <;> simp only [j,pin,tail,fields,Segment.select,Fin.append_left,Fin.append_right]
  rw [val]
  cases (s.select oa na oc nc) i <;> rfl

/-- The physical range is word-addressable when its initial segment fits
the width, so the native indexed read agrees with the bit vector. -/
theorem boundary_bitAt (s : Segment) (i : Fin a)
    {D : Fin d → Bool} {params : Fin np → Bool} {oa na oc nc : Fin a → Bool}
    {team step : ℕ} {hdr : ℕ → Word w}
    (loc : TickReadFields.HasFields (nt:=nt) (ns:=ns) D params oa na oc nc team step hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) (fit : S ≤ 2^w) :
    ChunkRequests.bitAt (initialMemory S hdr) (base off d nt ns np a s : Word w) (i.val : Word w) =
      TickBitRelation.bitWord w ((s.select oa na oc nc) i) := by
  have hi := i.isLt
  have ht : base off d nt ns np a s+i.val < 2^w := by
    cases s <;> simp only [base,Segment.number,pinCount] at * <;> omega
  unfold ChunkRequests.bitAt
  rw [← Nat.cast_add, Fin.val_cast_of_lt ht]
  exact boundary_bit s i loc bound

end ThreeFlat.RAM.TickBoundaryFields

end OAI
