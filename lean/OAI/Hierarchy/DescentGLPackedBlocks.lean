import OAI.Hierarchy.DescentGLPackedSequence
import OAI.Hierarchy.DescentPackedRegroup

namespace OAI
/-! # Reinterpret the real packed GL output as adjacent post-reset census vectors -/
namespace Hierarchy.DescentGLPacked
open DescentSIMDLookup DescentGL DescentColonies Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {h l b H w : ℕ}

theorem chunk_count (h l : ℕ) : chunks (2^(h+l)) (2^l)=2^h := by
  have eq:=chunks_group (2^h) 1 (2^l) (by decide) (Nat.two_pow_pos _)
  simpa [pow_add,chunks,ThreeFlat.Routing.poolBatchCount] using eq

def atChunk (v : Fin H) (a : Bits h) : Row H (2^(h+l)) (2^l) :=
  (v,⟨((address h) a).val,by rw [chunk_count];exact ((address h) a).isLt⟩)

theorem ordinal_chunk (v : Fin H) (a : Bits h) :
    (row H (2^(h+l)) (2^l) (atChunk (l:=l) v a)).val=(ordinal (address h) v a).val := by
  change ((address h) a).val+chunks (2^(h+l)) (2^l)*v.val=((address h) a).val+2^h*v.val
  rw [chunk_count]

theorem packet_data (v : Fin H) (a : Bits h) (X : Fin H→Block (h+l)→Cell b) :
    data X (atChunk v a)=packet (address l) (fun i=>X v (address (h+l) (Fin.append a i))) := by
  apply (encode b (2^l)).symm.injective
  funext j
  simp only [data,packet,Equiv.symm_apply_apply]
  have pos : ((address h) a).val*2^l+j.val<2^(h+l) := by
    rw [pow_add]
    calc _<((address h) a).val*2^l+2^l:=Nat.add_lt_add_left j.isLt _
         _=(((address h) a).val+1)*2^l:=(Nat.succ_mul ..).symm
         _≤_:=Nat.mul_le_mul_right _ ((address h) a).isLt
  have inChunk : (atChunk (l:=l) v a).2.val * 2^l + j.val < 2^(h+l) := pos
  rw [dite_eq_left inChunk]
  apply congrArg (X v)
  apply Fin.ext
  change ((address h) a).val * 2^l + j.val = ((address (h+l)) _).val
  rw [address_append, Equiv.apply_symm_apply]

def Dense (base : ℕ) (X : Fin H→Block (h+l)→Cell b) (m : Memory w) : Prop :=
  ∀p : Row H (2^(h+l)) (2^l),m (base+(row H _ _ p).val)=((data X p).val:Word w)

theorem packed_iff (B : Bank) (X : Fin H→Block (h+l)→Cell b) (mem : Memory w) :
    Dense B.base X mem ↔ Reads B (address h) (address l) (fun v u z=>X v (address (h+l) (Fin.append u z))) mem := by
  constructor
  · intro pre v u
    simpa only [ordinal_chunk,packet_data] using pre (atChunk v u)
  · intro pre p
    let a:=(address h).symm ⟨p.2.val,by simpa only [chunk_count] using p.2.isLt⟩
    have eq : atChunk (l:=l) p.1 a=p := by
      refine Prod.ext ?_ ?_
      · rfl
      · apply Fin.ext
        simp [a, atChunk]
    rw [←eq,ordinal_chunk,packet_data]
    exact pre p.1 a

theorem dense_read (A : Layout) (L : DescentGL.Layout (h+l)) (X : Fin H→Block (h+l)→Cell b)
    (m : Memory w) (S : Hardware A H h l b w (DescentGLNielsen.schedule (h+l)).length)
    (old : Dense (A.bank 0).base X m) (real : Setup A b H 0
      ((DescentGLNielsen.schedule (h+l)).zip (DescentGLNielsen.controls L)) m) :
    let n:=(DescentGLNielsen.schedule (h+l)).length
    Dense (A.bank n).base (fun v z=>X v ((rearrange L).symm z)) (result (steps A H (2^h) 0 n) m) :=
  (packed_iff ..).2 (gl_read A L X m S ((packed_iff ..).1 old) real)

/-- Flattening a true remixed physical word and regrouping adjacent small cells
changes neither its numeric encoded bits nor its host address. -/
theorem regroup_after {J M r : ℕ} (hm : 0<M) (hr : 0<r) (base : ℕ) (mem : Memory w)
    (X : Fin H→Fin (J*r)→Cell b)
    (source : ∀p : Row H (J*r) (M*r),mem (base+(row H _ _ p).val)=((data X p).val:Word w)) :
    ∀p : Row H J M,mem (base+(row H J M p).val)=((data (groupedRows X) p).val:Word w) :=
  regroup_read hm hr base mem X source

end
end Hierarchy.DescentGLPacked

end OAI
