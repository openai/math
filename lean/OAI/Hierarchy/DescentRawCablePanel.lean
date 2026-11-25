import OAI.Hierarchy.DescentNativeDonorROM
import OAI.Hierarchy.DescentPackedDonorEncoding
import OAI.Hierarchy.DescentPackedTrimOwner
import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # Short ordinary-cable records before and after hub contraction -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentHostDirectory SiteDecode
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

@[simp] theorem same_pre {c : ℕ} (p q : Bool) (n : Cell c) : samePre (cell p q n)=p := by simp [samePre,cell]
@[simp] theorem same_post {c : ℕ} (p q : Bool) (n : Cell c) : samePost (cell p q n)=q := by simp [samePost,cell]
@[simp] theorem units_read {c : ℕ} (p q : Bool) (n : Cell c) : grains (cell p q n)=n.val := by simp [grains,cell]
@[simp] theorem cell_zero (c : ℕ) : cell false false (0:Cell c)=0 := by apply Fin.ext;rfl
@[simp] theorem score_zero (c : ℕ) : score (0:Cell (2+c))=0 := by
  rw [←cell_zero c,score,same_post]; rfl

variable {V : Type} [Fintype V] [DecidableEq V]
def rooted (k slots loc a : ℕ) (hub : V→Bool) (z : Key V) (host : Cell loc) :=
  endpoint loc a ((host,tag (hub z.1)),(localNumber k slots z:ℕ))

omit [DecidableEq V] in
theorem rooted_read (rank : V↪ℕ) (k g slots loc a c : ℕ) (hub : V→Bool) (s t : Key V)
    (sr : s∈keys k slots) (dr : t∈keys k slots) (ids : 2^(k+1)*slots≤2^a)
    (u v : Cell loc) (spatial : u=v ↔ s.1=t.1) (n : Cell c) :
    output k g slots loc a c (input loc a c ((rooted k slots loc a hub s u,rooted k slots loc a hub t v),n))=
      cell (decide (packedNumber rank k slots s=packedNumber rank k slots t))
        (decide (packedNumber rank k slots (mergeHub hub k g s)=packedNumber rank k slots (mergeHub hub k g t))) n := by
  have short {y : Key V} (hy : y∈keys k slots) : localNumber k slots y<2^a := by
    simpa [trim] using (trim_lt k g slots (fun _=>false) y hy).trans_le ids
  have before:=keep_iff rank k g slots (fun _=>false) s t sr dr
  simp only [mergeHub,Bool.false_eq_true,ite_false,trim] at before
  have after:=keep_iff rank k g slots hub s t sr dr
  have localEq : ((localNumber k slots s:ℕ):Cell a)=((localNumber k slots t:ℕ):Cell a) ↔
      localNumber k slots s=localNumber k slots t := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (short sr),Fin.val_cast_of_lt (short dr)]
  simp only [output,rooted,Equiv.symm_apply_apply,flag_tag,Fin.val_cast_of_lt (short sr),
    Fin.val_cast_of_lt (short dr),spatial,localEq,←before,←after]

/-- The packed ordinary status column uses one shared ROM over the complete
local record, for any number of host × chronological chunks. -/
theorem publish {k g slots loc a c H J M w : ℕ} (banks : Banks) (out : ℕ)
    (fit : Fits banks ((loc+1+a)+(loc+1+a)+c) (2+c) M H J w out)
    (wire : Fin H→Fin J→Cell ((loc+1+a)+(loc+1+a)+c)) (m : Memory w)
    (loaded : PinFrame (M:=M) banks (output k g slots loc a c) wire m) :
    ∃last,(DescentSIMDLookup.program banks out H J M w).Exec m last (4+44*(H*chunks J M)) ∧
      (∀p : Row H J M,last (out+(row H J M p).val)=
        ((data (fun v j=>output k g slots loc a c (wire v j)) p).val:Word w)) ∧
      ∀x,x<out ∨ out+H*chunks J M≤x→last x=m x := by
  let last:=image out (H*chunks J M) (lookup banks) m
  refine ⟨last,?_,DescentSixParty.PackedCensus.col_read _ _ fit _ _ m loaded,?_⟩
  · have run : (ProtocolRAM.scan w out (H*chunks J M) (lookup banks)).Exec m last
        (4+(H*chunks J M)*(2*(lookup banks).work+4)) :=
      ProtocolRAM.scan_exec out (H*chunks J M) (lookup banks) m
        (show (lookup banks).Fits w out from by simp [lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]) fit.output
    have ticks : 44*(H*chunks J M)=(H*chunks J M)*(2*(lookup banks).work+4) := by
      rw [lookup_work]
      exact Nat.mul_comm 44 (H*chunks J M)
    rw [ticks]
    exact @run
  · rintro x (h|h)
    · simp [last,image,fillSegment,Nat.not_le.mpr h]
    · simp [last,image,fillSegment,Nat.not_lt.mpr h]

end
end Hierarchy.DescentRawCablePanel

end OAI
