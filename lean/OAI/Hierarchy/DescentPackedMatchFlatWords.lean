import OAI.Hierarchy.DescentPackedMatchFinal
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Reusing the all-key descriptor words at their original addresses -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w K H G M r D p d : ℕ}

def flat {s : Shape} (v : Fin K → Fin H → Fin G → Inputs s) (kh : Fin (K*H)) :=
  v (finProdFinEquiv.symm kh).1 (finProdFinEquiv.symm kh).2

theorem same_address (base : ℕ) (key : Fin K) (h : Fin H) (c : Fin (chunks G M)) :
    base+(row (K*H) G M (finProdFinEquiv (key,h),c)).val=
      ptr base H G M key.val+(row H G M (h,c)).val := by
  change base+(c.val+chunks G M*(h.val+H*key.val))=
    base+key.val*(H*chunks G M)+(c.val+chunks G M*h.val)
  ring

theorem flat_data {s : Shape} (x : Fin K → Fin H → Fin G → Inputs s)
    (key : Fin K) (h : Fin H) (c : Fin (chunks G M)) :
    data (fun v j=>encodeInput (flat x v j)) (finProdFinEquiv (key,h),c)=
      data (fun v j=>encodeInput (x key v j)) (h,c) := by
  simp only [data,flat,Equiv.symm_apply_apply]

theorem flat_read {s : Shape} (base : ℕ) (x : Fin K → Fin H → Fin G → Inputs s) (m : Memory w)
    (words : ∀key : Fin K,∀i : Row H G M,m (ptr base H G M key.val+(row H G M i).val)=
      ((data (fun h g=>encodeInput (x key h g)) i).val:Word w)) :
    ∀a : Row (K*H) G M,m (base+(row (K*H) G M a).val)=
      ((data (fun h g=>encodeInput (flat x h g)) a).val:Word w) := by
  rintro ⟨kh,c⟩
  obtain ⟨⟨k,h⟩,rfl⟩:=finProdFinEquiv.surjective kh
  rw [same_address,flat_data]
  exact words k (h,c)

def descriptorInputs (s : Shape) (B : ℕ) (u : Fin H→Fin G→Panel r D p d)
    (key : Fin K) (h : Fin H) (g : Fin G) := inputs s B key.val (u h g) fun _=>0

theorem all_flat (tables : Fin (fields r D p)→DescentPackedZip.Tables) (field : Fin (fields r D p)→Expr)
    (base : ℕ) (s : Shape) (B : ℕ) (dict : Fin K→Bank) (mask : Bank) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=d) (M:=M) tables field base)
    (static : ∀i,DescentPackedZip.Static (tables i) (setField (d:=d) i) M m)
    (source : ∀i,DescentPackedZip.Source (field i) (fun h g=>terrain u h g i) M m)
    (df : ∀key,(dict key).Fits w base) (mf : mask.Fits w base)
    (bits : ∀key,(dict key).bits=(d*fields r D p)*M) (span : H*chunks G M≤ mask.size)
    (wide : base+K*(H*chunks G M)<2^w) (size : s.inputBits*M≤w)
    (fixed : ∀key : Fin K,∀i : Cell ((d*fields r D p)*M),m ((dict key).base+i.val)=
      ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key.val) i).val:Word w))
    (masks : ∀t : Row H G M,m (mask.base+(row H G M t).val)=(maskWord s.inputBits M G t.2.val:Word w)) :
    let ps:=passes tables field dict mask base H G M
    let o:=ProtocolRAM.result ps m
    (all w tables field dict mask base H G M).Exec m o (clock ps) ∧
    (∀t : Row (K*H) G M,o (base+(row (K*H) G M t).val)=
      ((data (fun h g=>encodeInput (flat (descriptorInputs (K:=K) s B u) h g)) t).val:Word w)) ∧
    (∀a<base,o a=m a) ∧ CheapCode (all w tables field dict mask base H G M) := by
  have witness:=all_run tables field base s B dict mask u m bounds static source df mf bits span wide size fixed masks
  exact ⟨witness.1,flat_read base (descriptorInputs (K:=K) s B u) _
    (all_words tables field base s B dict mask u m bounds static source df mf bits span wide size fixed masks),
    witness.2.2⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather

end OAI
