import OAI.Hierarchy.DescentNativeDonorROM
import OAI.Hierarchy.DescentPackedDonorEncoding
import OAI.Hierarchy.DescentRawCableRoles
import OAI.Hierarchy.DescentPackedRegroup

namespace OAI
/-! # One shared local lookup reports all eleven ordinary roles of each old donor -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

theorem old_report {loc a c : ℕ} (k g slots : ℕ) (d : Donor loc a c) (live : d.live=true) :
    report k g slots d 0=oldCable (loc:=loc) (a:=a) k g slots d.picked d.left d.right d.oldUnits := by
  simp [report,live]

theorem arm_report {loc a c : ℕ} (k g slots : ℕ) (d : Donor loc a c) (s : Fin 2) :
    report k g slots d (Fin.succ (Fin.castAdd 8 s))=if d.first then cell true true d.armUnits else 0 := by
  simp [report]

theorem supply_report {loc a c : ℕ} (k g slots : ℕ) (d : Donor loc a c) (s : Fin 8) :
    report k g slots d (Fin.succ (Fin.natAdd 2 s))=
      if d.first then motif (loc:=loc) (a:=a) k g slots d.layout d.anchors d.supplyUnits s else 0 := by
  simp [report]

attribute [local irreducible] Procedure.Exec in
/-- The output uses the same physical word as the flattened eleven-role
row needed by the ordinary sum, even at a partially populated last chunk. -/
theorem donor_emitted {k g slots loc a c H J M w : ℕ} (banks : Banks) (out : ℕ) (hm : 0<M)
    (fit : Fits banks (bundleBits loc a c) ((2+c)*11) M H J w out)
    (rows : Fin H→Fin J→Donor loc a c) (m : Memory w)
    (loaded : PinFrame (M:=M) banks (donorROM k g slots loc a c) (fun v j=>packDonor (rows v j)) m) :
    let raw (v : Fin H) (r : Fin (J*11)) := let t:=finProdFinEquiv.symm r;report k g slots (rows v t.1) t.2
    let last:=image out (H*chunks J M) (lookup banks) m
    (program banks out H J M w).Exec m last (4+44*(H*chunks J M)) ∧
      (∀p : Row H (J*11) (M*11),last (out+(row H (J*11) (M*11) p).val)=((data raw p).val:Word w)) ∧
      ∀x,x<out ∨ out+H*chunks J M≤x→last x=m x := by
  dsimp only
  let raw (v : Fin H) (r : Fin (J*11)):=report k g slots (rows v (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2
  refine ⟨?_,?_,?_⟩
  · have clock : 4+44*(H*chunks J M)=4+(H*chunks J M)*(2*(lookup banks).work+4) := by
      rw [lookup_work]
      omega
    rw [clock]
    exact @ProtocolRAM.scan_exec w out (H*chunks J M) (lookup banks) m
      (by simp [lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]) fit.output
  · intro p
    have span:=chunks_group J M 11 hm (by decide)
    let q : Row H J M := (p.1,Fin.cast span p.2)
    have index : (row H (J*11) (M*11) p).val=(row H J M q).val := by
      change p.2.val+chunks (J*11) (M*11)*p.1.val=p.2.val+chunks J M*p.1.val
      exact congrArg (fun n : ℕ => p.2.val+n*p.1.val) span
    rw [index]
    have read:=DescentSixParty.PackedCensus.col_read banks out fit _ _ m loaded q
    have eqn : (fun v j=>donorROM k g slots loc a c (packDonor (rows v j)))=groupedRows raw := by
      funext v j
      change encode (2+c) 11 (report k g slots (unpackDonor (packDonor (rows v j)))) =
        encode (2+c) 11 (fun s : Fin 11 => raw v (finProdFinEquiv (j,s)))
      rw [unpack_pack]
      apply congrArg (encode (2+c) 11)
      funext s
      exact congrArg (fun z : Fin J × Fin 11 => report k g slots (rows v z.1) z.2)
        (finProdFinEquiv.symm_apply_apply (j,s)).symm
    rw [eqn] at read
    exact read.trans (congrArg (fun n : ℕ=>(n:Word w)) (data_group (by decide : 0<11) raw q p rfl rfl).symm)
  · rintro x (h|h)
    · simp [image,fillSegment,Nat.not_le.mpr h]
    · simp [image,fillSegment,Nat.not_lt.mpr h]

theorem donor_publish {k g slots loc a c H J M w : ℕ} (banks : Banks) (out : ℕ) (hm : 0<M)
    (fit : Fits banks (bundleBits loc a c) ((2+c)*11) M H J w out)
    (rows : Fin H→Fin J→Donor loc a c) (m : Memory w)
    (loaded : PinFrame (M:=M) banks (donorROM k g slots loc a c) (fun v j=>packDonor (rows v j)) m) :
    let raw (v : Fin H) (r : Fin (J*11)) := let t:=finProdFinEquiv.symm r;report k g slots (rows v t.1) t.2
    ∃last,(program banks out H J M w).Exec m last (4+44*(H*chunks J M)) ∧
      (∀p : Row H (J*11) (M*11),last (out+(row H (J*11) (M*11) p).val)=((data raw p).val:Word w)) ∧
      ∀x,x<out ∨ out+H*chunks J M≤x→last x=m x := by
  exact ⟨_,donor_emitted banks out hm fit rows m loaded⟩

end
end Hierarchy.DescentRawCablePanel

end OAI
