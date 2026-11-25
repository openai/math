import OAI.ThreeFlat.Diagonal.InitialMetadataScan
import OAI.ThreeFlat.Diagonal.ShrinkDescriptorReadback

namespace OAI
/-! # Indexed results of the three sequential metadata arrays -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.DescriptorScan RAM.PhysicalPinsExpr
open CompressorPacking.Native.ShrinkStage.DescriptorSpan
open scoped Classical Fin.NatCast
noncomputable section
variable {W : ℕ} (A : Archive)
local notation "cur" => (A.control:Word W)
local notation "f" => A.seedWords

def initialScan (i : ℕ) (e : Formula 1) (m : Memory W) :=
  (Pipeline.scan (A.control : Word W) i (i+1) (closed e)).run m

def KeepsMetadata (m old : Memory W) := ∀a,A.metadataKeep a→m a=old a

theorem MetadataSpace.stable {m old : Memory W} (h : A.MetadataSpace W) (keep : A.KeepsMetadata m old)
    (H : Scans.Header cur old A.seed 63 f) : Scans.Header cur m A.seed 63 f := by
  refine ⟨?_,H.fit,?_⟩
  · rw [keep _ (by rw [Fin.val_cast_of_lt h.controlRoom];exact h.control)];exact H.pointer
  · intro i hi
    rw [keep _ (.inl (by have:=h.header;omega))]
    exact H.values i hi

def StableAt (old : Memory W) (e : Formula 1) (a : ℕ) (v : Word W) : Prop :=
  ∀m,A.KeepsMetadata m old → e.value (fun _=>0) m (fun _=>(a:Word W))=v

structure ScanAt (e : Formula 1) (i : ℕ) (old out : Memory W) : Prop where
  frame : agreesOutside (f i) (f i+f (i+1)) out old
  words : ∀a,f i≤a → a<f i+f (i+1) → ∀v,A.StableAt old e a v → out a=v

theorem single_scan {m : Memory W} (sp : A.MetadataSpace W) (H : Scans.Header cur m A.seed 63 f) (i : ℕ)
    (small : i+1≤63) (window : A.initialRecords≤f i ∧ f i+f (i+1)≤A.metadataEnd) (e : Formula 1) :
    A.ScanAt e i m (A.initialScan i e m) := by
  let g:=fun a z=>(closed (w:=W) e).eval Fin.elim0 z (fun _=>a)
  let lo:=headerWord m cur i
  let len:=(headerWord m cur (i+1)).val
  have a : lo.val=f i:=H.get i (by omega)
  have b : len=f (i+1):=H.get (i+1) small
  have cap : lo.val+len<2^W := by rw [a,b];exact window.2.trans_lt sp.endFit
  change ScanAt A e i m (CompressorPacking.Native.sweep g len lo m)
  refine ⟨by simpa only [a,b] using sweep_outside g lo len m cap,?_⟩
  intro j hj hi v eqv
  have past : lo.val≤j := by rwa [a]
  have fut : j<lo.val+len := by rwa [a,b]
  rw [sweep_word g len lo m cap j past fut]
  change (closed e).eval _ _ _=_
  rw [eval_closed]
  apply eqv
  intro z hz
  apply beforeAddress_frame
  change z<A.initialRecords ∨ A.metadataEnd≤z at hz
  rcases hz with h|h
  · exact .inl (h.trans_le (window.1.trans a.ge))
  · exact .inr (fut.le.trans ((by rw [a,b];exact window.2 : lo.val+len≤A.metadataEnd).trans h))

theorem ScanAt.keep {m out : Memory W} {i : ℕ} {e : Formula 1} (h : A.ScanAt e i m out)
    (window : A.initialRecords≤f i ∧ f i+f (i+1)≤A.metadataEnd) : A.KeepsMetadata out m :=
  fun j z=>h.frame j (z.imp (fun l=>l.trans_le window.1) (fun r=>window.2.trans r))

def RawMetadataRows (m out : Memory W) : Prop :=
  (∀ i,f 7≤ i → i<f 9 → ∀ v,A.StableAt m A.initialKernel i v → out i=v) ∧
  (∀ i,f 9≤ i → i<f 11 → ∀ v,A.StableAt m A.initialHalfHeader i v → out i=v) ∧
    ∀ i,f 11≤ i → i<A.metadataEnd → ∀ v,A.StableAt m A.initialHalf i v → out i=v

private theorem three_scan_memory (control : Word W) (m : Memory W)
    (kernel halfHeader half : DescriptorExpr.Term W 0 1) :
    (Scans.pipeline control (.next (.one ⟨7,8,kernel⟩)
      (.next (.one ⟨9,10,halfHeader⟩) (.one ⟨11,12,half⟩)))).run m =
    (Pipeline.scan control 11 12 half).run ((Pipeline.scan control 9 10 halfHeader).run
      ((Pipeline.scan control 7 8 kernel).run m)) := rfl

private theorem rows_of_scans {m m1 m2 out : Memory W}
    (k : A.ScanAt A.initialKernel 7 m m1) (h : A.ScanAt A.initialHalfHeader 9 m1 m2)
    (finish : A.ScanAt A.initialHalf 11 m2 out)
    (kf : A.KeepsMetadata m1 m) (hf : A.KeepsMetadata m2 m1)
    (h1 : f 7+f 8=f 9) (h2 : f 9+f 10=f 11) (h3 : f 11+f 12=A.metadataEnd) :
    A.RawMetadataRows m out := by
  refine ⟨?_,?_,?_⟩
  · intro i lo hi v eqv
    exact (finish.frame i (.inl (by omega))).trans ((h.frame i (.inl hi)).trans
      (k.words i lo (by rwa [h1]) v eqv))
  · intro i lo hi v eqv
    exact (finish.frame i (.inl hi)).trans (h.words i lo (by rwa [h2]) v (fun z live=>eqv z
      (fun a ha=>(live a ha).trans (kf a ha))))
  · intro i lo hi v eqv
    exact finish.words i lo (by rwa [h3]) v (fun z live=>eqv z
      (fun a ha=>(live a ha).trans ((hf a ha).trans (kf a ha))))

theorem raw_metadata_rows (m : Memory W) (sp : A.MetadataSpace W) (H : Scans.Header cur m A.seed 63 f) :
    A.RawMetadataRows m (A.metadataMemory m) := by
  have h0 : f 7=A.initialRecords:=rfl
  have h1 : f 7+f 8=f 9:=rfl
  have h2 : f 9+f 10=f 11:=by change _+5*_+2*_= _+7*_;omega
  have h3 : f 11+f 12=A.metadataEnd:=by
    change A.initialRecords+7*A.initialSites+8*A.initialDegree*A.initialSites =
      A.initialRecords+(7+8*A.initialDegree)*A.initialSites
    rw [Nat.add_mul,Nat.add_assoc]
  have bounds0 : A.initialRecords≤f 7 ∧ f 7+f 8≤A.metadataEnd:=by omega
  have bounds1 : A.initialRecords≤f 9 ∧ f 9+f 10≤A.metadataEnd:=by omega
  have bounds2 : A.initialRecords≤f 11 ∧ f 11+f 12≤A.metadataEnd:=by omega
  let m1:=A.initialScan 7 A.initialKernel m
  let m2:=A.initialScan 9 A.initialHalfHeader m1
  let out:=A.initialScan 11 A.initialHalf m2
  have k : A.ScanAt A.initialKernel 7 m m1 := A.single_scan sp H 7 (by decide) bounds0 A.initialKernel
  have kf:=ScanAt.keep A k bounds0
  have h : A.ScanAt A.initialHalfHeader 9 m1 m2 := A.single_scan sp (MetadataSpace.stable A sp kf H) 9 (by decide) bounds1 A.initialHalfHeader
  have hf:=ScanAt.keep A h bounds1
  have finish : A.ScanAt A.initialHalf 11 m2 out := A.single_scan sp (MetadataSpace.stable A sp hf (MetadataSpace.stable A sp kf H)) 11
    (by decide) bounds2 A.initialHalf
  have memory : A.metadataMemory m = out :=
    three_scan_memory (A.control : Word W) m (closed A.initialKernel)
      (closed A.initialHalfHeader) (closed A.initialHalf)
  rw [memory]
  exact rows_of_scans A k h finish kf hf h1 h2 h3


end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
