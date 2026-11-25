import OAI.Hierarchy.DescentHostCountMask
import OAI.Hierarchy.DescentActorDirectoryFlags
import OAI.Hierarchy.DescentActorCompactRAM
import OAI.Hierarchy.DescentResetActorRaster

namespace OAI
/-! # Compressing the reset actor directory using its actual high-window flags -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
open DescentSIMDLookup DescentActorRaster DescentDenseHostOrder Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "pool" => DescentDenseHostOrder.roster Z.graph (Z.k-T.commonDepth) Ht
variable {H : ℕ} (vertex : Z.V↪Fin H)

def shapeOrder : ↥pool ≃ Fin (pool).card :=
  Equiv.ofBijective (localRank Z.graph (Z.k-T.commonDepth) Ht)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(localRank Z.graph (Z.k-T.commonDepth) Ht).injective,by simp⟩)

def rackAt {V : Type} (vertex : V ↪ Fin H) (j : Fin H) : Option V :=
  if h : ∃ v, vertex v = j then some h.choose else none

theorem rackAt_known {V : Type} (vertex : V ↪ Fin H) (v : V) :
    rackAt vertex (vertex v) = some v := by
  let h : ∃ u, vertex u = vertex v := ⟨v, rfl⟩
  rw [rackAt, dite_eq_left h]
  exact congrArg some (vertex.injective h.choose_spec)

theorem rackAt_some {V : Type} (vertex : V ↪ Fin H) {j : Fin H} {v : V}
    (hit : rackAt vertex j = some v) : vertex v = j := by
  unfold rackAt at hit
  split at hit
  next h => exact (Option.some.inj hit) ▸ h.choose_spec
  next => simp at hit

def sparseActor (j : Fin (H*(pool).card)) (hi : DescentColonies.Block T.commonDepth) : Cell 1 :=
  let z:=finProdFinEquiv.symm j
  (rackAt vertex z.1).elim 0 fun v=>if emits Z T (recover Z.graph v ((shapeOrder Z T).symm z.2).val) hi then 1 else 0

theorem sparse_known (q : ↥(commonNames Z T)) (hi : DescentColonies.Block T.commonDepth) :
    sparseActor Z T vertex (rawHostRank Z T vertex q) hi=if emits Z T q.val hi then 1 else 0 := by
  have decoded : finProdFinEquiv.symm (rawHostRank Z T vertex q) = hostFields Z T vertex q :=
    finProdFinEquiv.symm_apply_apply (hostFields Z T vertex q)
  rw [sparseActor, decoded]
  change (rackAt vertex (vertex (position Z.graph q.val))).elim 0
    (fun v => if emits Z T (recover Z.graph v
      (((shapeOrder Z T).symm ((shapeOrder Z T) (localShape Z T q))).val)) hi then (1 : Cell 1) else 0) = _
  rw [rackAt_known, Equiv.symm_apply_apply]
  change (if emits Z T (recover Z.graph (position Z.graph q.val)
    (DescentDenseHostOrder.shape Z.graph q.val)) hi then (1 : Cell 1) else 0) = _
  rw [recover_shape]

theorem rack_flag (j : Fin (H*(pool).card)) :
    (∃hi,sparseActor Z T vertex j hi≠0) ↔ ∃q : ↥(commonNames Z T),rawHostRank Z T vertex q=j := by
  classical
  constructor
  · rintro ⟨hi,lit⟩
    let z:=finProdFinEquiv.symm j
    let shape:=((shapeOrder Z T).symm z.2).val
    change (rackAt vertex z.1).elim 0
      (fun v => if emits Z T (recover Z.graph v shape) hi then (1 : Cell 1) else 0) ≠ 0 at lit
    cases atRack:rackAt vertex z.1 with
    | none=>simp [atRack] at lit
    | some v=>
      let q:=recover Z.graph v shape
      have live : emits Z T q hi:=by
        by_contra miss
        apply lit
        rw [atRack]
        exact ite_eq_right miss
      obtain ⟨u,hu,hx⟩:=(reset_occupied Z T q hi).mpr live
      let named : ↥(commonNames Z T):=placed Z T u
      have hv : named.val=q:=hu
      refine ⟨named,finProdFinEquiv.eq_symm_apply.symm.mpr ?_⟩
      apply Prod.ext
      · change vertex (position Z.graph named.val)=z.1
        rw [hv]
        have pos : ∀ key, position Z.graph (recover Z.graph v key) = v := by
          intro key
          cases key <;> rfl
        exact (congrArg vertex (pos shape)).trans (rackAt_some vertex atRack)
      · change shapeOrder Z T (localShape Z T named)=z.2
        apply (shapeOrder Z T).eq_symm_apply.symm.mpr
        apply Subtype.ext
        change DescentDenseHostOrder.shape Z.graph named.val=shape
        rw [hv]
        have localKey : ∀ key, DescentDenseHostOrder.shape Z.graph (recover Z.graph v key) = key := by
          intro key
          rcases key with ⟨s,⟨⟨⟩,term⟩⟩|⟨s,⟨⟨⟩,i⟩,cell⟩|⟨s,⟨⟨⟩,z⟩,ps⟩ <;> rfl
        exact localKey shape
  · rintro ⟨q,rfl⟩
    obtain ⟨u,_,atQ⟩:=Finset.mem_image.mp q.property
    have issued : emits Z T q.val (blockId Z T u):=(reset_occupied Z T _ _).mp ⟨u,atQ,rfl⟩
    exact ⟨blockId Z T u, by simp [sparse_known, issued]⟩

theorem prefix_input {w lanes : ℕ} (hm : 0<lanes) (word : lanes≤w) (j : Fin (H*(pool).card)) :
    (if ∃u : Fin (chunks (2^T.commonDepth) lanes),
      ((data (sparseActor Z T vertex) (j,u)).val:Word w)≠0 then (1:Word w) else 0)=
    (DescentEdgeTapePrefix.row (fun _ : ↥(commonNames Z T)=>1) (fun x=>(rawHostRank Z T vertex x).val) j.val:Word w) := by
  have present_iff := (Flags.chunks_present (sparseActor Z T vertex) j hm word).trans
    (rack_flag Z T vertex j)
  by_cases hit : ∃q : ↥(commonNames Z T),rawHostRank Z T vertex q=j
  · rw [ite_eq_left (present_iff.mpr hit)]
    rcases hit with ⟨q,rfl⟩
    have injective : Function.Injective (fun x => (rawHostRank Z T vertex x).val) :=
      Fin.val_injective.comp (rawHostRank Z T vertex).injective
    simp only [DescentEdgeTapePrefix.row_present _ _ injective q, Nat.cast_one]
  · rw [ite_eq_right (fun h => hit (present_iff.mp h))]
    simp only [DescentEdgeTapePrefix.row_absent _ _ _ (fun q eqn=>hit ⟨q,Fin.ext eqn⟩),
      Nat.cast_zero]

local notation "slots" => H * Finset.card (DescentDenseHostOrder.roster Z.graph (Z.k - T.commonDepth) Ht)
local notation "sparse" => rawHostRank Z T vertex

include vertex in
theorem denseFits : Fintype.card ↥(commonNames Z T) ≤ slots:=by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (rawHostRank Z T vertex) (rawHostRank Z T vertex).injective

def paddedDense := (denseHostRank Z T vertex).trans (Fin.castLEEmb (denseFits Z T vertex))

/-- One physical pass combines each raw rack's packets into its flag. The real
prefix is then inverted, leaving a public dense ordinal with its true sparse
source address. No edge incidence participates in any of the three passes. -/
theorem actor_directory_full {w M : ℕ} (hm : 0<M) (wide : M≤w)
    (roots src flags ranks : Bank) (scratch vals dest : ℕ) (atRow : Fin slots→ℕ) (mem : Memory w)
    (rootFit : roots.Fits w flags.base) (srcFit : src.Fits w flags.base)
    (nr : slots≤roots.size) (span : ∀j,atRow j+chunks (2^T.commonDepth) M ≤ src.size)
    (root : ∀j,mem (roots.base+j.val)=(atRow j:Word w))
    (words : ∀j (b : Fin (chunks (2^T.commonDepth) M)),mem (src.base+(atRow j+b.val))=
      ((data (sparseActor Z T vertex) (j,b)).val:Word w))
    (flagFit : flags.Fits w scratch) (rankFit : ranks.Fits w scratch)
    (nf : slots≤flags.size) (nd : slots≤ranks.size)
    (flagEnd : flags.base+slots≤ranks.base) (rankEnd : ranks.base+slots+1 ≤ scratch)
    (middle : scratch+slots≤vals) (last : vals+slots≤dest)
    (room : dest+2*slots<2^w) (one : 1<2^w) (lanes : chunks (2^T.commonDepth) M≤2^w) :
    let nChunk:=chunks (2^T.commonDepth) M
    let cost:=4+slots*(2*(Flags.poll roots src nChunk).work+4)
    let invert:=Inverse.program w scratch vals dest slots flags ranks
    let p:=((Flags.emit roots src flags.base slots nChunk w).seq
      (ProtocolRAMEndpointPrefix.exclusive w flags.base ranks.base slots)).seq invert
    ∃out,p.Exec mem out ((cost+(10+(3+12*slots)))+
        ProtocolRAMGeneratedWrite.work slots (Inverse.address flags ranks dest slots) .row) ∧
      (∀x : ↥(commonNames Z T),out (dest+(denseHostRank Z T vertex x).val)=((sparse x).val:Word w)) ∧
      out (ranks.base+slots)=(Fintype.card ↥(commonNames Z T):Word w) ∧ (∀a<flags.base,out a=mem a) ∧
      (∀x : ↥(commonNames Z T),out (ranks.base+(sparse x).val)=((denseHostRank Z T vertex x).val:Word w)) ∧
      (∀j : Fin slots,out (flags.base+j.val)=if ∃x:↥(commonNames Z T),sparse x=j then 1 else 0) := by
  let bits (j : Fin slots) (b : Fin (chunks (2^T.commonDepth) M)) :=
    ((data (sparseActor Z T vertex) (j,b)).val:Word w)
  obtain ⟨issued,known,early⟩:=Flags.issue (N := slots) (G := 2^T.commonDepth) (M := M) roots src atRow bits mem flags.base rootFit srcFit nr span
    root words one lanes (by omega)
  let mid:=ProtocolRAM.image flags.base slots (Flags.poll roots src (chunks (2^T.commonDepth) M)) mem
  have receipt (j : Fin slots) : mid (flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : ↥(commonNames Z T)=>1) (fun x=>(sparse x).val) j.val:Word w):=
    (known j).trans (prefix_input Z T vertex hm wide j)
  obtain ⟨ordered,atDense⟩:=hostTape_native Z T vertex mid flagEnd (by omega) (fun j h=>receipt ⟨j,h⟩)
  let pref:=ProtocolRAMEndpointPrefix.image ranks.base
    (DescentEdgeTapePrefix.before (fun _ : ↥(commonNames Z T)=>1) (fun x=>(sparse x).val)) mid slots
  have flags_kept (j : Fin slots) : pref (flags.base+j.val)=if ∃x:↥(commonNames Z T),sparse x=j then 1 else 0:=by
    have bound := j.isLt
    rw [show pref (flags.base+j.val)=mid (flags.base+j.val) from
      ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (Or.inl (by omega))]
    have present_iff := (Flags.chunks_present (sparseActor Z T vertex) j hm wide).trans
      (rack_flag Z T vertex j)
    by_cases hit : ∃ x : ↥(commonNames Z T), sparse x = j
    · rw [ite_eq_left hit]
      exact (known j).trans (ite_eq_left (present_iff.mpr hit))
    · rw [ite_eq_right hit]
      exact (known j).trans (ite_eq_right (fun h => hit (present_iff.mp h)))
  obtain ⟨inverted,read,unchanged,_⟩:=Inverse.run sparse (paddedDense Z T vertex) flags ranks scratch vals dest pref
    flagFit rankFit nf nd middle last room one flags_kept atDense
  let emit := Flags.emit roots src flags.base slots (chunks (2^T.commonDepth) M) w
  let scan := ProtocolRAMEndpointPrefix.exclusive w flags.base ranks.base slots
  let invert := Inverse.program w scratch vals dest slots flags ranks
  let out := Inverse.image sparse (paddedDense Z T vertex) flags ranks scratch vals dest pref
  refine ⟨out, ?_, read, ?_, ?_, ?_, ?_⟩
  · intro labels regs keys machine
    exact PhysicalProcedure.Procedure.Exec.then (A := emit.seq scan) (B := invert) (a := mem)
      (b := pref) (c := out) (PhysicalProcedure.Procedure.Exec.then (A := emit) (B := scan)
        (a := mem) (b := mid) (c := pref) issued ordered) inverted machine
  · exact (unchanged _ (Or.inl (by omega))).trans (hostTape_count Z T vertex mid)
  · intro a ha
    calc
      out a = pref a := unchanged a (Or.inl (by omega))
      _ = mid a := ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (Or.inl (by omega))
      _ = mem a := early a (Or.inl ha)
  · intro x
    have bound := (sparse x).isLt
    exact (unchanged _ (Or.inl (by omega))).trans (atDense x)
  · intro j
    have bound := j.isLt
    exact (unchanged _ (Or.inl (by omega))).trans (flags_kept j)

theorem actor_directory {w M : ℕ} (hm : 0<M) (wide : M≤w)
    (roots src flags ranks : Bank) (scratch vals dest : ℕ) (atRow : Fin slots→ℕ) (mem : Memory w)
    (rootFit : roots.Fits w flags.base) (srcFit : src.Fits w flags.base)
    (nr : slots≤roots.size) (span : ∀j,atRow j+chunks (2^T.commonDepth) M ≤ src.size)
    (root : ∀j,mem (roots.base+j.val)=(atRow j:Word w))
    (words : ∀j (b : Fin (chunks (2^T.commonDepth) M)),mem (src.base+(atRow j+b.val))=
      ((data (sparseActor Z T vertex) (j,b)).val:Word w))
    (flagFit : flags.Fits w scratch) (rankFit : ranks.Fits w scratch)
    (nf : slots≤flags.size) (nd : slots≤ranks.size)
    (flagEnd : flags.base+slots≤ranks.base) (rankEnd : ranks.base+slots+1 ≤ scratch)
    (middle : scratch+slots≤vals) (last : vals+slots≤dest)
    (room : dest+2*slots<2^w) (one : 1<2^w) (lanes : chunks (2^T.commonDepth) M≤2^w) :
    let nChunk:=chunks (2^T.commonDepth) M
    let cost:=4+slots*(2*(Flags.poll roots src nChunk).work+4)
    let invert:=Inverse.program w scratch vals dest slots flags ranks
    let p:=((Flags.emit roots src flags.base slots nChunk w).seq
      (ProtocolRAMEndpointPrefix.exclusive w flags.base ranks.base slots)).seq invert
    ∃out,p.Exec mem out ((cost+(10+(3+12*slots)))+
        ProtocolRAMGeneratedWrite.work slots (Inverse.address flags ranks dest slots) .row) ∧
      (∀x : ↥(commonNames Z T),out (dest+(denseHostRank Z T vertex x).val)=((sparse x).val:Word w)) ∧
      out (ranks.base+slots)=(Fintype.card ↥(commonNames Z T):Word w) ∧ (∀a<flags.base,out a=mem a) := by
  obtain ⟨done,exec,inverse,count,early,_,_⟩:=actor_directory_full Z T vertex hm wide roots src flags ranks scratch vals dest
    atRow mem rootFit srcFit nr span root words flagFit rankFit nf nd flagEnd rankEnd middle last room one lanes
  exact ⟨done,exec,inverse,count,early⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
