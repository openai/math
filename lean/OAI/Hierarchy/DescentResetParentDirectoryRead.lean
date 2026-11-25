import OAI.Hierarchy.DescentResetParentAperture
import OAI.Hierarchy.DescentResetParentDate
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The bounded directory instruction recovers the preceding host of every real reset actor -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentHubBits DescentCensusRAM ProtocolRAM
open DescentDyadicSpan DescentResetParentDate
open DescentResetParentAperture (parent codes ids first bins)
open DescentIssuedTerminalId Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "pool" => roster Z.graph (Z.k-T.commonDepth) Ht
set_option quotPrecheck false in
local notation "Vnew" => ↥(Z.commonNames T)
variable {H pad : ℕ} (vertex : Z.V↪Fin H) (capacity : Fintype.card ↥(Z.commonNames T)≤pad)
local notation "S" => Finset.card pool
local notation "N" => H*S
local notation "raw" => rawHostRank Z T vertex
local notation "rank" => Function.Embedding.trans (denseHostRank Z T vertex) (Fin.castLEEmb capacity)

theorem bounded_parent_directory {w : ℕ} (base : ℕ) (flags : Bank) (mem : Memory w)
    (old : flags.Fits w base) (rows : N≤flags.size) (room : DescentResetParentDate.endAddress base N pad<2^w)
    (bitsAt : ∀j:Fin N,mem (flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(raw v).val) j.val:Word w)) :
    let out:=DescentResetParentDate.memory base N pad S flags mem room
    DescentResetStemKeyReindex.Directory (parent base N pad).base (Z.parentIndex T vertex) out ∧
    (∀j:Fin pad,(¬∃v,rank v=j) → out ((parent base N pad).base+j.val)=0) ∧
    ∀a,a<base ∨ DescentResetParentDate.endAddress base N pad≤a → out a=mem a := by
  classical
  intro out
  let b:=DescentResetParentAperture.banks base N pad w room
  let m₀:=DescentResetParentDate.head base N S mem
  let m₁:=DescentResetParentDate.«prefix» base N S flags mem
  let v₀:=DescentResetParentDate.value base N
  have run:=DescentResetParentDate.any base N pad S flags mem old rows room
  obtain ⟨codesFit,idFit,lim,_⟩:=DescentResetParentAperture.fits room
  have fn : N≤(codes base N).size:=span_ge _
  have fi : N≤(ids base N).size:=(Nat.le_succ _).trans (span_ge _)
  have split:base+N≤(ids base N).base:=Nat.add_le_add_left fn _
  have low:flags.base+N≤base:=(Nat.add_le_add_left rows _).trans old.2.2
  have data0 (i : Fin N) : m₀ (flags.base+i.val)=mem (flags.base+i.val):=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl (by have:=i.isLt;omega))
  have data1 (a : ℕ) (small : a<(ids base N).base) : m₁ a=m₀ a:=
    ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl small)
  obtain ⟨canonical,named⟩:=Z.hostTape_native T vertex m₀ (low.trans (by omega)) lim
    (fun i hi=>(data0 ⟨i,hi⟩).trans (bitsAt ⟨i,hi⟩))
  have physical : (ProtocolRAMEndpointPrefix.exclusive w flags.base (ids base N).base N).Exec
      m₀ m₁ (10+(3+12*N)):=ProtocolRAMEndpointPrefix.run flags.base (ids base N).base N (sumWords flags.base m₀) m₀
    (low.trans (by omega)) lim rfl (fun j _=>by simp [sumWords])
  have eqn:=ProtocolRAM.exec_unique _ m₀ _ _ physical canonical
  have activeBits (i : Fin N) : m₁ (flags.base+i.val)=(if active raw i then 1 else 0) := by
    rw [data1 _ (by have:=i.isLt;omega),data0 i,bitsAt i]
    by_cases live : active raw i
    · obtain ⟨v,rfl⟩ := live
      rw [ite_eq_left (show active raw (raw v) from ⟨v,rfl⟩),
        DescentEdgeTapePrefix.row_present (fun _ : Vnew => 1) (fun u : Vnew => (raw u).val)
          (fun _ _ eqn => (raw).injective (Fin.ext eqn)) v]
      rfl
    · rw [ite_eq_right live,DescentEdgeTapePrefix.row_absent _ _ _ (fun v h=>live ⟨v,Fin.ext h⟩)]
      rfl
  have ranked (v : Vnew) : m₁ ((ids base N).base+(raw v).val)=((rank v).val:Word w):=by
    rw [eqn]; exact named v
  have up:base≤b.first:=by change base ≤ base + DescentDyadicSpan.span N + DescentDyadicSpan.span (N+1); omega
  have chosen:=DescentParentBoundedKey.genuine raw rank b flags (ids base N) m₁
    ⟨old.1,old.2.1,old.2.2.trans up⟩ idFit rows fi activeBits ranked
  have weight (j : Fin N) : (v₀.eval m₁ (j.val:Word w)).val=(Z.parentROM T j).val := by
    have r:=(lookup_nat (codes base N) m₁ (j.val:Word w) .row j.val rfl (j.isLt.trans_le fn) codesFit.2.1).trans
      ((data1 _ (by change base+j.val<(ids base N).base;have:=j.isLt;omega)).trans
      (DescentStaticWordColumn.read base N (fun t=>t/S) mem j.isLt))
    change ((Expr.lookup (codes base N) .row).eval m₁ (j.val:Word w)).val=_
    rw [r,←Z.parentROM_val T j,Fin.val_cast_of_lt (by have:=j.isLt;have:=Nat.div_le_self j.val S;change j.val/S<2^w;omega)]
  have read (j : Fin (pad+1)) :
      out (b.bins+j.val)=(sumAt (target raw rank) (fun t=>(Z.parentROM T t).val) j:Word w):=by
    have vals:=run.2.2.2 j
    rw [chosen,show (fun t:Fin N=>(v₀.eval m₁ (t.val:Word w)).val)=(fun t=>(Z.parentROM T t).val) from funext weight] at vals
    exact vals
  refine ⟨Z.parent_directory T vertex _ out ?_,?_,run.2.2.1⟩
  · intro v
    change out (b.bins + (rank v).val) = _
    have total := read (rank v).castSucc
    simp only [sumAt, target_at, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Z.parentROM_at T vertex] at total
    exact total
  · intro j empty
    have different (t : Fin N) : target raw rank t≠j.castSucc:=by
      by_cases active' : active raw t
      · intro hit
        rw [target, dite_eq_left active'] at hit
        exact empty ⟨active'.choose, Fin.ext (congrArg (fun x : Fin (pad+1) => x.val) hit)⟩
      · intro eqn
        rw [target,dite_eq_right active'] at eqn
        exact (Nat.ne_of_lt j.isLt) (congrArg Fin.val eqn).symm
    change out (b.bins + j.val) = 0
    simpa [sumAt,different] using read j.castSucc

include capacity in
/-- Both issued programs agree on every allocated receiver in the authentic occupancy bitmap. -/
theorem parent_matches_original {w : ℕ} (base : ℕ) (flags : Bank) (mem : Memory w)
    (old : flags.Fits w base) (rows : N≤flags.size) (room : DescentResetParentDate.endAddress base N pad<2^w)
    (bitsAt : ∀j:Fin N,mem (flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(raw v).val) j.val:Word w)) :

    let actual:=DescentResetParentDate.memory base N pad S flags mem room
    ∃original : Memory w,
      (DescentResetParentAperture.originalProgram base N pad S flags w room).Exec mem original
        (DescentResetParentAperture.originalTicks base N pad flags w room) ∧
      (DescentResetParentDate.program base N pad S flags w room).Exec mem actual
        (DescentResetParentDate.ticks base N pad flags w room) ∧
      ∀j : Fin pad,actual ((parent base N pad).base+j.val)=original ((parent base N pad).base+j.val):=by
  intro actual
  have bounded:=Z.bounded_parent_directory T vertex capacity base flags mem old rows room bitsAt
  obtain ⟨out,ran,_,_,original,blank,_⟩:=DescentResetParentAperture.original_publish
    Z T vertex capacity base flags mem old rows room bitsAt
  refine ⟨out,ran,(DescentResetParentDate.any base N pad S flags mem old rows room).1,?_⟩
  intro j
  by_cases exists_ : ∃v,rank v=j
  · obtain ⟨v,rfl⟩:=exists_
    exact (bounded.1 (Z.denseHostRank T vertex v)).trans (original (Z.denseHostRank T vertex v)).symm
  · exact (bounded.2.1 j exists_).trans (blank j exists_).symm


end
end Hierarchy.DescentSixParty.ResetInput

end OAI
