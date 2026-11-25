import OAI.Hierarchy.DescentExteriorPathReplay
import OAI.Hierarchy.DescentFrozenHistoryDigits

namespace OAI
/-! # Reconstructing the actual selected per-step frozen coordinates from one fixed tape -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorReplay DescentHostDirectory DescentHostDegree DescentCommonHost DescentDenseHostOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail hwire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ i z D : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ hwire hist}
  {current : Reached W G q ε S k i z D hwire hist}
  (path : Path initial current)
  (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
  {bw count : ℕ} (slot : ℕ→Hop) (m : Memory bw) (pins : Fin count→P)

omit [Fintype P] in
theorem Path.frozen_age : path.frozen=k*i := by
  induction path with
  | here=>simp [Path.frozen]
  | ordinary prev ticket ih =>
    change k+prev.frozen = _
    rw [ih,Nat.mul_succ,Nat.add_comm]
  | reset prev b ih =>
    change k+prev.frozen = _
    rw [ih,Nat.mul_succ,Nat.add_comm]

/-- Only literal old-host scales, shape ranks and actual earlier reset directories.
The full index row for each exterior cohort is supplied once by the immutable calendar. -/
def Path.shapeFields : Prop := by
  induction path with
  | here=>exact True
  | @ordinary A age zi Di zn Dn src prev fee he T c norm dst ticket ih =>
    let bank:=slot age
    let heap:=stage slot count m age
    exact ih ∧ bank.compact=none ∧
      (∀v,bank.hostBase.read heap ((src.vertex v).val:Computability.VPVNP.BurstRAM.Word bw)=
        (((src.vertex v).val*((2^(k+1)-1)*(2^packExponent 20 src.placement.degree+2)):ℕ):Computability.VPVNP.BurstRAM.Word bw)) ∧
      ∀bit:Block k,bank.localShape.read heap (bit.val:Computability.VPVNP.BurstRAM.Word bw)=
        ((nodeNumber (k-gainExponent 20 src.placement.degree)
          (group (k-gainExponent 20 src.placement.degree) bit)*(2^packExponent 20 src.placement.degree+2):ℕ):Computability.VPVNP.BurstRAM.Word bw)
  | @reset A age zi Di dim gh C₀ f₀ g₀ c₀ t₀ src prev ctl b ih=>
    let hop:=slot age
    let heap:=stage slot count m age
    let vertex:=b.frame.host.symm.toEmbedding.trans src.vertex
    let palette:=DescentDenseHostOrder.roster b.reset.graph (b.reset.k-b.terminals.commonDepth)
      (GroupStage.depthBound Di dim f₀ g₀)
    exact ih ∧ ∃bank,hop.compact=some bank ∧
      (∀v,hop.hostBase.read heap ((src.vertex v).val:Computability.VPVNP.BurstRAM.Word bw)=(((src.vertex v).val*palette.card:ℕ):Computability.VPVNP.BurstRAM.Word bw)) ∧
      (∀bit:Block k,hop.localShape.read heap (bit.val:Computability.VPVNP.BurstRAM.Word bw)=(b.localTrunk bit:Computability.VPVNP.BurstRAM.Word bw)) ∧
      ∀v,bank.read heap ((b.reset.rawHostRank b.terminals vertex v).val:Computability.VPVNP.BurstRAM.Word bw)=
        ((b.reset.denseHostRank b.terminals vertex v).val:Computability.VPVNP.BurstRAM.Word bw)

private theorem split_number {f g t : ℕ} {A B C E : Type}
    {before:E→Bits t} {mid:E→Bits f} {later:E→Bits g} {h₀:E→A} {h₁:E→B} {h₂:E→C}
    {k z:ℕ} (old:Spine before mid h₀ h₁ z) (next:Spine mid later h₁ h₂ k)
    (n:ℕ) (u:E) (observed : n%2^(k+z)=(address _ ((old.append next).cut (before u)).2).val) :
    n%2^z=(address _ (old.cut (before u)).2).val ∧
      n/2^z%2^k=(address _ (next.cut (mid u)).2).val := by
  have a:=old.earlier next u
  have b:=old.newest next u
  rw [←observed,pow_add,Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)] at a
  rw [←observed,pow_add,Nat.mod_mul_left_div_self] at b
  exact ⟨a,b⟩

open DescentHostDirectory DescentHostDegree DescentCommonHost DescentDenseHostOrder in
theorem Path.fields_of_digits (p:ℕ) (hp:0<p) (a:Archive I) (r:path.recorded p) (seed:a.Particles initial)
    (code:Fin count→ℕ) (literal:∀t < i,∀j:Fin count,(slot t).frozenDigit.read (stage slot count m t) (j.val:Computability.VPVNP.BurstRAM.Word bw)=
      ((code j/2^(k*t)%2^k:ℕ):Computability.VPVNP.BurstRAM.Word bw))
    (shape:path.shapeFields (count:=count) slot m)
    (frozen:∀j:Fin count,code j%2^path.frozen=
      (address _ ((path.pinSpine base radix p hp a r seed).cut (active initial base radix (pins j))).2).val) :
    path.exteriorFields base radix slot m pins := by
  induction path with
  | here=>trivial
  | ordinary prev ticket ih=>
    obtain ⟨past,direct,scale,localName⟩:=shape
    let prior:=prev.pinSpine base radix p hp a r seed
    let owner:=(prev.particles p hp a r seed).attached
    let next:=ticket.pinStep base radix owner
    have pieces j:=split_number prior next (code j) (pins j) (frozen j)
    refine ⟨ih r (fun t ht=>literal t (by omega)) past (fun j=>(pieces j).1),owner,direct,?_,?_,?_⟩
    · intro j
      rw [literal _ (Nat.lt_succ_self _),←prev.frozen_age]
      exact congrArg (fun n:ℕ=>(n:Computability.VPVNP.BurstRAM.Word bw)) (pieces j).2
    · exact fun _=>scale _
    · exact fun _=>localName _
  | @reset A age zi Di dim gh C₀ f₀ g₀ c₀ t₀ src prev ctl b ih=>
    obtain ⟨past,bank,direct,scale,localName,lookup⟩:=shape
    have eqTail : tail=t₀:=by
      simpa only [Nat.log2_two_pow] using congrArg Nat.log2 (base.symm.trans ctl.base)
    subst t₀
    let prior:=prev.pinSpine base radix p hp a r.1 seed
    let owner:=(prev.particles p hp a r.1 seed).attached
    let next:=b.pinStep owner
    have pieces j:=split_number prior next (code j) (pins j) (frozen j)
    refine ⟨ih r.1 (fun t ht=>literal t (by omega)) past (fun j=>(pieces j).1),owner,bank,direct,?_,?_,?_,lookup⟩
    · intro j
      rw [literal _ (Nat.lt_succ_self _),←prev.frozen_age]
      exact congrArg (fun n:ℕ=>(n:Computability.VPVNP.BurstRAM.Word bw)) (pieces j).2
    · exact fun _=>scale _
    · exact fun _=>localName _

end
end Hierarchy.DescentSixParty.Chronology

end OAI
