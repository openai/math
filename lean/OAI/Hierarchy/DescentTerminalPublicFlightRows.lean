import OAI.Hierarchy.DescentTerminalPublicSortBook
import OAI.Hierarchy.DescentTerminalOriginalExterior
import OAI.Hierarchy.DescentTerminalPlaneArena

namespace OAI
/-! # Whole public output words from the executed third flight and the stable order -/
namespace Hierarchy.DescentTerminalPublicIdentity
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPublicWordRAM
open DescentTerminalDataPlane DescentExteriorShelf DescentExterior DescentGL DescentExteriorFetch
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open DescentTerminalExteriorPackets DescentTerminalPrimitiveArena DescentInitialHost
open Computability.BorderVNP.FragmentBucket ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {F : Type} [Field F] {cp data w j r t H : ℕ}
variable (X : Approximation F cp data)
set_option quotPrecheck false
local notation "E" => ExteriorCount X
local notation "N" => E*2^(j+r)
local notation "C" => 2^j*t
variable (rawRows headerRows : ℕ)
local notation "state" => (⟨E,j,r,t,rawRows,N,headerRows⟩ : DescentTerminalDataPlane.Shape)
variable (origin sortedAt identityAt : ℕ) (cables : Fin 5→Bank) (candidate : Bank)
local notation "tapes" => controls sortedAt identityAt N
local notation "plane" => Arena.plane state origin tapes cables candidate
local notation "Mems" => Memory w

private theorem live_row (L : Tapes) (rows : ℕ) (m : Memory w) (u : Word w)
    (live : u < (rows : Word w)) :
    (row L rows).eval m u =
      L.phase.read m (L.slabBase.read m (L.slab.read m (L.portAt.read m u)) +
        L.highBase.read m (L.high.read m (L.portAt.read m u)) + L.lowAt.read m u) := by
  exact ite_eq_left (decide_eq_true live)

omit [Field F] in
theorem public_flight (m : Mems) (layout : Fin E → DescentGL.Layout (j+(j+r)))
    (x : Fin E → Plane j r → Fin t→Bool) (hidden : Hidden E j r t→Bool) (home : Fin N → Fin H)
    (positive : 0<w) (bits : C ≤ w) (space : origin+24*span j r t E<2^w)
    (identityLow : identityAt+pad N ≤ origin) (sortedLow : sortedAt+N ≤ origin)
    (identities : ∀i < pad N,m (identityAt+i)=(i:Word w))
    (sorted : ∀u : Fin N,m (sortedAt+u.val)=(((Computability.BorderVNP.FragmentBucket.dest home).symm u).val:Word w))
    (matrix : Loaded origin layout x hidden m) (i : Fin N) :
    DescentTerminalDataPlane.exteriorRows state plane m ((plane).output.base+i.val)=
      ((flight X layout hidden ((Computability.BorderVNP.FragmentBucket.dest home).symm i)).val:Word w) := by
  let post:=DescentTerminalDataPlane.exterior state plane m
  have spanRow := row_room j r t E
  have capacity : N<2^w := by omega
  have idRoom : pad N<2^w := by omega
  have hold (a : ℕ) (ha : a < origin) : post a=m a := flagged_before j r t E origin m ha
  have table (u : ℕ) (hu : u<pad N) : post (identityAt+u)=(u:Word w) :=
    (hold _ ((Nat.add_lt_add_left hu _).trans_le identityLow)).trans (identities u hu)
  obtain ⟨literal,nil⟩:=reads (w:=w) N identityAt idRoom table
  have rank (u:Fin N) : (bank sortedAt N).read post (u.val:Word w)=
      (((Computability.BorderVNP.FragmentBucket.dest home).symm u).val:Word w) := by
    rw [at_index capacity u,hold _ ((Nat.add_lt_add_left u.isLt _).trans_le sortedLow),sorted]
  have measured:=(machine_trace origin positive bits (by omega) layout x hidden m 0 0 matrix).2.2.2
  have word (u:Fin N) : (plane).public.phase.read post (u.val:Word w)=((flight X layout hidden u).val:Word w) := by
    change post (start j r t E origin+2*N+((u.val:Word w).val%span j r t E))=_
    rw [Fin.val_cast_of_lt (u.isLt.trans capacity),Nat.mod_eq_of_lt (u.isLt.trans_le spanRow)]
    exact (preserves_flights origin m (2:Fin 3) u).trans (measured u)
  let perm := (Computability.BorderVNP.FragmentBucket.dest home).symm i
  have lo : (i.val : Word w) < ((N : ℕ) : Word w) := by
    rw [Fin.lt_def, Fin.val_cast_of_lt (i.isLt.trans capacity), Fin.val_cast_of_lt capacity]
    exact i.isLt
  have near : i.val<N+2 := by have:=i.isLt;omega
  refine (DescentTerminalChipRuntime.image_at post (plane).output.base (N+2)
    (row (plane).public N) ⟨i.val,near⟩).trans ?_
  refine (live_row (plane).public N post (i.val : Word w) lo).trans ?_
  change (plane).public.phase.read post (((⟨identityAt,0⟩:Bank).read post ((⟨identityAt,0⟩:Bank).read post
    ((bank sortedAt N).read post (i.val:Word w)))+(bank identityAt N).read post ((bank identityAt N).read post
    ((bank sortedAt N).read post (i.val:Word w))))+(⟨identityAt,0⟩:Bank).read post (i.val:Word w))=_
  simp only [rank i,nil,literal,zero_add,add_zero]
  exact word perm

end
end Hierarchy.DescentTerminalPublicIdentity

end OAI
