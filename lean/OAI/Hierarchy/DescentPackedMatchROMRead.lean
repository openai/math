import OAI.Hierarchy.DescentPackedMatchROM

namespace OAI
/-! # Readback of the matcher dictionaries and the two immutable mask banks -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentPackedProfileWindow
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {r D p d K H G M w : ℕ}

structure Loaded (s : Shape) (B R : ℕ) (A : Menu (r:=r) (D:=D) (p:=p) (K:=K)) (m : Memory w) : Prop where
  joins : ∀j,DescentPackedZip.Static (A.joins j) (setField (d:=d) j) M m
  descriptors : ∀key : Fin K,∀i : Cell ((d*fields r D p)*M),m ((A.desc key).base+i.val)=
    ((DescentSIMDLookup.table (descriptor (r:=r) (D:=D) (p:=p) (digit:=d) s B key.val) i).val:Word w)
  masks : ∀t : Row H G M,m (A.mask.base+(row H G M t).val)=(maskWord s.inputBits M G t.2.val:Word w)
  lookup : resident s A.lookup (K*H) G M m
  sums : ∀i : Cell (s.outputBits*M),m (A.count.base+i.val)=(chunkCount s M i:Word w)
  fixed : ProfileTable.static s M R A.profile m

theorem loaded (s : Shape) (d r D p B K H G M unit base : ℕ) (source : Bank) (m : Memory w)
    (large : matchUnit s d r D p≤unit) :
    let R:=M*s.pairs
    Loaded (d:=d) (M:=M) (H:=H) (G:=G) s B R (chart s d r D p K H G M R unit base source)
      (mounted s d r D p B K H G M R unit base m) := by
  let R:=M*s.pairs
  let N:=fields r D p
  let a:=s.outputBits*M
  let b:=s.digit*R
  have wide : d*N+d≤unit := (le_max_left _ _).trans large
  have env : s.bits+3*(s.digit*s.pairs)≤unit := (le_max_right _ _).trans large
  have inp : s.inputBits≤ s.bits:=le_max_left ..
  have out : s.outputBits≤ s.bits:=le_max_right ..
  have raw : d*N*M≤unit*M := Nat.mul_le_mul_right M (by omega)
  have joined:=(Nat.mul_le_mul_right M wide)
  have arg : s.inputBits*M≤unit*M:=Nat.mul_le_mul_right M (by omega)
  have scaled:=Nat.mul_le_mul_right M env
  have bound:=Nat.mul_le_mul_right M out
  have full : ProfileTable.bits a b≤unit*M := by
    dsimp only [ProfileTable.bits,a,b,R]
    nlinarith only [scaled,bound]
  have top : a≤unit*M := by unfold ProfileTable.bits at full;omega
  have off : b≤unit*M := by unfold ProfileTable.bits at full;omega
  have rd (j : Page N K) {bits : ℕ} (i : Cell bits) (fits : bits≤unit*M) :=
    page_read s d r D p B K H G M R unit base m j i.val
      (i.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) fits))
  constructor
  · intro j
    constructor
    · intro i
      exact rd (.inl (.inl 0)) i raw
    · intro i
      simpa only [chart,R,code,at_live] using rd (.inl (.inr j)) i joined
  · intro key i
    simpa only [chart,R,code,at_live] using rd (.inr (.inl key)) i raw
  · intro t
    simpa only [chart,R,Equiv.symm_apply_apply] using desc_mask s d r D p B K H G M R unit base m (row H G M t)
  · constructor
    · intro i
      change _=((DescentSIMDLookup.table (lookupCell s) i).val:Word w)
      simpa only [chart,R,code,show (0 : Fin 6).val = 0 by decide,at_live] using rd (.inr (.inr 0)) i arg
    · exact topo_mask s d r D p B K H G M R unit base m
  · intro i
    simpa only [chart,R,code,show (1 : Fin 6).val = 1 by decide,at_live] using rd (.inr (.inr 1)) i top
  · refine ⟨fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_⟩
    · exact rd (.inr (.inr 2)) i top
    · exact rd (.inr (.inr 3)) i off
    · exact rd (.inr (.inr 4)) i off
    · simpa only [chart,R,code,show (5 : Fin 6).val = 5 by decide,at_live] using rd (.inr (.inr 5)) i full

theorem Loaded.header {s : Shape} {B R : ℕ} {A : Menu (r:=r) (D:=D) (p:=p) (K:=K)} {m : Memory w}
    (h : Loaded (d:=d) (M:=M) (H:=H) (G:=G) s B R A m) (l : ProfileTable.Layout) (stream : ℕ→Cell s.digit)
    (count : l.countROM=A.count) (tables : l.tables=A.profile)
    (raw : ∀j<l.raw.size,m (l.raw.base+j)=((DescentPackedProfileWindow.word s.digit R stream j).val:Word w)) :
    Header s M R (K*H) G A.lookup l stream m :=
  ⟨h.lookup,fun i=>by simpa only [count] using h.sums i,by simpa only [tables] using h.fixed,raw⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

end OAI
