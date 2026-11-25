import OAI.Hierarchy.DescentScalarBookColumns
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentVectorBookReshape

namespace OAI
/-! # One program gathers every operand page and sends it to the receiving bank -/
namespace Hierarchy.DescentGatheredVectorReshape
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM.ScalarOperand (Refs Values Measured)
open scoped Fin.CommRing
noncomputable section
variable {N Q D k K cap H G J r M w s nb mb : ℕ}
local notation "gatherColumns" => DescentOrdinaryAtomFieldRAM.ScalarOperand.columns

def program (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a base out w : ℕ) (src : Bank) :=
  (ProtocolRAM.program w (gatherColumns C src.base H G (M*r))).seq
    (DescentVectorBookReshape.program N H Q J r a M base out w src)

def result (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a base out : ℕ) (src : Bank) (m : Memory w) :=
  DescentVectorBookReshape.result N H Q J r a M base out src (ProtocolRAM.result (gatherColumns C src.base H G (M*r)) m)

def ticks (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a : ℕ) (src : Bank) :=
  ProtocolRAM.clock (gatherColumns C src.base H G (M*r)) + DescentVectorBookReshape.ticks N H Q J r a M

private theorem recode {A B H L a w : ℕ} (same : A=B) (name : Fin B → Fin A) (numeric : ∀i,(name i).val=i.val)
    (xs : Fin H → Fin A → Cell a) (m : Memory w) (base : ℕ)
    (old : ∀p : Row H A L,m (base+(row H A L p).val)=((data xs p).val:Word w)) :
    ∀p : Row H B L,m (base+(row H B L p).val)=((data (fun h g=>xs h (name g)) p).val:Word w) := by
  subst B
  have eq : ∀g,name g=g := fun g=>Fin.ext (numeric g)
  simpa only [eq] using old

theorem run (C : Fin N → Fin Q → Refs D k K cap) (V : Fin N → Fin Q → Values D k K cap H G s nb mb)
    (base out K' : ℕ) (src : Bank) (m : Memory w) (hm : 0 < M) (hr : 0 < r)
    (same : G=J*r) (name : Fin (J*r) → Fin G) (numeric : ∀i,(name i).val=i.val)
    (measured : ∀page l,Measured (C page l) (V page l) K' (M*r) src.base m)
    (fit : DescentVectorBookReshape.Room N H Q J r (s*K') M w base out src) :
    let done := result C H G J r M (s*K') base out src m
    (program C H G J r M (s*K') base out w src).Exec m done (ticks C H G J r M (s*K') src) ∧
    (∀page b (p : Row (H*Q) J M),done (DescentScalarBookReshape.dest H Q J M
       (DescentVectorBookReshape.destBase out H Q J r M page) b+(row (H*Q) J M p).val)=
       ((data (DescentScalarBookReshape.book (fun l h g=>(V page l).book K' h (name g)) b) p).val:Word w)) ∧
    ∀u,u < src.base ∨ out+N*DescentVectorBookReshape.rows H Q J r M ≤ u → done u=m u := by
  intro done
  let mid := ProtocolRAM.result (gatherColumns C src.base H G (M*r)) m
  have counts : chunks G (M*r)=chunks J M := by rw [same]; exact chunks_group J M r hm hr
  have endSrc : src.base+(N*Q)*(H*chunks G (M*r)) ≤ base := by
    rw [counts]
    simpa only [DescentVectorBookReshape.sourceWords,Nat.mul_assoc] using fit.sourceEnd
  have destEnd : base ≤ out := (Nat.le_add_right ..).trans fit.early
  have width := fit.end_
  obtain ⟨gather,banks,gframe,_⟩ :=
    DescentOrdinaryAtomFieldRAM.ScalarOperand.all_books C V src.base K' (M*r) m measured (by omega)
  let f page l h (g : Fin (J*r)) := (V page l).book K' h (name g)
  have previous (page : Fin N) (l : Fin Q) := recode same name numeric ((V page l).book K') mid
    (DescentVectorBookReshape.sourceBase src H Q J M page+l.val*(H*chunks J M)) (by
      intro p
      simpa only [DescentOrdinaryAtomFieldRAM.ScalarOperand.place,DescentVectorBookReshape.sourceBase,
        DescentVectorBookReshape.sourceWords,counts,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using banks page l p)
  obtain ⟨moved,posted,mframe⟩ := DescentVectorBookReshape.run base out src mid f hm hr fit previous
  refine ⟨fun {P R K₀} mach pc reg pub exit rom advice cfg raw enter sameMem =>
    Procedure.Exec.then gather moved mach pc reg pub exit rom advice cfg raw enter sameMem,posted,?_⟩
  intro u at_
  rcases at_ with low|high
  · exact (mframe u (.inl (low.trans_le ((Nat.le_add_right ..).trans endSrc)))).trans (gframe u (.inl low))
  · exact (mframe u (.inr high)).trans (gframe u (.inr (endSrc.trans (destEnd.trans ((Nat.le_add_right ..).trans high)))))

/-- The native procedure terminates with its advertised clock on arbitrary memory. -/
theorem exec (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a base out : ℕ) (src : Bank) (m : Memory w)
    (early : ∀p l,((C p l).expr H).inputEnd ≤ src.base)
    (inside : src.base+(N*Q)*(H*chunks G (M*r)) < 2^w)
    (room : DescentVectorBookReshape.Room N H Q J r a M w base out src) :
    (program C H G J r M a base out w src).Exec m (result C H G J r M a base out src m) (ticks C H G J r M a src) := by
  intro P R K₀ mach pc reg pub exit rom advice cfg raw enter same
  exact Procedure.Exec.then
    (DescentOrdinaryAtomFieldRAM.ScalarOperand.exec C src.base H G (M*r) m early inside)
    (DescentVectorBookReshape.exec base out src
      (ProtocolRAM.result (gatherColumns C src.base H G (M*r)) m) room)
    mach pc reg pub exit rom advice cfg raw enter same

theorem cheap (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a base out w : ℕ) (src : Bank) :
    CheapCode (program C H G J r M a base out w src) := by
  exact cheap_seq (@ProtocolRAM.program_cheap _ _)
    (cheap_seq (@DescentStaticWordColumn.cheap w base _ _) (@scan_cheap _ _ _ _))

theorem tariff (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a w base out source : ℕ) (src : Bank)
    (limits : ∀p l,let t:=C p l;t.want.work+t.addr.work+t.counts.work ≤ source) :
    let nodes:=DescentPackedActorMask.nodes (DescentHaloWalkRAM.breadth D*2^k) K cap
    let bound:=DescentOrdinaryAtomFieldRAM.ScalarOperand.termBound nodes source
    ticks C H G J r M a src ≤
        (4+(N*Q)*(4+(H*chunks G (M*r))*(2*bound+4))) +
          (8+10*DescentVectorBookReshape.dictionaryWords r a M+74*(N*DescentVectorBookReshape.rows H Q J r M)) ∧
      DescentStaticWordColumn.names (program C H G J r M a base out w src) ≤
        (15+(N*Q)*(11+4*bound)) + (15*(DescentVectorBookReshape.cells N H Q J r a M+1)+111) := by
  intro nodes bound
  obtain ⟨ct,hw⟩ := DescentOrdinaryAtomFieldRAM.ScalarOperand.tariff C src.base H G (M*r) w source limits
  constructor
  · unfold ticks
    rw [DescentVectorBookReshape.ticks_eq]
    exact Nat.add_le_add_right ct _
  · unfold program
    rw [DescentStaticWordColumn.names_seq,DescentVectorBookReshape.names]
    exact Nat.add_le_add_right hw _

/-- All immutable inputs, including banks allocated between work areas, keep their words. -/
theorem frame (C : Fin N → Fin Q → Refs D k K cap) (H G J r M a base out : ℕ) (src : Bank) (m : Memory w)
    (u : ℕ) (old : u < src.base ∨ src.base+(N*Q)*(H*chunks G (M*r)) ≤ u)
    (static : u < base ∨ base+DescentVectorBookReshape.cells N H Q J r a M ≤ u)
    (output : u < out ∨ out+N*DescentVectorBookReshape.rows H Q J r M ≤ u) :
    result C H G J r M a base out src m u=m u := by
  apply (DescentVectorBookReshape.frame _ u static output).trans
  apply ProbeStage.Native.columns_frame
  simpa [DescentOrdinaryAtomFieldRAM.ScalarOperand.expressions] using old

end
end Hierarchy.DescentGatheredVectorReshape

end OAI
