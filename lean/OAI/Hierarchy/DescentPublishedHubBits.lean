import OAI.Hierarchy.DescentPackedCensusFromSigned
import OAI.Hierarchy.DescentHubOrdinal
import OAI.Hierarchy.DescentOrdinaryHostCount
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # The physical public hub bit at seed and ordinary common hosts -/
namespace Hierarchy.DescentHubBits
open DescentSIMDLookup DescentSixParty DescentPacking.PackedMatch.Local.Stage
open DescentHostDirectory DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) {H : ℕ} (rank : V↪Fin H)

theorem live (v : V) : (Census.hub A rank (rank v)).val=(A.hub v).toNat := by
  have present : ∃u,rank u=rank v:=⟨v,rfl⟩
  have chosen:=rank.injective present.choose_spec
  simp only [Census.hub,dite_eq_left present,chosen]
  cases A.hub v <;> decide

theorem absent (a : Fin H) (none : ¬∃u,rank u=a) : Census.hub A rank a=0 := by
  simp [Census.hub,dite_eq_right none]

theorem column {w : ℕ} (base : ℕ) (m : Memory w)
    (real : ∀v,m (base+(rank v).val)=((A.hub v).toNat:Word w))
    (filler : ∀i : Fin H,(¬∃v,rank v=i)→m (base+i.val)=0) :
    ∀i : Fin H,m (base+i.val)=((Census.hub A rank i).val:Word w) := by
  intro i
  by_cases occurs : ∃v,rank v=i
  · obtain ⟨v,rfl⟩:=occurs
    rw [live]
    exact real v
  · rw [absent A rank i occurs]
    exact filler i occurs

def ordinary (slot prev select : Bank) : Expr :=
  .branch .eq (.lookup select .row) (.lit 0) (.lit 0) (.lookup prev (.lookup slot .row))

/-- Both immutable columns are public functions of the heap size, slot count and gain.
The sole dynamic operand is the bit at the old host. -/
theorem scan_ordinary {w : ℕ} (k slots gain : ℕ) (slot prev select : Bank) (out : ℕ)
    (len : ℕ) (mem : Memory w) (old : ℕ→Bool)
    (sfit : slot.Fits w out) (pfit : prev.Fits w out) (efit : select.Fits w out)
    (room : out+len<2^w) (slotsFit : len≤ slot.size) (eligFit : len≤ select.size)
    (oldRoom : ∀i : Fin len,(ordinaryHubRow k slots gain i.val).1<prev.size)
    (previous : ∀i : Fin len,let t:=(ordinaryHubRow k slots gain i.val).1
      mem (prev.base+t)=((old t).toNat:Word w))
    (static : ∀i : Fin len,let entry:=ordinaryHubRow k slots gain i.val
      mem (slot.base+i.val)=(entry.1:Word w) ∧ mem (select.base+i.val)=(entry.2.toNat:Word w)) :
    let term:=ordinary slot prev select
    let next:=image out len term mem
    (scan w out len term).Exec mem next (4+len*(2*term.work+4)) ∧
    (∀i : Fin len,let entry:=ordinaryHubRow k slots gain i.val
      next (out+i.val)=((old entry.1 && entry.2).toNat:Word w)) ∧
    ∀a,a<out ∨ out+len≤a→next a=mem a := by
  let expr:=ordinary slot prev select
  refine ⟨scan_exec out len expr mem ⟨⟨efit,trivial⟩,trivial,trivial,pfit,sfit,trivial⟩ room,?_,
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _⟩
  intro i
  have x:=(lookup_nat slot mem (i.val:Word w) .row i.val rfl (i.isLt.trans_le slotsFit) sfit.2.1).trans (static i).1
  have e:=(lookup_nat select mem (i.val:Word w) .row i.val rfl (i.isLt.trans_le eligFit) efit.2.1).trans (static i).2
  have b:=(lookup_nat prev mem (i.val:Word w) _ _ x (oldRoom i) pfit.2.1).trans (previous i)
  rw [ProtocolRAMGeneratedWrite.read_image]
  change (if (Expr.lookup select .row).eval mem (i.val:Word w) == (0:Word w) then 0
    else (Expr.lookup prev (.lookup slot .row)).eval mem (i.val:Word w)) = _
  rw [e,b]
  have wide : 1<2^w:=lt_of_le_of_lt pfit.1 pfit.2.1
  have nonzero : (1 : Word w) ≠ 0 := by
    intro eq
    have val := congrArg Fin.val eq
    simp [Nat.mod_eq_of_lt wide] at val
  cases flag : (ordinaryHubRow k slots gain i.val).2 <;> simp [nonzero]

end
end Hierarchy.DescentHubBits

namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDirectory DescentHubBits DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
open DescentCompiler DescentHostDegree ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d k w : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {S : AtomSchedule}
  {q ε : ℝ} {W : MarkedWorld F d P bits} {i z degree wire hist z' degree' : ℕ} {u : ℝ}
  {src : Reached W G q ε S k i z degree wire hist} {he : 0≤ε} {T : StageInput W G u ε}
  {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {tgt : Reached n.result G q ε S k (i+1) z' degree' wire hist}
  (link : OrdinaryLink src he T p n tgt)


include link in
/-- The heap tag decoded at the actual successor rank uses the old rank of its
actual predecessor, including true hosts with no incident cable. -/
theorem hub_row (v : tgt.V) :
    let slots:=2^packExponent 20 src.placement.degree+2
    let gain:=gainExponent 20 src.placement.degree
    let entry:=ordinaryHubRow k slots gain (tgt.vertex v).val
    ∃u : src.V,(src.vertex u).val=entry.1 ∧ tgt.placement.hub v=(src.placement.hub u && entry.2) := by
  obtain ⟨age,power,chart,_,index,members,flags⟩:=link.hostOrdinal
  dsimp only
  rw [index v,ordinaryHubRow_at k _ _ (fun u=>(src.vertex u).val) (chart v) (members v)]
  exact ⟨(chart v).1,rfl,flags v⟩

include link in
/-- At a padded position beyond the true full rectangle the predecessor read
also lies beyond its real prefix and therefore contributes zero. -/
theorem ghost_parent {x : ℕ} (ghost : Fintype.card tgt.V≤x) :
    let slots:=2^packExponent 20 src.placement.degree+2
    let gain:=gainExponent 20 src.placement.degree
    Fintype.card src.V≤(ordinaryHubRow k slots gain x).1 := by
  change Fintype.card src.V≤x/_/_
  apply (Nat.le_div_iff_mul_le (heapRoom k)).2
  apply (Nat.le_div_iff_mul_le (by positivity)).2
  simpa only [link.hostCount] using ghost

/-- The single predecessor flag used by the native row expression is defined on
every natural address. The compact extent decides all reads on padded hosts. -/
def oldBit (x : ℕ) : Bool :=
  if h : ∃v,(src.vertex v).val=x then src.placement.hub h.choose else false

theorem oldBit_at (v : src.V) : oldBit (src:=src) (src.vertex v).val=src.placement.hub v := by
  have yes : ∃u,(src.vertex u).val=(src.vertex v).val:=⟨v,rfl⟩
  simp only [oldBit,dite_eq_left yes,src.vertex.injective (Fin.ext yes.choose_spec)]

include link in
theorem census_ordinary {pad lo bits : ℕ} (enough : Fintype.card tgt.V≤pad)
    (mem : Memory bits) (rows : ∀i : Fin pad,
      let entry:=ordinaryHubRow k (2^packExponent 20 src.placement.degree+2)
        (gainExponent 20 src.placement.degree) i.val
      mem (lo+i.val)=((oldBit (src:=src) entry.1 && entry.2).toNat:Word bits)) :
    ∀i : Fin pad,mem (lo+i.val)=((Census.hub tgt.placement
      (tgt.vertex.trans (Fin.castLEEmb enough)) i).val:Word bits) := by
  apply DescentHubBits.column
  · intro v
    change mem (lo+(tgt.vertex v).val)=((tgt.placement.hub v).toNat:Word bits)
    have result:=rows ((tgt.vertex v).castLE enough)
    obtain ⟨u,fromPos,hub⟩:=link.hub_row v
    simpa only [Fin.val_castLE,←fromPos,oldBit_at,hub] using result
  · intro i empty
    have before:=DescentHostCount.prefix_live tgt.vertex enough i
    have big : Fintype.card tgt.V≤ i.val:=Nat.le_of_not_gt (fun h=>empty (before.mp h))
    have prev:=link.ghost_parent big
    have missing : ¬∃v,(src.vertex v).val=(ordinaryHubRow k (2^packExponent 20 src.placement.degree+2)
        (gainExponent 20 src.placement.degree) i.val).1 := by
      rintro ⟨v,hit⟩
      have tight:=(src.vertex v).isLt
      omega
    simpa [oldBit,missing] using rows i

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
