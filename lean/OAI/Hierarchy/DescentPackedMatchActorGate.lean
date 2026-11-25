import OAI.Hierarchy.DescentPackedMatchedGeometry
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Gate every selected winner by the actual prior row's actor bit -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.ActorGate
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {k d s M H G w : ℕ}

def expression (tab : Fin (2^k)→Tables) (actors : Bank) (winner : Fin (2^k)→Bank) (x : Fin (2^k)) : Expr :=
  (tab x).read (.lookup actors .row) (.lookup (winner x) .row)

def passes (tab : Fin (2^k)→Tables) (actors : Bank) (winner : Fin (2^k)→Bank) (base H G M : ℕ) :=
  ProbeStage.Native.columns (H*chunks G M) base (List.ofFn (expression tab actors winner))

def ptr (base H G M : ℕ) (x : Fin (2^k)) := base+x.val*(H*chunks G M)

theorem work (tab : Fin (2^k)→Tables) (actors : Bank) (winner : Fin (2^k)→Bank) (base H G M : ℕ) :
    clock (passes tab actors winner base H G M)≤4+2^k*(4+H*chunks G M*(2*25+4)) := by
  have bound := ProbeStage.Native.columns_clock (H*chunks G M) base 25 (List.ofFn (expression tab actors winner)) (by
    intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;simp only [expression,Tables.read,Expr.work];decide)
  simpa only [passes,List.length_ofFn] using bound

theorem run (tab : Fin (2^k)→Tables) (actors : Bank) (winner : Fin (2^k)→Bank) (base : ℕ) (m : Memory w)
    (fit : ∀x,Fits (tab x) (.lookup actors .row) (.lookup (winner x) .row) (1*2^k) d M base w)
    (room : base+2^k*(H*chunks G M)<2^w) (spanA : H*chunks G M≤actors.size) (spanW : ∀x,H*chunks G M≤(winner x).size)
    (active : Fin H→Fin G→Cell (1*2^k)) (value : Fin (2^k)→Fin H→Fin G→Cell d)
    (chip : ∀p : Row H G M,m (actors.base+(row H G M p).val)=((data active p).val:Word w))
    (live : ∀x,∀p : Row H G M,m ((winner x).base+(row H G M p).val)=((data (value x) p).val:Word w))
    (fixed : ∀x,Static (tab x) (fun u (t : Cell d) => gated (s:=s) u x t) M m) :
    let ps:=passes tab actors winner base H G M
    let mem:=result ps m
    (program w ps).Exec m mem (clock ps) ∧
      (∀x,∀p : Row H G M,mem (ptr base H G M x+(row H G M p).val)=
        ((data (fun h g=>gated (s:=s) (active h g) x (value x h g)) p).val:Word w)) ∧
        (∀a<base,mem a=m a) ∧ CheapCode (program w ps) := by
  let es:=List.ofFn (expression tab actors winner)
  have fields (e : Expr) (he : e∈es) : e.Fits w base := by
    obtain ⟨x,rfl⟩:=List.mem_ofFn.mp he
    exact ⟨(fit x).apply,(fit x).right,(fit x).shift,(fit x).left⟩
  have len : es.length=2^k := List.length_ofFn
  refine ⟨ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es le_rfl fields (by simpa only [len] using room)),?_,
    (fun _ h=>ProbeStage.Native.columns_frame es m (Or.inl h)),@ProtocolRAM.program_cheap _ _⟩
  intro x p
  change result (ProbeStage.Native.columns (H*chunks G M) base es) m
    (base+x.val*(H*chunks G M)+(row H G M p).val) = _
  refine (ProbeStage.Native.columns_read es m le_rfl fields x.val
    (x.isLt.trans_eq len.symm) (row H G M p)).trans ?_
  have af : actors.Fits w base := (fit x).left.1
  have wf : (winner x).Fits w base := (fit x).right.1
  have zero : gated (s:=s) (0 : Cell (1*2^k)) x (0 : Cell d)=0 := by simp [gated,digit]
  simpa only [es,List.getElem_ofFn,expression] using read_data (tab x) (.lookup actors .row) (.lookup (winner x) .row) base (fit x)
    (fun a b=>gated (s:=s) a x b) zero m (fixed x) active (value x) (source_column actors base af m active spanA chip)
    (source_column (winner x) base wf m (value x) (spanW x) (live x)) p

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.ActorGate

end OAI
