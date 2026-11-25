import OAI.Hierarchy.DescentIssuedFallbackPanel
import OAI.Hierarchy.DescentPriorOperandColumns
import OAI.Hierarchy.DescentResetFieldReturn
import OAI.Hierarchy.DescentResetChannelSubwords
import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! # Original operand digits at each physical reset donor and its remixed low coordinate -/
namespace Hierarchy.DescentResetRetainedPages
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentOperandStateBanks
open DescentSixParty.PackedFlow.Channels DescentGLPacked DescentGLPacked.BankImage
open DescentGL DescentColonies DescentIssuedFallbackPanel
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a b N D H h l c M w : ℕ}

/-- Original node selection costs one shared dictionary for all pages. The
matrix receives the scalar width, rather than the full previous K-node cell. -/
def node {slots : ℕ} (base a N M : ℕ) (old : Pages slots→Bank) (p : Pages slots) (n : Fin N) : Expr :=
  ScalarOperand.project (ScalarOperand.chart base a N M) (.lookup (old p) .row) n

theorem original {slots : ℕ} (base floor : ℕ) (old : Pages slots→Bank) (valAt : Pages slots→Fin H→Block (h+l)→Cell (a*N))
    (m : Memory w) (p : Pages slots) (n : Fin N)
    (fits : (old p).Fits w base) (capacity : H*chunks (2^(h+l)) (2^l)≤(old p).size)
    (oldReads : DescentPackedColony.Reads (old p) (valAt p) (2^l) m)
    (placed : base+N*2^((a*N)*2^l)≤floor) (small : floor<2^w) :
    let mid:=ROM.after (ScalarOperand.pages a N (2^l)) ((a*N)*2^l) base m
    Source (node base a N (2^l) old p n) (fun v z=>ScalarOperand.take n (valAt p v z)) (2^l) mid :=by
  intro mid
  have pre : base≤floor:=(Nat.le_add_right ..).trans placed
  have kept : DescentPackedColony.Reads (old p) (valAt p) (2^l) mid:=by
    intro q
    have low: (old p).base+(row H (2^(h+l)) (2^l) q).val<base:=
      (Nat.add_lt_add_left ((row _ _ _ q).isLt.trans_le capacity) _).trans_le fits.2.2
    exact (ROM.frame _ _ _ _ _ (.inl low)).trans (oldReads q)
  exact ScalarOperand.fetched _ _ n floor mid _
    (source_column _ floor ⟨fits.1,fits.2.1,fits.2.2.trans pre⟩ mid _ capacity kept)
    (ROM.bank_room _ _ _ _ n le_rfl placed small) rfl (ScalarOperand.initialized base a N (2^l) m n)

/-- The previous bank used by the basis changer is literally the earlier
word of M slow groups times r consecutive block digits. -/
theorem ungrouped {groups oldLanes radix : ℕ} (src : Bank)
    (size : 2^(h+l)=groups*radix) (batch : 2^l=oldLanes*radix) (hm : 0<oldLanes) (hr : 0<radix)
    (x : Fin H→Block (h+l)→Cell b) (m : Memory w)
    (held : DescentPackedColony.Reads src (fun v g=>encode b radix (fun j=>x v (Fin.cast size.symm (finProdFinEquiv (g,j))))) oldLanes m) :
    DescentPackedColony.Reads src x (2^l) m :=DescentPackedResetSource.ungroup_cast size batch hm hr src.base m x held

/-- The literal low donor field following the common GL permutation. It is
shared by every high row, with no per-group address or name in the code. -/
def low (base b radix M : ℕ) (B : Bank) (j : Fin radix) : Expr :=
  ScalarOperand.project (ScalarOperand.chart base b radix M) (.lookup B .row) j

def originalAt (small : c≤h+l) (L : DescentGL.Layout (h+l)) (j : Fin (2^(h+l-c)))
    (x : Fin H→Block (h+l)→Cell a) (v : Fin H) (hi : Block c) :=
  x v ((rearrange L).symm (join small hi j))

theorem remixed (small : c≤h+l) (L : DescentGL.Layout (h+l)) (j : Fin (2^(h+l-c)))
    (x : Fin H→Block (h+l)→Cell a) (B : Bank) (base floor : ℕ) (m : Memory w)
    (fit : B.Fits w base) (capacity : H*chunks (2^c) M≤B.size)
    (emitted : DescentPackedColony.Reads B (blockValues small x L) M m)
    (placed : base+(2^(h+l-c))*2^((a*2^(h+l-c))*M)≤floor) (limit : floor<2^w) :
    let radix:=2^(h+l-c)
    let mid:=ROM.after (ScalarOperand.pages a radix M) ((a*radix)*M) base m
    Source (low base a radix M B j) (originalAt small L j x) M mid :=by
  intro radix mid
  have cut : base≤floor:=(Nat.le_add_right ..).trans placed
  have read : DescentPackedColony.Reads B (blockValues small x L) M mid:=by
    intro q
    have before:= (Nat.add_lt_add_left ((row H (2^c) M q).isLt.trans_le capacity) B.base).trans_le fit.2.2
    exact (ROM.frame _ _ _ _ _ (.inl before)).trans (emitted q)
  have got:=ScalarOperand.fetched (ScalarOperand.chart base a radix M) (.lookup B .row) j floor mid
    (blockValues small x L) (source_column B floor ⟨fit.1,fit.2.1,fit.2.2.trans cut⟩ mid _ capacity read)
    (ROM.bank_room _ _ _ _ j le_rfl placed limit) rfl (ScalarOperand.initialized base a radix M m j)
  unfold originalAt
  simpa only [radix,low,ScalarOperand.take,blockValues,Equiv.symm_apply_apply] using got

/-- Use the true selected mixed bank directly when the old lanes split
exactly; the smaller-lane variant accepts the cells returned by Channels.repack. -/
theorem from_dense (small : c≤h+l) (pitch : M*2^(h+l-c)=2^l) (hm : 0<M)
    (L : DescentGL.Layout (h+l)) (j : Fin (2^(h+l-c))) (x : Fin H→Block (h+l)→Cell a)
    (B : Bank) (base floor : ℕ) (m : Memory w) (fit : B.Fits w base) (capacity : H*chunks (2^c) M≤B.size)
    (mixed : Dense (h:=h) (l:=l) B.base (fun v z=>x v ((rearrange L).symm z)) m)
    (placed : base+(2^(h+l-c))*2^((a*2^(h+l-c))*M)≤floor) (limit : floor<2^w) :
    let radix:=2^(h+l-c)
    let mid:=ROM.after (ScalarOperand.pages a radix M) ((a*radix)*M) base m
    Source (low base a radix M B j) (originalAt small L j x) M mid :=
  remixed small L j x B base floor m fit capacity
    (DescentPlainTerminal.Suffix.grouped_remix small pitch hm B.base x L m mixed) placed limit

theorem donor_site {J V : Type} (order : Block (h+l)≃J×Block b) (L : DescentGL.Layout (h+l))
    (small : c≤h+l) (j : Fin (2^(h+l-c))) (host : Fin H→V) (x : ((J×V)×Block b)→Cell a)
    (v : Fin H) (hi : Block c) :
    originalAt small L j (fun v z=>x (((order z).1,host v),(order z).2)) v hi=
      x (DescentIssuedFallbackPanel.donor order L small (host v) hi j) :=rfl

end
end Hierarchy.DescentResetRetainedPages

end OAI
