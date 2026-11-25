import OAI.Hierarchy.DescentTerminalNeighborVolume
import OAI.Hierarchy.DescentTerminalPointerGather

namespace OAI
/-! # The shared terminal table counting all true grains to a selected neighbor -/

namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentSIMDLookup DescentTerminalPointerDigits Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentSharedCableNames ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- One short signed field for each block, signed port, and packed group chunk. -/
abbrev PanelIndex (blocks cap groups M:ℕ) := Fin blocks×Fin (2*cap)×Fin (chunks groups M)
def columns (blocks cap groups M:ℕ) := 1+blocks*((2*cap)*chunks groups M)
def number (blocks cap groups M:ℕ) : Fin 1 ⊕ PanelIndex blocks cap groups M ≃ Fin (columns blocks cap groups M) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv

def candidate (D : ℕ) (n : ℕ) : Option (Fin D) := if h:0<n ∧ n≤D then some ⟨n-1,by omega⟩ else none
theorem candidate_read {D : ℕ} (j:Fin D) : candidate D (j.val+1)=some j := by
  have h:0<j.val+1 ∧ j.val+1≤D:=⟨by omega,j.isLt⟩
  simp [candidate,h]

variable {blocks cap groups M d w : ℕ}
def sample (D:ℕ) (positive:0<M) (z:Fin (columns blocks cap groups M)→Cell d)
    (x:Fin blocks) (j:Fin (2*cap)) (g:Fin groups) : Option (Stage.Live D cap) :=
  let c:=(position (0:Fin 1) g positive).2
  let a:=DescentSignedCableCodec.width D cap
  let v:Cell a:=⟨digit a (lane g positive).val (z (number blocks cap groups M (.inr (x,j,c)))).val,DescentTerminalSignedGrainWord.digit_bound ..⟩
  DescentSignedCableCodec.decode D cap v

def tally (D scale:ℕ) (positive:0<M) (z:Fin (columns blocks cap groups M)→Cell d) : ℕ :=
  match candidate D (z (number blocks cap groups M (.inl 0))).val with
  | none=>0
  | some j=>(∑g:Fin groups,∑x:Fin blocks,(peerWires (fun k=>sample D positive z x k g) j).card)*scale

theorem tally_bound (D scale:ℕ) (positive:0<M) (z:Fin (columns blocks cap groups M)→Cell d) :
    tally D scale positive z≤groups*(blocks*cap)*scale := by
  unfold tally
  split
  · exact Nat.zero_le _
  · apply Nat.mul_le_mul_right
    calc
      _ ≤ ∑_:Fin groups,∑_:Fin blocks,cap := Finset.sum_le_sum fun g _=>Finset.sum_le_sum fun x _=>
        (Finset.card_le_card (Finset.filter_subset ..)).trans (by simp)
      _ = _ := by simp

def bits (blocks cap groups scale:ℕ) := Nat.clog 2 (groups*(blocks*cap)*scale+1)
def aggregate (D scale:ℕ) (positive:0<M) (z:Fin (columns blocks cap groups M)→Cell d) :
    Cell (bits blocks cap groups scale) :=
  ⟨tally D scale positive z,(Nat.lt_succ_of_le (tally_bound D scale positive z)).trans_le (Nat.le_pow_clog (by decide) _)⟩

/-- The previous group banks retain packed cells at `home*chunks+chunk`.
The numeric `first` and `ticket` arguments have one physical read per
bounded-degree candidate. `ticket` is zero for an inactive side. -/
def source (first ticket:Expr) (panels : Fin blocks→Fin (2*cap)→Bank) :
    Fin (columns blocks cap groups M)→Expr := fun j=>
  Sum.elim (fun _=>ticket) (fun t:PanelIndex blocks cap groups M=>
    .lookup (panels t.1 t.2.1) (.op .add first (.lit t.2.2.val))) ((number blocks cap groups M).symm j)

theorem reads_sample {n homes : ℕ} (D:ℕ) (positive:0<M) (mem:Memory w) (first ticket:Expr)
    (panels:Fin blocks→Fin (2*cap)→Bank) (i:Fin n) (home:Fin homes)
    (homeRead:first.eval mem (i.val:Word w)=((home.val*chunks groups M:ℕ):Word w))
    (whole:∀x j (k:Fin (chunks groups M)),((panels x j).read mem (((home.val*chunks groups M+k.val:ℕ):Word w))).val<2^d)
    (fits:∀x j,homes*chunks groups M≤(panels x j).size) (space:homes*chunks groups M≤2^w)
    (x:Fin blocks) (j:Fin (2*cap)) (g:Fin groups) :
    sample (d:=d) D positive (Gather.values (source first ticket panels) mem i) x j g=
      DescentTerminalSignedGrainWord.wing D cap (panels x j) mem home g positive := by
  let c:=(position (0:Fin 1) g positive).2
  have coord:home.val*chunks groups M+c.val=(row homes groups M (position home g positive)).val := by
    simp [row,position,c,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have at_:(panels x j).read mem (((home.val*chunks groups M+c.val:ℕ):Word w))=
      mem ((panels x j).base+(row homes groups M (position home g positive)).val) := by
    rw [coord,Bank.read,Fin.val_cast_of_lt ((row homes groups M (position home g positive)).isLt.trans_le space),Nat.mod_eq_of_lt ((row homes groups M (position home g positive)).isLt.trans_le (fits x j))]
  have value:(Gather.values (source first ticket panels) mem i
      (number blocks cap groups M (.inr (x,j,c))) : Cell d).val=
      (mem ((panels x j).base+(row homes groups M (position home g positive)).val)).val := by
    simp only [Gather.values,source,Equiv.symm_apply_apply,Sum.elim_inr,Expr.eval,homeRead,RowOp.opcode,BinaryOp.eval,
      ←Nat.cast_add]
    rw [Fin.val_cast_of_lt (whole x j c),at_]
  unfold sample DescentTerminalSignedGrainWord.wing DescentTerminalSignedGrainWord.chip
  apply congrArg (DescentSignedCableCodec.decode D cap)
  apply Fin.ext
  exact congrArg (digit _ (lane g positive).val) value

theorem issue (D scale:ℕ) (positive:0<M) (origin n:ℕ) (first ticket:Expr) (panels:Fin blocks→Fin (2*cap)→Bank)
    (mem:Memory w) (fits:∀j,((source (groups:=groups) (M:=M) first ticket panels) j).Fits w origin)
    (small:2^d<2^w) (endAt:Gather.rom origin (columns blocks cap groups M) n+
      DescentTerminalPointerFrame.size (columns blocks cap groups M) d+n<2^w) :
    let src:=source (groups:=groups) (M:=M) first ticket panels
    let f:=aggregate D scale positive (blocks:=blocks) (cap:=cap) (groups:=groups) (d:=d)
    let ps:=Gather.reads origin n src
    let warm:=result ps mem
    let B:=Gather.banks (L:=columns blocks cap groups M) origin n
    let base:=Gather.rom origin (columns blocks cap groups M) n
    let fee:=DescentTerminalPointerFrame.size (columns blocks cap groups M) d
    let out:=base+fee
    let next:=DescentTerminalPointerFrame.result base B n f warm
    ((program w ps).seq (DescentTerminalPointerFrame.program w base B n f)).Exec mem next
      (clock ps+((4+10*fee)+(4+n*(16+26*columns blocks cap groups M)))) ∧
      CheapCode ((program w ps).seq (DescentTerminalPointerFrame.program w base B n f)) ∧
      (∀i:Fin n,next (out+i.val)=((f (Gather.values src mem i)).val:Word w)) ∧
      ∀a,a<origin ∨ out+n≤a→next a=mem a :=
  Gather.execute origin n (source first ticket panels) (aggregate D scale positive (d:=d)) mem fits small endAt

end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI
