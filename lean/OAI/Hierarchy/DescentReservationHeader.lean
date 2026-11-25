import OAI.Hierarchy.DescentResetWalshCutoff
import OAI.Hierarchy.DescentResetReservationCount
import OAI.Hierarchy.DescentGoodPortCoherence

namespace OAI
/-! # The actual direct-link reserved width from the old Walsh total and both measured depths -/
namespace Hierarchy.DescentReservationHeader
open DescentPlainTerminal.Suffix.Cutoff DescentSIMDLookup DescentGL DescentColonies DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w : ℕ}

/-- Oversized reservations for unobserved neighbors clip to the finite column count.
The two lookup banks have exactly the same addressing as the attained cutoff pass. -/
def width (K scale level count Y : ℕ) : ℕ :=
  min Y ((Y*(K*count+scale*2^level)) ⌈/⌉ (8*K*(scale*2^level)))

def header (base levels total K scale bound : ℕ) (m : Memory w) (z : ℕ) : Word w :=
  if z<base then m z else if z-base<2^levels then (2^total*(z-base):ℕ) else
    if z-(base+2^levels)<2^(levels+total) then
      let idx:=z-(base+2^levels)
      (width K scale (idx/2^total) (idx%2^total) bound:ℕ) else m z

def Resident (base levels total K scale bound : ℕ) (m : Memory w) : Prop :=
  (∀j<2^levels,m (base+j)=(2^total*j:ℕ)) ∧
    ∀j<2^levels,∀z<2^total,m (base+2^levels+(2^total*j+z))=(width K scale j z bound:ℕ)

theorem mounted (base levels total K scale bound : ℕ) (m : Memory w) :
    Resident base levels total K scale bound (header base levels total K scale bound m) := by
  refine ⟨fun j hj=>?_,fun j hj z hz=>?_⟩
  · simp only [header,not_lt.mpr (Nat.le_add_right _ _),ite_false,Nat.add_sub_cancel_left,hj,ite_true]
  · have idx:=index_lt levels total j z hj hz
    have outside : ¬base+2^levels+(2^total*j+z)<base := by omega
    have later : ¬base+2^levels+(2^total*j+z)-base<2^levels := by omega
    simp only [header,outside,ite_false,later,Nat.add_sub_cancel_left,idx,ite_true,
      Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt hz,Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt hz]

theorem frame (base levels total K scale bound : ℕ) (m : Memory w) (z : ℕ) (apart : z<base ∨ finish base levels total≤z) :
    header base levels total K scale bound m z=m z := by
  rcases apart with before|after
  · simp [header,before]
  · unfold finish at after
    have nonnegLevels := Nat.zero_le (2^levels)
    have nonnegTable := Nat.zero_le (2^(levels+total))
    have aboveBase : base ≤ z := by omega
    have aboveLevels : 2^levels ≤ z-base := by omega
    have aboveTable : 2^(levels+total) ≤ z-(base+2^levels) := by omega
    simp only [header,not_lt.mpr aboveBase,not_lt.mpr aboveLevels,not_lt.mpr aboveTable,ite_false]

theorem read (base levels total K scale bound : ℕ) (left right sum : Expr) (m : Memory w) (p : Word w)
    (j₁ j₂ s : ℕ) (bind : left.eval m p=(j₁:Word w)) (link : right.eval m p=(j₂:Word w))
    (source : sum.eval m p=(s:Word w))
    (levelsFit : max j₁ j₂<2^levels) (sumFit : s<2^total) (widthFit : levels+total≤w)
    (rom : Resident base levels total K scale bound m) :
    (term base levels total left right sum).eval m p=(width K scale (max j₁ j₂) s bound:ℕ) := by
  let j:=max j₁ j₂
  have levelWidth : 2^levels≤2^w:=Nat.pow_le_pow_right (by decide) (by omega)
  have jw : j<2^w:=levelsFit.trans_le levelWidth
  have j1 : j₁<2^w:=(le_max_left j₁ j₂).trans_lt jw
  have j2 : j₂<2^w:=(le_max_right j₁ j₂).trans_lt jw
  have tested : DescriptorExpr.Comparison.lt.test (left.eval m p) (right.eval m p)=true ↔ j₁<j₂ := by
    rw [bind,link]
    simp only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,
      Fin.val_cast_of_lt j1,Fin.val_cast_of_lt j2]
  have chosen : (level left right).eval m p=(j:Word w) := by
    by_cases less : j₁<j₂
    · calc
        (level left right).eval m p=right.eval m p := ite_eq_left (tested.mpr less)
        _=(j:Word w) := by simpa only [j,max_eq_right less.le] using link
    · calc
        (level left right).eval m p=left.eval m p := ite_eq_right (mt tested.mp less)
        _=(j:Word w) := by simpa only [j,max_eq_left (le_of_not_gt less)] using bind
  have offset : (levelBank base levels).read m (j:Word w)=((2^total*j:ℕ):Word w) := by
    change m (base+(j:Word w).val%2^levels)=_
    rw [Fin.val_cast_of_lt jw,Nat.mod_eq_of_lt (show j<2^levels from levelsFit)]
    exact rom.1 j levelsFit
  have index := index_lt levels total j s levelsFit sumFit
  have fits := index.trans_le (Nat.pow_le_pow_right (by decide) widthFit)
  change (tableBank base levels total).read m (BinaryOp.add.eval
    ((levelBank base levels).read m ((level left right).eval m p)) (sum.eval m p))=_
  rw [chosen,offset,source]
  change (tableBank base levels total).read m (((2^total*j:ℕ):Word w)+(s:Word w))=_
  rw [←Nat.cast_add]
  change m (base+2^levels+((2^total*j+s:ℕ):Word w).val%2^(levels+total))=_
  rw [Fin.val_cast_of_lt fits,Nat.mod_eq_of_lt index]
  exact rom.2 j levelsFit s sumFit

theorem word_exact (K scale level count n : ℕ) (room : n<w) :
    ((width K scale level count (2^n):Word w)).val=width K scale level count (2^n) :=
  Fin.val_cast_of_lt ((min_le_left ..).trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) room))

theorem last_word (H levels total h : ℕ) (space : levels+total≤h/2) :
    finish H levels total-H≤2*2^(h/2) :=bound_words H levels total h space

variable {hosts u l bits out : ℕ}

theorem from_first (L : Bank) (index left right : Expr) (mem : Memory w) (tick : Word w)
    (target : Fin hosts) (limit : L.Fits w out) (rows : hosts*2^u≤L.size) (widthBits : bits≤w)
    (addr : index.eval mem tick=((row target (fun _ : Fin u=>false)).val:Word w))
    (flow : Block (u+l)→ℕ) (measured : digit bits (ordinal l (fun _=>false)).val
      (mem (L.base+(row target (fun _ : Fin u=>false)).val)).val=∑i : Bits (u+l),flow (address (u+l) i))
    (base levels total K scale n j z : ℕ) (src : left.eval mem tick=(j:Word w))
    (dst : right.eval mem tick=(z:Word w)) (depthFit : max j z<2^levels) (sumFit : (∑x,flow x)<2^total)
    (word : levels+total≤w) (outWidth : n<w) (rom : Resident base levels total K scale (2^n) mem) :
    ((term base levels total left right (firstTotal L index bits)).eval mem tick).val=
      width K scale (max j z) (∑x,flow x) (2^n) := by
  have totalRead := firstTotal_read L index mem tick target limit rows widthBits addr flow measured
  have result := DescentReservationHeader.read base levels total K scale (2^n) left right (firstTotal L index bits)
    mem tick j z (∑x,flow x) src dst totalRead depthFit sumFit word rom
  exact (congrArg Fin.val result).trans (word_exact K scale (max j z) (∑x,flow x) n outWidth)


open DescentChosenRouter DescentSixParty
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d g h C Ht Δ : ℕ} {bw : P→ℕ}
  {W : MarkedWorld F d P bw} {price ε : ℝ} {Z : ResetInput W price ε h C Ht} {T : Z.Terminals}
variable {pos : W.graph.Site→V} {ix : W.graph.Site→Block (u+l)} {hub : V→Bool}
variable (frame : Z.SourceFrame T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K : ℕ) (traffic : V→V→Block (u+l)→ℕ)
    (wt : V→Block (u+l)→ℕ)

theorem physical_width (roster : ResetInput.SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K (fun v z i=>(traffic v z i:ℝ)) Δ wt)
    (hw : 0<wire) (hK : 0<K) (hB : 0<B) (v z : V) :
    width K (2^f*B) (max (Z.placement.b (frame.host v)) (Z.placement.b (frame.host z))) (∑x,traffic v z x) (2^n)=
      min (2^n) (T.columns.size (frame.host v) (frame.host z)) :=
  congrArg (min (2^n)) (frame.reservation_size vertex near n f B wire K Δ wt traffic roster hw hK hB v z).symm

theorem observed_span (s : Bool) (a : Z.Contact) :
    min (2^Z.n) (T.columns.size (Z.placement.ends s a).val.1 (Z.placement.ends (!s) a).val.1)=Z.placement.span a := by
  rw [←T.columns.span s a]
  apply min_eq_right
  let g:=Z.placement.ends s a
  let item : {t // Z.placement.ends s t=g}:=⟨a,rfl⟩
  exact (Finset.single_le_sum (f:=fun t : {t // Z.placement.ends s t=g}=>Z.placement.span t.val)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ item)).trans (Z.placement.room s g)

/-- Executing the previous selected chart read for one source/peer returns the exact clipped reservation.
Its output fits in n+1 bits even when the accepted column set is full. -/
theorem physical_read (roster : ResetInput.SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K (fun v z i=>(traffic v z i:ℝ)) Δ wt)
    (nonzero : 0<wire) (paid : 0<K) (positive : 0<B) (v z : V)
    (L : Bank) (idx left right : Expr) (m₀ : Memory w) (tick : Word w) (target : Fin hosts)
    (legal : L.Fits w out) (rows : hosts*2^u≤L.size) (wordBits : bits≤w)
    (physical : idx.eval m₀ tick=((row target (fun _ : Fin u=>false)).val:Word w))
    (seen : digit bits (ordinal l (fun _=>false)).val (m₀ (L.base+(row target (fun _ : Fin u=>false)).val)).val=
      ∑i : Bits (u+l),traffic v z (address (u+l) i))
    (base levels total : ℕ) (own : left.eval m₀ tick=(Z.placement.b (frame.host v):Word w))
    (peer : right.eval m₀ tick=(Z.placement.b (frame.host z):Word w)) (levelRoom : max (Z.placement.b (frame.host v)) (Z.placement.b (frame.host z))<2^levels)
    (massRoom : (∑x,traffic v z x)<2^total) (space : levels+total≤w) (output : n<w)
    (dict : Resident base levels total K (2^f*B) (2^n) m₀) :
    ((term base levels total left right (firstTotal L idx bits)).eval m₀ tick).val=
      min (2^n) (T.columns.size (frame.host v) (frame.host z)) :=
  (from_first L idx left right m₀ tick target legal rows wordBits physical (traffic v z) seen base levels total K (2^f*B) n
    (Z.placement.b (frame.host v)) (Z.placement.b (frame.host z)) own peer levelRoom massRoom space output dict).trans
    (physical_width frame vertex near n f B wire K traffic wt roster nonzero paid positive v z)

theorem stored_output (n Y : ℕ) : min (2^n) Y<2^(n+1) :=
  (min_le_left ..).trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self _))

end
end Hierarchy.DescentReservationHeader

end OAI
