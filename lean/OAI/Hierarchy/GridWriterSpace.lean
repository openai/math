import OAI.Hierarchy.GridCompilerEmitter
import OAI.Hierarchy.GridBandwidth
import OAI.Hierarchy.GridTraceCap

namespace OAI
/-! # Address and shape bounds for the actual common dyadic grid writer -/

noncomputable section
namespace Hierarchy.GridCompilerAdmission
open ThreeFlat RAM UniversalGrid GridThrough GridScale Filter
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {k n p w e B : ℕ}
variable (X : Catalyst.Approximation F k p)
abbrev envelope (F : Type) [Fintype F] (k : ℕ) := 1000*(k+1)+(Fintype.card F)^2+50
abbrev limit (F : Type) [Fintype F] (k n e B : ℕ) := GridPaddedCellImage.limit e
  ((n+1)^k) B (Ordered.hiddenCount e n) (Ordered.edgeCount e n) (Fintype.card F)

structure Space (w n e B : ℕ) : Prop where
  writer : GridOrderedSources.Fits (n:=n) (r:=e) (w:=64*w) X (arena w) B
  selection : (arena w).railMap.Fits (64*w) k n e B
  image : ∀ v : GridNativeEvaluator.Setting (e:=e) (n:=n) X,
    GridPaddedCellImage.Fits (w:=64*w) X (Ordered.wiring v) ((arena w).finalBanks (limit F k n e B))
  words : GridApproximationAdvice.wordCount X≤12*B
  compact : 12*B≤(arena w).J
  rails : e≤(arena w).J/8
  axes : k≤(arena w).J/8
  pinData : (n+1)^k*p≤(arena w).J
  kernel : GridNativeEvaluator.footprint (n:=n) (e:=e) X ≤ 2^(64*w)

theorem space (age : envelope F k≤w) (hk : 0<k) (pos : 0<B) (size : X.size≤B)
    (fixed : 6+k+Fintype.card F*Fintype.card F≤B)
    (low : (n+1)^k*B≤2^(2*w))
    (line : e*(n+1)≤2*k*((n+1)^k*B)) : Space X w n e B := by
  let L := (n+1)^k*B
  let J := GridDescription.sector w
  change 1000*(k+1)+(Fintype.card F)^2+50≤w at age
  have wp : 1≤w := by omega
  have high := GridDescription.sectors_fit wp
  have Lpos : 1≤L := Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) pos
  have bL : B≤L := Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
  have gridSide : n+1≤(n+1)^k := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (Nat.succ_pos n) (show 1≤k from hk))
  have gL : n+1≤L := gridSide.trans (Nat.le_mul_of_pos_right _ pos)
  have copy : (n+1)^k≤L := Nat.le_mul_of_pos_right _ pos
  have space3 : w*L≤2^(3*w) := by
    calc
      _ ≤ 2^w*2^(2*w) := Nat.mul_le_mul Nat.lt_two_pow_self.le low
      _ = _ := by rw [←pow_add]; congr 1; omega
  have sectors : 8*2^(3*w)≤J := by
    change 2^3*2^(3*w)≤2^(32*w)
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have eL : e≤e*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have cL : (400*k+40+(Fintype.card F)^2+11)*L≤2^(3*w) :=
    (Nat.mul_le_mul_right L (by omega)).trans space3
  change e*(n+1)≤2*k*L at line
  have lin : limit F k n e B≤2^(3*w) := by
    have b := GridPaddedCellImage.linear_limit (F:=F) line
    change _≤(250*k+40)*L+(Fintype.card F)^2+11 at b
    have f := Nat.le_mul_of_pos_right ((Fintype.card F)^2+11) Lpos
    exact b.trans (by nlinarith only [cL,f,Nat.zero_le (k*L)])
  have L3 : L≤2^(3*w) := (Nat.le_mul_of_pos_left _ wp).trans space3
  have ec : GridOrderedEdgeRAM.totalWords e n≤12*(e*(n+1)) := by
    unfold GridOrderedEdgeRAM.totalWords Ordered.edgeCount
    nlinarith only [eL]
  have pl : GridApproximationAdvice.portCount X≤B := by
    unfold Catalyst.Approximation.size at size
    exact (Nat.le_add_left _ _).trans size
  have pp : p≤B := (show p≤GridApproximationAdvice.portCount X by
    simp [GridApproximationAdvice.portCount,Catalyst.Port]).trans pl
  have data : (n+1)^k*p≤L := Nat.mul_le_mul_left _ pp
  have kL : k*L≤2^(3*w) := (Nat.mul_le_mul_right L (by omega)).trans space3
  have e3 : e*(n+1)≤2^(3*w) := line.trans
    ((Nat.mul_le_mul_right L (by omega : 2*k≤w)).trans space3)
  have klPos : k≤2^(3*w) := (Nat.le_mul_of_pos_right _ Lpos).trans kL
  have words := GridApproximationAdvice.wordCount_cap X size fixed
  have pack : 12*B≤J := (Nat.mul_le_mul_left 12 bL).trans
    ((Nat.mul_le_mul_right L (by omega : 12≤w)).trans (space3.trans (by omega)))
  have edges : GridOrderedEdgeRAM.totalWords e n≤J := ec.trans <|
    (Nat.mul_le_mul_left 12 line).trans (by
      have bet := (Nat.mul_le_mul_right L (by omega : 24*k≤w)).trans space3
      nlinarith only [bet,sectors])
  have chosen : (n+1)^k*k*B≤J := by
    rw [show (n+1)^k*k*B=k*L by dsimp [L]; ring]
    omega
  have kRows : (n+1)^k*k≤J := by
    exact (Nat.le_mul_of_pos_right _ pos).trans chosen
  have arcRoom : 12*J<2^(64*w) := by change 64*J<_ at high; omega
  have localRoom : L ≤ J := by omega
  have railRoom : e*(n+1) ≤ J := by omega
  have railPart : e ≤ J/8 := by omega
  have axisPart : k ≤ J/8 := by omega
  have position : GridOrderedSources.Fits (n:=n) (r:=e) (w:=64*w) X (arena w) B :=
    GridOrderedSources.fits_of_pages X _ B (words.trans pack) pl
      (fun j => (GridApproximationAdvice.width_le_size X j).trans size)
      (copy.trans localRoom) (gL.trans localRoom) axisPart (bL.trans localRoom)
      (data.trans localRoom) localRoom chosen edges railRoom (by change 2 ≤ J; omega) arcRoom
  have runtime := GridNativeEvaluator.path_bound (e:=e) (n:=n) X size line
  have sq := Nat.le_mul_of_pos_right ((Fintype.card F)^2+11) Lpos
  refine ⟨position,?_,?_,words,pack,railPart,axisPart,data.trans localRoom,?_⟩
  · constructor
    · exact (gL.trans localRoom).trans_lt (by omega)
    · exact (copy.trans localRoom).trans_lt (by omega)
    · exact (bL.trans localRoom).trans_lt (by omega)
    · change 5*J+e ≤ 6*J; omega
    · change 5*J+J/8+e ≤ 6*J; omega
    · change 5*J+2*(J/8)+k ≤ 6*J; omega
    · change 5*J+3*(J/8)+e ≤ 6*J; omega
    · constructor
      · change 6*J+(n+1)^k*k ≤ 7*J; omega
      · change 7*J+((n+1)^k*k)*B ≤ 8*J; omega
    · change 8*J+e*(n+1) < 2^(64*w); omega
  · intro v
    have enough : limit F k n e B ≤ 2^(4*w) := lin.trans
      (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3*w≤4*w))
    have widthEq : (Ordered.wiring v).internal=Ordered.hiddenCount e n := rfl
    have extentEq : GridPaddedCellImage.limit e ((n+1)^k) B (Ordered.wiring v).internal
        (Ordered.wiring v).equal.length (Fintype.card F)=limit F k n e B :=
      congrArg₂ (fun hidden edges => GridPaddedCellImage.limit e ((n+1)^k) B hidden edges (Fintype.card F))
        widthEq (Ordered.wiring_count v)
    have pageEq (amount : ℕ) : GridPaddedCellImage.sectors w amount=(arena w).finalBanks amount := rfl
    have fitted := GridPaddedCellImage.sector_fits X (Ordered.wiring v) wp (Nat.pow_pos (Nat.succ_pos _))
      size fixed (by rw [extentEq]; exact enough)
    rw [extentEq,pageEq] at fitted
    exact fitted
  · change _≤(400*k+40)*L+_+11 at runtime
    nlinarith only [runtime,cL,sq,high,sectors,Nat.zero_le (GridNativeEvaluator.tailTime (n:=n) (e:=e) X)]

theorem selected_space {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (A k : ℕ) (pos : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      let B := pairs A w q
      ∀ X : Catalyst.Approximation F k (q*pins w a), X.size≤B →
        Space X w (side a-1) (external k a B) B := by
  filter_upwards [depth_range env k A 0,sublinear env (10*k+3),sublinear env 2,
    budgets env k A 1 0,eventually_ge_atTop (2*envelope F k)] with w depth sub half h large
  intro q qp qt a B X size
  have hi := (depth q qp qt).2
  change (10*k+3)*a≤w at sub
  change evalDepth w k A 0 a q≤w+(10*k+3)*a at hi
  have step : evalDepth w k A 0 a q≤2*w := by omega
  have sum : side a-1+1=side a := Nat.sub_add_cancel (Nat.two_pow_pos _)
  have hp := (h q qp qt).bankLo
  have fix : 6+k+Fintype.card F*Fintype.card F≤B := by
    change 2*a≤w at half
    have : 6+k+Fintype.card F*Fintype.card F≤w-a := by dsimp [envelope] at large; rw [←pow_two]; omega
    exact (this.trans Nat.lt_two_pow_self.le).trans hp
  apply space X (by omega) pos ((Nat.two_pow_pos _).trans_le hp) size fix
  · rw [sum]
    calc
      _ = evalWork w k A 0 a q := by simp [evalWork]
      _ ≤ 2^(2*w) := (Nat.lt_log2_self.le).trans (Nat.pow_le_pow_right (by decide : 0<2) step)
  · rw [sum]
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    simp only [B,external,Nat.succ_sub_one,pow_succ]
    ring_nf; exact le_rfl

end Hierarchy.GridCompilerAdmission
end

end OAI
