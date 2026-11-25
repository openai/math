import OAI.ThreeFlat.Diagonal.PhysicalShrinkAdmission
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace

namespace OAI
/-! # Word-space bounds for the actual shrinking stage and its integral layout scores -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident
open NavigationDirectory NavigationPass PhysicalShrink
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D : ℕ)
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "wideTags" => ThreeFlat.Diagonal.tagBits d
local notation "t" => CompressorPacking.tagBits d

def shrinkFixedWords : ℕ :=
  80 + d + 2^k + 2^wideTags + (3*(2^k*d)/4) + D + (S).pieceRadix + keyBound S 1 wideTags +
    T.more.length+1 + widthMultiplicity k d + shrinkBaseBound T + shrinkMotifWidthFactor T k d

private theorem scalar_summands {slots colors tags bundle degree pieces keys tiles demand table issued v : ℕ}
    (total : 80+slots+colors+tags+bundle+degree+pieces+keys+tiles+1+demand+table+issued≤v) :
    colors≤v ∧ slots≤v ∧ tags≤v ∧ bundle≤v ∧ degree≤v ∧ pieces≤v ∧ keys≤v ∧
      tiles+1≤v ∧ demand≤v ∧ table≤v ∧ issued≤v := by
  omega

private theorem scalar_heap_bounds (shape : Dimensions) {v : ℕ} (arena : (Stage.shrink shape).heapWords≤v) :
    shape.motifs≤v ∧ shape.oldBase≤v := by
  simp only [Stage.heapWords] at arena
  omega

variable (rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
variable (A : State (2^s) (shrinkCharge s+rem))
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "x" => dims S N t rem
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "top" => shrinkMotifWidthFactor T k d*(1+A.maxWidth)

theorem shrink_scalar_room {u : ℕ} (hu : 40≤u) (fixed : shrinkFixedWords T s D≤u)
    (arena : (Stage.shrink x).heapWords≤2^(u^10))
    (wire : A.maxWidth+1≤(2^(u^10))^4) :
    let W:=16*u^10
    ShrinkOldCaps s rem W ∧ ShrinkOutputCaps s D N W ∧ T.more.length+1≤2^W ∧
      1+2*(widthMultiplicity k d*A.maxWidth)+shrinkBaseBound T<2^W ∧ top<2^W ∧
      80*(Q).motifs*top^2<2^W := by
  let v:=2^(u^10)
  have uv : u≤v := by
    exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) _))
  have huge : 2^(16*u^10) = v^16 := by rw [Nat.mul_comm, pow_mul]
  have one_lt_v : 1<v := by omega
  have smallV : v<v^16 := by simpa only [pow_one] using Nat.pow_lt_pow_right one_lt_v (by decide : 1<16)
  have fixv : shrinkFixedWords T s D≤v := fixed.trans uv
  obtain ⟨co,sl,wideRadix,bun,tg,pc,wideKey,tiles,dem,tbl,issue⟩ :=
    scalar_summands (slots:=d) (colors:=2^k) (tags:=2^wideTags) (bundle:=3*(2^k*d)/4)
      (degree:=D) (pieces:=(S).pieceRadix) (keys:=keyBound S 1 wideTags)
      (tiles:=T.more.length) (demand:=widthMultiplicity k d) (table:=shrinkBaseBound T)
      (issued:=shrinkMotifWidthFactor T k d) (v:=v) fixv
  have nativeTags : t ≤ wideTags :=
    Nat.clog_le_of_le_pow (@Nat.lt_two_pow_self wideTags).le
  have nativeRadix : 2^t ≤ 2^wideTags := Nat.pow_le_pow_right (by decide) nativeTags
  have ta := nativeRadix.trans wideRadix
  have key : keyBound S 1 t≤v := by
    apply le_trans _ wideKey
    unfold keyBound
    gcongr
  obtain ⟨am,nb⟩ := scalar_heap_bounds x (v:=v) arena
  change N≤v at nb
  change A.maxWidth+1≤v^4 at wire
  have res : 2^rem≤(x).motifs := by
    have nz : 0<N := Fintype.card_pos
    change 2^rem≤N*d*(2^rem)*2^t*d*(3*2^(k-2))
    calc
      2^rem ≤ N*d*(2^rem) := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t)).trans
        ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos s)).trans (Nat.le_mul_of_pos_right _ (by positivity)))
  have ks : keyBound S N t=N*keyBound S 1 t := by unfold keyBound;ring
  have sq : v*v<v^16 := by simpa only [pow_two] using Nat.pow_lt_pow_right one_lt_v (by decide : 2<16)
  have fifth : top≤v^5 := by
    calc
      _ ≤ v*(v^4) := Nat.mul_le_mul issue (by omega)
      _ = _ := by ring
  have capRoom : widthMultiplicity k d*A.maxWidth≤v^5 := by
    calc
      _ ≤ v*v^4 := Nat.mul_le_mul dem (by omega)
      _ = _ := by ring
  have linear : 1+2*(widthMultiplicity k d*A.maxWidth)+shrinkBaseBound T≤v^6 := by
    have base : v≤v^5 := Nat.le_self_pow (by decide) _
    have one : 1≤v^5 := Nat.pow_pos (by omega)
    calc
      _ ≤ 4*v^5 := by omega
      _ ≤ v*v^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have scale80 : 80≤v := (by decide : 80≤2^7).trans
    (Nat.pow_le_pow_right (by decide) ((by omega : 7≤u).trans (Nat.le_self_pow (by decide) _)))
  have family : (Q).motifs≤v := am
  have sc : 80*(Q).motifs*top^2≤v^12 := by
    calc
      _ ≤ v*v*(v^5)^2 := Nat.mul_le_mul (Nat.mul_le_mul scale80 family) (Nat.pow_le_pow_left fifth _)
      _ = _ := by ring
  change ShrinkOldCaps s rem (16*u^10) ∧ _
  refine ⟨⟨by rw [huge];omega,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals rw [huge]
  · exact co.trans_lt smallV
  · exact sl.trans_lt smallV
  · exact ta.trans_lt smallV
  · exact (res.trans am).trans_lt smallV
  · exact bun.trans_lt smallV
  · rw [ks]; exact (Nat.mul_le_mul nb key).trans_lt sq
  · exact (Nat.mul_le_mul nb ta).trans sq.le
  · exact tg.trans_lt smallV
  · exact pc.trans_lt smallV
  · exact tiles.trans smallV.le
  · exact linear.trans_lt (Nat.pow_lt_pow_right one_lt_v (by decide : 6<16))
  · exact fifth.trans_lt (Nat.pow_lt_pow_right one_lt_v (by decide : 5<16))
  · exact sc.trans_lt (Nat.pow_lt_pow_right one_lt_v (by decide : 12<16))

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open CompressorPacking Native Native.ShrinkStage NavigationDirectory
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (B : Block F)

theorem cursor_width_word_space {u rem low off slots e : ℕ} (hu : e+40≤u) (lowBound : low≤u^10)
    (growth : B.widthBase≤u) (slotsFit : off*slots*3≤u^e) (hk : 2≤(B.repeat (u^8)).charge+rem) :
    ((B.cursorState hk low off slots).maxWidth+1)*B.widthBase^(u^8) ≤ (2^(u^10))^4 := by
  have pos : 0<u := by omega
  have width : (B.cursorState hk low off slots).maxWidth≤2^low*u^e :=
    (B.cursorState hk low off slots).maxWidth_le fun j=>by rw [B.cursorState_width];exact Nat.mul_le_mul_left _ slotsFit
  have poly:=width_pow_le_two_pow_sq (by omega : e≤u)
  have old : 2^low*u^e≤2^(low+u^2) := by rw [pow_add];gcongr
  have p:=Nat.two_pow_pos (low+u^2)
  have bigger : (B.cursorState hk low off slots).maxWidth+1≤2^(low+u^2+1) := by
    rw [pow_succ 2 (low+u^2)]
    omega
  have repeats : B.widthBase^(u^8)≤2^(u^9) := by
    calc
      _ ≤ (2^u)^(u^8) := Nat.pow_le_pow_left (growth.trans Nat.lt_two_pow_self.le) _
      _ = _ := by rw [←pow_mul,pow_succ u 8,Nat.mul_comm u]
  have q := Nat.pow_le_pow_right pos (by decide : 2≤10)
  have q' := Nat.pow_le_pow_right pos (by decide : 9≤10)
  have q0 : 0<u^10 := Nat.pow_pos pos
  exact (Nat.mul_le_mul bigger repeats).trans (by
    rw [←pow_add,←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega)

private theorem member_le_sum {a : ℕ} {l : List ℕ} (h : a∈l) : a≤l.sum :=
  List.le_sum_of_mem h

theorem shrink_heap_word_space {u rem low : ℕ} (hu : 40≤u) (levels : B.levels+1≤u) (factor : B.allocations.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (x : Dimensions) (actual : Stage.shrink x∈(B.repeat (u^8)).directory rem ((B.repeat (u^8)).charge+rem)) :
    (Stage.shrink x).heapWords≤2^(u^10) := by
  have total:=B.cursor_heap_space hu levels factor half depth
  have here:=member_le_sum (List.mem_map.mpr ⟨_,actual,rfl⟩ :
      (Stage.shrink x).heapWords∈(((B.repeat (u^8)).directory rem ((B.repeat (u^8)).charge+rem)).map Stage.heapWords))
  have up:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le (u^10) (u^4))
  omega

theorem shrink_history_word_space {u rem low off slots e : ℕ} (hu : e+40≤u) (lowBound : low≤u^10)
    (growth : B.widthBase≤u) (slot : off*slots*3≤u^e) (hk : 2≤(B.repeat (u^8)).charge+rem)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History) (a : ℕ)
    (actual : a∈((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).readStages (fun X=>X.maxWidth) h) :
    a+1≤(2^(u^10))^4 :=
  (B.history_maxWidth _ _ _ h a actual).trans (B.cursor_width_word_space hu lowBound growth slot hk)

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
