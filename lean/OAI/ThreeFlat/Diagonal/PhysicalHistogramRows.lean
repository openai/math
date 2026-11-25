import OAI.ThreeFlat.Diagonal.PhysicalBlockLength
import OAI.ThreeFlat.Diagonal.PhysicalChargeFactor
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OAI
/-! # Histogram rows in the public physical stage directory -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

namespace Program

def factors : {s : ℕ} → Program F s → List ℕ
  | _, .done _ => []
  | _, .shrink s _ _ _ tail => shrinkChargeFactor s :: factors tail
  | _, .refresh s _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => (2*2^s+2) :: factors tail

private theorem histogram_density (x : CompressorPacking.Native.ShrinkStage.Dimensions) :
    x.motifs ≤ 3*x.oldDegree*x.originalSites := by
  open CompressorPacking.Native.ShrinkStage in
    unfold Dimensions.motifs Dimensions.upperBlocks Dimensions.oldEdges Dimensions.originalSites Dimensions.originalLanes
  have h : 2^(x.colorBits-2) ≤ 2^x.colorBits := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  calc
    _ ≤ (x.oldBase*x.oldDegree*x.residual*x.tagRadix*x.oldDegree)*(3*2^x.colorBits) := by gcongr
    _ = _ := by ring

/-- Count the physical rows in the exact public histogram sequence. The bound uses the
same fixed degree constants as the quantitative charge proof, on the original site array. -/
theorem histogram_rows {s : ℕ} (P : Program F s) (K : ℕ) (bounds : ∀ a∈P.factors,a≤K)
    (rem v : ℕ) :
    ((P.directory rem v).map NavigationDirectory.Stage.motifs).sum ≤
      P.length*K*(v*2^(P.charge+rem)) := by
  induction P generalizing v with
  | done s => simp [length,directory]
  | shrink s t T small tail ih =>
    let d := 2^s
    let tag := 2^CompressorPacking.tagBits d
    let x : CompressorPacking.Native.ShrinkStage.Dimensions := ⟨v,d,2*d+1,tag,2^(tail.charge+rem),2^t⟩
    have areas := shrink_positions s t (tail.charge+rem) v
    have orig : x.originalSites=v*2^(shrinkCharge s+tail.charge+rem) := by
      simpa only [Nat.add_assoc] using areas.1
    have out : (v*tag)*2^(tail.charge+rem) ≤ x.originalSites := by
      have step : ((v*tag)*2^(tail.charge+rem))*4≤x.originalSites := areas.2
      exact (Nat.le_mul_of_pos_right _ (by decide : 0<4)).trans step
    have cap := bounds _ List.mem_cons_self
    have hd : 3*x.oldDegree≤K := by
      change shrinkChargeFactor s≤K at cap
      change 3*2^s≤K
      unfold shrinkChargeFactor at cap
      omega
    have h0 := (histogram_density x).trans (Nat.mul_le_mul_right _ hd)
    have h1 := ih (fun a ha=>bounds a (List.mem_cons_of_mem _ ha)) (v*tag)
    change x.motifs+_ ≤ (tail.length+1)*K*(v*2^(shrinkCharge s+tail.charge+rem))
    rw [←orig,Nat.succ_mul,Nat.add_mul]
    exact (Nat.add_le_add h0 (h1.trans (Nat.mul_le_mul_left _ out))).trans_eq (Nat.add_comm ..)
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let m := 2^s
    let sites := v*2^(s+tail.charge+rem)
    have orig : (v*m)*2^(tail.charge+rem)=sites := by
      simp only [sites,m,Nat.add_assoc,pow_add]; ring
    have sub : v*2^(tail.charge+rem) ≤ sites :=
      (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right v (Nat.two_pow_pos s))).trans_eq orig
    have cap := bounds _ List.mem_cons_self
    change 2*2^s+2≤K at cap
    have h0 := sub.trans (Nat.le_mul_of_pos_left sites (by omega : 0<K))
    have h1 := ih (fun a ha=>bounds a (List.mem_cons_of_mem _ ha)) (v*m)
    change v*2^(tail.charge+rem)+_ ≤ (tail.length+1)*K*sites
    rw [orig] at h1
    rw [Nat.succ_mul,Nat.add_mul]
    exact (Nat.add_le_add h0 h1).trans_eq (Nat.add_comm ..)

theorem factors_cast {s t : ℕ} (e : s=t) (P : Program F s) :
    (e ▸ P : Program F t).factors=P.factors := by cases e; rfl

end Program

namespace Block

variable (B : Block F) in
def shrinkFactors : ℕ → ℕ → List ℕ
  | 0,_ => []
  | n+1,i => shrinkChargeFactor (B.exponent i) :: shrinkFactors n (i+1)

def costFactors (B : Block F) :=
  B.shrinkFactors B.levels 0 ++ [2*2^(B.exponent B.levels)+2]

theorem factors_shrinkPrefix (B : Block F) (n i : ℕ) (P : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i P).factors=B.shrinkFactors n i++P.factors := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [shrinkPrefix,Program.factors,ih,Program.factors_cast,
      shrinkFactors,List.cons_append]

theorem factors_prefix (B : Block F) (P : Program F (B.exponent 0)) :
    (B.prefix P).factors=B.costFactors++P.factors := by
  simp only [Block.prefix,factors_shrinkPrefix,Program.factors_cast,Program.factors,costFactors,
    List.append_assoc,List.cons_append,List.nil_append]

theorem factor_bound (B : Block F) (n a : ℕ) (ha : a∈(B.repeat n).factors) : a≤B.costFactors.sum := by
  have contains : a∈B.costFactors := by
    induction n with
    | zero => simp [Block.repeat,Program.factors] at ha
    | succ n ih =>
      rw [Block.repeat,B.factors_prefix,List.mem_append] at ha
      exact ha.elim id ih
  exact List.le_sum_of_mem contains

end Block

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
