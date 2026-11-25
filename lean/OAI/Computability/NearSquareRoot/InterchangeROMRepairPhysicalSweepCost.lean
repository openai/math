import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepConcrete

/-! # Local work and the coefficient of recursive costs in the spectral leaf -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress GeneratorSyntax LoomRegisters InterchangeBatch
open InterchangeROMRepair.Physical (Allowance)

def wireSize (h u v mark tags out : Tree) : ℕ :=
  h.count + u.count + v.count + mark.count + tags.count + out.count + 1

/-- The copies, projections and collection frames add a linear scan on the six occupied trees. -/
theorem wires (h u v mark tags out : Tree) (am ab ap al : Allowance) :
    let a := oneCost h u v mark tags out am ab ap al
    let w := 2000 * wireSize h u v mark tags out
    a.time ≤ am.time + ab.time + ap.time + al.time + w ∧
    a.cap ≤ am.cap + ab.cap + ap.cap + al.cap + w ∧
    a.depth ≤ am.depth + ab.depth + ap.depth + al.depth + w := by
  simp only [oneCost,wireSize,joinCost,projectCost,scanCost,cost2,cost3,seriesClock,costSum,
    two,three,Option.elim',Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Task.forest_cons,Task.forest_nil,id_eq,Tree.count]
  omega

noncomputable def pivotLocal (b n j : ℕ) (h : Header) (hdr u v : Tree) : ℕ :=
  headerTime (numericSpec b n [(j,j)]) h pivotK pivotDegree +
    110 * ((Task.forest id [hdr]).count + 1) + (send h).count + u.count + v.count + 10

/-- Recursive time, maximum resident data, and return depth each appear once. -/
theorem pivot_budget (b n j : ℕ) (h : Header) (hdr u v : Tree) (a : Allowance) :
    let p := pivotCost b n j h hdr u v a
    let k := pivotLocal b n j h hdr u v
    p.time ≤ a.time + k ∧ p.cap ≤ a.cap + k ∧ p.depth ≤ a.depth + k := by
  simp only [pivotCost,pivotLocal,dataSpace,returnSpace,Tree.count,Task.forest_cons,Task.forest_nil,id_eq]
  omega

private theorem code_le (p : ℕ) (x : ZMod (p+1)) :
    (InterchangeROMTable.numeral x.val).count ≤ 2*p+1 := by
  change size (tally x.val) ≤ _
  rw [size_tally,tally_length]
  have h := ZMod.val_lt x
  omega

theorem packed_trees {A D : Type} (rows : Series A) (payload : Series D) (width p : ℕ)
    (hw : payload.count ≤ width) (tag : A → Ordering) (x : A → D → ZMod (p+1)) :
    let m := stripe rows fun a => SweepTable.mark (tag a)
    let t := Physical.Broadcast.output rows (fun _ => payload) (fun a => SweepTable.mark (tag a))
    let z := row rows payload x
    let Q := (2*p+11)*(rows.count*(width+1)+1)
    (Task.forest id [m,z]).count + t.count + 1 ≤ Q ∧ m.count ≤ Q ∧ t.count ≤ Q ∧ z.count ≤ Q := by
  have small (a : A) : (SweepTable.mark (tag a)).count ≤ 3 := by
    cases tag a <;> decide
  have h := Physical.Broadcast.cells rows (fun _ => payload) (fun a => SweepTable.mark (tag a))
    (fun a d => InterchangeROMTable.numeral (x a d).val) width 3 (2*p+1) (fun _ => hw)
    small (fun a d => code_le p (x a d))
  have k : 3+(2*p+1)+7 = 2*p+11 := by omega
  rw [k] at h
  refine ⟨h,?_⟩
  simp only [Physical.Broadcast.input,Task.forest_cons,Task.forest_nil,id_eq,Tree.count] at h
  change _ + ((_ : ℕ) + 1 + 1) + 1 + _ + 1 ≤ _ at h
  exact ⟨by omega, by omega, by exact (by dsimp [row]; omega)⟩

/-- The physical local overhead is linear in the number of occupied record cells, plus the
header setup. Its radix-dependent coefficient is independent of the field width. -/
noncomputable def localCharge (b n j p half : ℕ) (inv : Bool) (h : Header) (hdr : Tree)
    (rows width : ℕ) :=
  let cells := rows*(width+1)+1
  let Q := (2*p+11)*cells
  let T := headerTime (numericSpec b n [(j,j)]) h pivotK pivotDegree
  let M := maskTime b n j h rows
  M + Physical.Broadcast.factor*Q + SweepTable.factor p half inv*cells +
    T + 110*(hdr.count+3) + 2*Q + (send h).count + 10 +
    2000*((send h).count+5*Q+1)

variable {I J D : Type} [DecidableEq J] {b n : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ) (pay : I → Series D)
  (j : J) (p half : ℕ) (inv : Bool)
  (x : (i : I) → domain (J:=J) (b:=b) P G B f i → D → ZMod (p+1)) (i : I)

/-- A recursive caller pays its own time/data/depth once; every other term is explicit. -/
theorem native_cost_le (hw : (pay i).count ≤ l i) (ac : Allowance) :
    let q := request ord P G B f l pay j p x i
    let a := nativeCost ord P G B f l pay j p half inv x i ac
    let k := localCharge b n (ord j) p half inv (header (f i) (P i) (G i) (B i))
      q.header (countRows (b:=b) ord P G B f i) (l i)
    a.time ≤ ac.time + k ∧ a.cap ≤ ac.cap + k ∧ a.depth ≤ ac.depth + k := by
  intro q a k
  let h := header (f i) (P i) (G i) (B i)
  let rows := layoutRows (b:=b) ord P G B f i
  let v (k : domain (J:=J) (b:=b) P G B f i) := x i (InterchangeSpectralRequest.swapAt j k)
  let y (k : domain (J:=J) (b:=b) P G B f i) (d : D) :=
    InterchangeSpectralRequest.advance inv (half : ZMod (p+1)) j (fun k => x i k d) k
  let u := row rows (pay i) (x i)
  let v' := row rows (pay i) v
  let y' := row rows (pay i) y
  let tag := direction (b:=b) P G B f j i
  let m := stripe rows fun a => SweepTable.mark (tag a)
  let t := Physical.Broadcast.output rows (fun _ => pay i) fun a => SweepTable.mark (tag a)
  let Q := (2*p+11)*(rows.count*(l i+1)+1)
  let Z := SweepTable.factor p half inv*(rows.count*(l i+1)+1)
  let T := headerTime (numericSpec b n [((ord j).val,(ord j).val)]) h pivotK pivotDegree
  let M := maskTime b n (ord j) h rows.count
  let F := Physical.Broadcast.factor
  let L := (Task.forest id [m,u]).count+t.count+1
  let z := pivotCost b n (ord j) h q.header u v' ac
  have bounds : L ≤ Q ∧ m.count ≤ Q ∧ t.count ≤ Q ∧ u.count ≤ Q :=
    packed_trees rows (pay i) (l i) p hw tag (x i)
  have hv : v'.count ≤ Q := (packed_trees rows (pay i) (l i) p hw tag v).2.2.2
  have hy : y'.count ≤ Q := (packed_trees rows (pay i) (l i) p hw tag y).2.2.2
  have hm : F*L ≤ F*Q := Nat.mul_le_mul_left _ bounds.1
  have w := wires (send h) u v' m t y' (uniformCost M) (uniformCost (F*L)) z (uniformCost Z)
  change a.time ≤ M + F*L + z.time + Z + 2000*wireSize (send h) u v' m t y' ∧
    a.cap ≤ M + F*L + z.cap + Z + 2000*wireSize (send h) u v' m t y' ∧
    a.depth ≤ M + F*L + z.depth + Z + 2000*wireSize (send h) u v' m t y' at w
  let K := T + 110*(q.header.count+3) + 2*Q + (send h).count + 10
  have pk : pivotLocal b n (ord j) h q.header u v' ≤ K := by
    change T + 110*((Task.forest id [q.header]).count+1)+(send h).count+u.count+v'.count+10 ≤ _
    simp only [K,Task.forest_cons,Task.forest_nil,id_eq,Tree.count]
    omega
  have pp := pivot_budget b n (ord j) h q.header u v' ac
  change z.time ≤ _ ∧ z.cap ≤ _ ∧ z.depth ≤ _ at pp
  have bw : wireSize (send h) u v' m t y' ≤ (send h).count+5*Q+1 := by unfold wireSize; omega
  change a.time ≤ ac.time + (M + F*Q + Z + T + 110*(q.header.count+3) + 2*Q + (send h).count + 10 + 2000*((send h).count+5*Q+1)) ∧
    a.cap ≤ ac.cap + (M + F*Q + Z + T + 110*(q.header.count+3) + 2*Q + (send h).count + 10 + 2000*((send h).count+5*Q+1)) ∧
    a.depth ≤ ac.depth + (M + F*Q + Z + T + 110*(q.header.count+3) + 2*Q + (send h).count + 10 + 2000*((send h).count+5*Q+1))
  dsimp only [K] at pk
  omega

end InterchangeROMRepair.Sweep

end NearSquareRoot
end Computability
end OAI
