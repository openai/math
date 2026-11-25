import OAI.Computability.NearSquareRoot.InterchangeRequestHeader
import OAI.Computability.NearSquareRoot.InterchangeLeaf
import OAI.Computability.NearSquareRoot.InterchangeProgram

/-!
# Closing the literal recursive interchange on sufficiently wide records

The local program is first compiled on *all* admissible internal requests.
Only after it supplies its polynomial degree do we restrict the recursive
job to a domain closed under the actual children in that program's ledger.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom

variable {b : ℕ}

abbrev Internal (valid : Request b → Prop) (n : ℕ) :=
  {a : Subtype valid // n < a.val.width}

abbrev internalRequest {valid : Request b → Prop} {n : ℕ} (x : Internal valid n) := x.val.val

def Thick (k : ℕ) (a : Request b) := (Nat.log 2 a.rows.count + 1) ^ k ≤ a.recordWidth + 1

abbrev ThickRequest (valid : Request b → Prop) (k : ℕ) :=
  {a : Request b // valid a ∧ Thick k a}

def stepAccount (valid : Request b → Prop) (n : ℕ) (θ : ℝ)
    (a : Request b) (l : List (Request b)) :=
  (∀ y ∈ l, valid y ∧ y.width = lanes n a.width ∧ y.recordWidth = a.recordWidth ∧
    y.rows.count ≤ a.rows.count) ∧
  (l.map (fun y => (y.rows.count : ℝ))).sum ≤ θ * a.rows.count

theorem thick_child {a y : Request b} {k : ℕ} (h : Thick k a)
    (hw : y.recordWidth = a.recordWidth) (hc : y.rows.count ≤ a.rows.count) : Thick k y := by
  unfold Thick at *
  rw [hw]
  exact (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.log_mono_right hc)) _).trans h

private theorem thick_mass {I : Type} (xs : I → Request b) (hb : 2 ≤ b) (k : ℕ)
    (ok : ∀ i, Admissible (xs i)) (fat : ∀ i, Thick k (xs i)) (i : I) :
    mass (regime xs) (fun i => (xs i).rows.count) (fun i => (xs i).recordWidth) k i ≤
      (((2*b+9)^k + 1 : ℕ) : ℝ) * (xs i).recordVolume := by
  let x := xs i
  have head := x.header_count_log hb (ok i)
  have hsize : x.header.count + 1 ≤ (2*b+9)*(Nat.log 2 x.rows.count+1) := by
    rw [show 2*b+9=2*b+8+1 by omega,Nat.add_mul,Nat.one_mul]
    omega
  have hk := Nat.pow_le_pow_left hsize k
  rw [mul_pow] at hk
  have d := hk.trans (Nat.mul_le_mul_left _ (fat i))
  change (x.header.count+1)^k ≤ (2*b+9)^k * (x.recordWidth+1) at d
  change (x.rows.count : ℝ) * ((x.recordWidth : ℝ) + (x.header.count + 1 : ℝ)^k) ≤ _
  exact_mod_cast (show x.rows.count * (x.recordWidth + (x.header.count+1)^k) ≤
      ((2*b+9)^k + 1) * x.recordVolume by
    change _ ≤ _ * (x.rows.count * (x.recordWidth+1))
    calc
      _ ≤ x.rows.count * ((2*b+9)^k * (x.recordWidth+1) + (x.recordWidth+1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring)

private theorem ledger_tunnel {I X Y : Type} {o : Oracle X} {w v : I → ℝ}
    {calls : I → List X} {p q : I → Tree} (embed : Y → X) (ledger : I → List Y)
    (heq : ∀ i, (ledger i).map embed = calls i)
    (h : Tunnel o w calls p q) (hpos : ∀ i, 1 ≤ v i)
    (C : ℕ) (bound : ∀ i, w i ≤ (C:ℝ) * v i) :
    Tunnel ⟨o.fare ∘ embed, o.query ∘ embed, o.reply ∘ embed⟩ v ledger p q := by
  obtain ⟨_, cmd, K, run⟩ := h
  refine ⟨hpos,cmd,K*C,fun i parent env D child r => ?_⟩
  have caller y (hy : y ∈ calls i) : Acc (parent :: env) parent (o.query y) (o.reply y) ((D:ℝ)*o.fare y) := by
    rw [← heq i] at hy
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
    exact child z hz
  have e := run i parent env D caller r
  refine e.mono ?_
  rw [Oracle.reserve, ← heq i, List.map_map]
  apply add_le_add_left
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (bound _) (by positivity)

private theorem sum_volume (valid : Request b → Prop) {n : ℕ} {θ : ℝ} {x : Request b}
    {l : List (Request b)} (h : stepAccount valid n θ x l) :
    (l.map (fun y => (y.recordVolume : ℝ))).sum ≤ θ * x.recordVolume := by
  have eq : l.map (fun y => (y.recordVolume : ℝ)) =
      l.map (fun y => (y.rows.count : ℝ) * (x.recordWidth+1 : ℕ)) := by
    apply List.map_congr_left
    intro y hy
    simp only [recordVolume, Nat.cast_mul, (h.1 y hy).2.2.1]
  rw [eq, List.sum_map_mul_right]
  change _ ≤ θ * ((x.rows.count * (x.recordWidth+1) : ℕ) : ℝ)
  rw [Nat.cast_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h.2 (by positivity)

set_option maxHeartbeats 350000 in
/-- A single compiled command realizes every thick request. The thickness
exponent is chosen from the unfiltered internal program. The leaf uses the
bounded-width tape permutation directly. The account charges repeated child
calls with their full multiplicities. -/
theorem close_fat_recursion (valid : Request b → Prop) (hb : 2 ≤ b)
    (ok : ∀ a, valid a → Admissible a) (positive : ∀ a, valid a → 0 < a.width)
    (data : Manifest _ (fun a : Subtype valid => a.val.recordWidth) (fun a => a.val.contents))
    (m n : ℕ) (α θ : ℝ) (hm : 1 < m) (hmn : m ≤ n) (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ : θ < (m:ℝ)^α)
    (step : ∃ uses : Internal valid n → List (Request b),
      (∀ x, stepAccount valid n θ x.val.val (uses x)) ∧
      Quest (job b) (regime internalRequest) (fun x => x.val.val.rows.count)
        (fun x => x.val.val.recordWidth) uses ((job b).issue ∘ internalRequest)
        ((job b).reply ∘ internalRequest)) :
    ∃ k : ℕ, Sized (fun x : ThickRequest valid k => (x.val.recordVolume : ℝ) * (x.val.width : ℝ)^α)
      (fun x => (job b).issue x.val) (fun x => (job b).reply x.val) := by
  classical
  obtain ⟨uses, law, quest⟩ := step
  obtain ⟨k, run⟩ := quest.eligible
  let X := ThickRequest valid k
  let xs (x : X) := x.val
  let S := {x : X // n < (xs x).width}
  let parent (q : S) : Internal valid n := ⟨⟨q.val.val,q.val.property.1⟩,q.property⟩
  let small (q : S) (z : {y // y ∈ uses (parent q)}) : X :=
    ⟨z.val,(law (parent q)).1 _ z.property |>.1,
      thick_child q.val.property.2 ((law (parent q)).1 _ z.property).2.2.1
        ((law (parent q)).1 _ z.property).2.2.2⟩
  let ledger (q : S) := (uses (parent q)).attach.map (small q)
  have imageLedger (q : S) : (ledger q).map xs = uses (parent q) := by
    simp [ledger,small,xs,List.map_map,Function.comp_def]
  have spec (q : S) (y : X) (hy : y ∈ ledger q) :=
    (law (parent q)).1 (xs y) (by rw [← imageLedger q]; exact List.mem_map_of_mem hy)
  let vol (x : X) : ℝ := (xs x).recordVolume
  have adm (x : X) := ok (xs x) x.property.1
  have ripe := ripe_volume xs hb adm (w:=vol) (fun x => by unfold vol; exact_mod_cast (xs x).rows_le_recordVolume)
  have stored := issue_volume xs hb adm
    (show Manifest _ _ _ from ⟨data.size.choose,fun x => data.size.choose_spec ⟨x.val,x.property.1⟩⟩)
  let o : Oracle (Request b) :=
    ⟨fun a => (a.recordVolume : ℝ) * (a.width : ℝ)^α,(job b).issue,(job b).reply⟩
  let sub (q : S) := xs q.val
  let w := mass (regime sub) (fun q => (sub q).rows.count) (fun q => (sub q).recordWidth) k
  have raw : Tunnel o w (fun q => uses (parent q)) ((job b).issue ∘ sub) ((job b).reply ∘ sub) :=
    (run o.fare).slide parent
  let oo : Oracle X := ⟨o.fare ∘ xs, o.query ∘ xs, o.reply ∘ xs⟩
  have localBound (q : S) : w q ≤ (((2*b+9)^k+1:ℕ):ℝ) * vol q.val :=
    thick_mass sub hb k (fun z => adm z.val) (fun z => z.val.property.2) q
  have middle : Tunnel oo (fun q : S => vol q.val) ledger ((job b).issue ∘ sub) ((job b).reply ∘ sub) :=
    ledger_tunnel (o:=o) xs ledger imageLedger raw (fun q => ripe.1 q.val) _ localBound
  let leaf := {x : X // (xs x).width ≤ n}
  let lx (x : leaf) := xs x.val
  have solid (i : leaf) : solidShape (lx i) :=
    ⟨fun d hd => (adm i.val d (List.mem_append_left _ (List.mem_append_left _ hd))).1,
     fun d hd => (adm i.val d (List.mem_append_left _ (List.mem_append_right _ hd))).1,
     fun d hd => (adm i.val d (List.mem_append_right _ hd)).1⟩
  have lf := bounded_leaf_task b n (by omega) lx solid (fun x => x.property)
  obtain ⟨C,hC⟩ := stored
  have ls := (Sized.natural lf).adapts (fun x : leaf => ripe.1 x.val) (C+1) (fun x => by
    have hc := hC x.val
    have hv := ripe.1 x.val
    change (((job b).issue (lx x)).count : ℝ) + 1 ≤ _
    change (((job b).issue (lx x)).count : ℝ) ≤ (C:ℝ)*vol x.val at hc
    push_cast
    linarith)
  have both := branch_tunnel xs n ripe ⟨C,hC⟩ ledger ls middle
  refine ⟨k,interchange_recursive_program (fun x : X => (xs x).width)
    (fun x => (xs x).recordVolume) (branch_ledger xs n ledger) _ _ m α θ hm hα
    (fun x => positive _ x.property.1) (fun x => by
      have h := ripe.1 x
      change (1 : ℝ) ≤ ((xs x).recordVolume : ℝ) at h
      exact (by exact_mod_cast h : 1 ≤ (xs x).recordVolume)) hθ ?_ ?_ both⟩
  · intro x y hy
    by_cases h : n < (xs x).width
    · have hy' : y ∈ ledger ⟨x,h⟩ := by simpa only [branch_ledger,h,↓reduceDIte] using hy
      rw [(spec ⟨x,h⟩ y hy').2.1]
      exact (Nat.mul_le_mul_left _ hmn).trans (lanes_mul_le _ _)
    · simp [branch_ledger,h] at hy
  · intro x
    by_cases h : n < (xs x).width
    · let q : S := ⟨x,h⟩
      have hsum := sum_volume valid (law (parent q))
      rw [← imageLedger q, List.map_map] at hsum
      simpa only [branch_ledger,h,↓reduceDIte,Function.comp_def] using hsum
    · simp only [branch_ledger,h,↓reduceDIte,List.map_nil,List.sum_nil]
      exact mul_nonneg hθ0 (Nat.cast_nonneg _)

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
