import OAI.Computability.NearSquareRoot.InterchangeROMLeafMasks
import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # A common physical leaf command for all radix and width parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeaf

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom InterchangeAddress InterchangeROMLeafMasks InterchangeROMLeafMasksShape

def payload {b : ℕ} (q : Request b) := stripe q.rows q.contents

theorem reply_size {b : ℕ} (q : Request b) : ((Request.job b).reply q).count = (payload q).count := by
  let sw := swapper (T:=IntegerMultiplication.Adic.Block b q.width) q.before q.between q.after_
  let e : Equiv.Perm _ := ⟨sw,sw,fun _ => rfl,fun _ => rfl⟩
  exact Controlled.stripe_count_perm q.rows e q.contents

theorem rows_le_size {b : ℕ} (q : Request b) : q.rows.count ≤ (payload q).count := by
  unfold payload
  rw [stripe_simple,Series.count,Task.forest_count]
  omega

def leafQuery {b : ℕ} (q : Request b) :=
  Tree.fork (.fork (send (tally b)) q.header) (payload q)

/-- The same program accepts every legal shape and radix. Its only
superlinear dependence is on the small field's cardinality, with an
additive descriptor cost independent of the sizes of individual records. -/
theorem universal_leaf : ∃ k : ℕ, Task
    (fun i : Instance => (i.D+1)^k * ((payload i.req).count+1) + (size (descriptor i.req)+1)^2)
    (fun i => leafQuery i.req) (fun i => (Request.job i.radix).reply i.req) := by
  obtain ⟨k,mask⟩ := Instance.bank
  have scan := mask.forget.left (fun i : Instance => payload i.req)
  have route := InterchangeROMColors.batch_program.forget.on (fun i : Instance => batch i.req)
  have actual : Task (fun i : Instance => (batch i.req).work)
      (fun i => Tree.fork (send ((batch i.req).colors.map (batch i.req).masks)) (payload i.req))
      (fun i => (Request.job i.radix).reply i.req) := by
    apply route.conform (fun _ => rfl) (fun i => ?_) (fun i => permuted _)
    exact congrArg (Tree.fork _) (original _)
  refine ⟨k+2,(scan.compose actual).bound 6 (fun i => ?_)⟩
  have total : (batch i.req).colors.length = i.D*i.D := by
    simp [batch,ranks,Instance.D]
  have volume : (batch i.req).volume = (payload i.req).count + (payload i.req).count + 1 := by
    change (send (batch i.req).values).count + (send (batch i.req).answer).count + 1 = _
    rw [original,permuted,reply_size]
    rfl
  have one : 0 < i.D + 1 := by omega
  have small := Nat.pow_le_pow_right one (by omega : k ≤ k+2)
  have pair := Nat.pow_le_pow_right one (by omega : 2 ≤ k+2)
  have N := rows_le_size i.req
  have l := Nat.mul_le_mul small (by dsimp only [Instance.N]; omega : i.N ≤ (payload i.req).count+1)
  have factor : i.D * i.D + 1 ≤ (i.D+1)^(k+2) := (by nlinarith : i.D*i.D+1 ≤ (i.D+1)^2).trans pair
  have banks := Nat.mul_le_mul_right (2*((payload i.req).count+1)) factor
  simp only [Instance.work,InterchangeROMColors.Batch.work,total,volume]
  nlinarith

end InterchangeROMLeaf

end NearSquareRoot
end Computability
end OAI
