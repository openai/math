import OAI.Computability.NearSquareRoot.InterchangeROMFrontBound
import OAI.Computability.NearSquareRoot.KernelComputableAddress

/-! # The exact prelude contribution in the recursive request ledger -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFront

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMFrame
  NearSquareRoot.InterchangeROMRecursion

theorem computable_rate (F : Core) {X : Type} [Primcodable X] {p b n : X → ℕ}
    (hp : Computable p) (hb : Computable b) (hn : Computable n) :
    Computable fun x => rate F (p x) (b x) (n x) := by
  have pow : Computable₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    (KernelComputableAddress.primrec_pow Primrec.fst Primrec.snd).to₂.to_comp
  have spec := Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) hb)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) hn)) (Computable.const 3)
  have bytes := Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) hp)
    (Computable.const 7)
  have powA := pow.comp (Primrec.nat_add.to_comp.comp (pow.comp hb hn) (Computable.const 1))
    (Computable.const F.degree)
  have powB := pow.comp (Primrec.nat_add.to_comp.comp spec (Computable.const 2)) (Computable.const F.degree)
  have growth := Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp powA bytes) powB
  exact Primrec.nat_mul.to_comp.comp (Computable.const 16) (Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp spec bytes)
      (Primrec.nat_mul.to_comp.comp (Computable.const F.clock)
        (Primrec.nat_add.to_comp.comp growth (Computable.const 1)))) (Computable.const 10))

/-- Attach the single mixed-radix front end to either the center program or
the completed leaf. The active ledger, full-child parking and outstanding
return depth pass through this wrapper exactly. -/
theorem Core.node (F : Core) (p : ℕ) [NeZero p] (i : Input) (stage : Cmd)
    (sm fu : List (Request i.b)) (good : Request.Packed (@digit p) i.req)
    (work park returns : ℕ)
    (chosen : At (InterchangeROMFrame.node F.cmd stage i.b i.n)
      (bif decide i.stage then stage else .pass) (Request.job i.b) sm fu i.middle
      ((Request.job i.b).reply i.req) work park returns) :
    At (InterchangeROMFrame.node F.cmd stage i.b i.n) (InterchangeROMFrame.node F.cmd stage i.b i.n)
      (Request.job i.b) sm fu ((Request.job i.b).issue i.req) ((Request.job i.b).reply i.req)
      (rate F p i.b i.n * localMass i.req (F.degree+1) + work) park returns := by
  have h := chosen.node (t:=F.clock*(Input.scale.work F.degree i+1)) (fun env deck => by
    have op := F.run i (InterchangeROMFrame.node F.cmd stage i.b i.n::env) deck
    simpa only [Input.result_eq,Input.query] using op)
  apply h.mono _ le_rfl le_rfl
  calc
    _ = (5*(literal i.b i.n).count + F.clock*(Input.scale.work F.degree i+1) +
      ((Request.job i.b).issue i.req).count + i.middle.count + 20) + work := by ring
    _ ≤ _ := Nat.add_le_add_right (rate_bound F p i good) work

end InterchangeROMFront

end NearSquareRoot
end Computability
end OAI
