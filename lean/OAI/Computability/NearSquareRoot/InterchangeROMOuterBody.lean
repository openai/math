import OAI.Computability.NearSquareRoot.InterchangeROMOuterNative

/-! # The mixed ledger of the selected native outer stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
  NearSquareRoot.InterchangeROMRecursion NearSquareRoot.InterchangeROMExpose NearSquareRoot.InterchangeSpectralFibre

/-- Fuse two local framing passes, the small-row cubic call ledger, and the
actual full-row reserve command. The complete run obeys the padded-volume
rational factor and uses the chosen literal code under its caller's binder. -/
theorem body : ∃ k A : ℕ, ∀ {b p a m l n : ℕ} (q : Request b) (hb : 2 ≤ b)
    (hn : 0 < a+m+a) (hw : a+m+a < q.width) (_ : 3 ≤ l*n) (_ : l*n ≤ b)
    (ok : Packed (@value (p+1)) q) (parent enter main leave : Cmd) (entry middle exitTime limit : ℕ),
    let i := InterchangeROMStars.frame a m q hb hn hw ok.1
    let tag := send (centerHeader i)
    let header := send (groupedHeader i (l*n))
    let op : key i (l*n) → key i (l*n) := swapMain (OuterReserves.main a m)
    let valid := Packed (b:=b) (@value (p+1))
    let src := Tree.fork tag (centerPayload i)
    let dst := Tree.fork tag (InterchangeROMStars.afterMain a m q hb hn hw ok.1)
    At parent enter (job b) [] [] src (.fork tag (.fork header (stream i (l*n) id))) entry 0 0 →
    (∀ x : tensor i p l n, ∃ sm : List (Request b), sm.length ≤ limit ∧
      (∀ y ∈ sm, valid y ∧ y.width=f i ∧ y.recordWidth=q.recordWidth ∧ y.rows.count=(groupedRows i (l*n)).count) ∧
      At parent main (job b) sm [] (cubic i x) (cubic i (permute x op)) middle 0 0) →
    At parent leave (job b) [] [] (.fork tag (.fork header (stream i (l*n) op))) dst exitTime 0 0 →
    ∃ sm fu : List (Request b),
      stepAccount valid (a+m+a) (((limit*BatchRows.groups b (l*n):ℕ):ℝ)/b+(2*a:ℕ)) q (sm++fu) ∧
      (∀ y∈sm, 3*y.rows.count ≤ 2*q.rows.count) ∧
      At parent (stage b a m enter main leave) (job b) sm fu src ((job b).reply q)
        (entry+(middle+100*(tag.count+1))+2+exitTime+2+
          InterchangeROMStars.coefficient A k b a m (2*(p+1)+3)*(localMass q k+1)+2)
        (InterchangeROMStars.reserve b a*(Nat.log 2 q.recordVolume+1)) 3 := by
  obtain ⟨k,A,stars⟩ := InterchangeROMStars.run_priced
  refine ⟨k,A,?_⟩
  intro b p a m l n q hb hn hw hW smallBank good parent enter main leave entry middle exitTime limit
    i tag header op valid src dst bank compute unbank
  obtain ⟨x,enc⟩ := tensor_input i p l n good
  obtain ⟨sm,countSmall,smallOK,run⟩ := compute x
  obtain ⟨fu,countFull,fullOK,starRun⟩ := stars q hb hn hw good.1 (record (@value (p+1)) q.recordWidth)
    good.2.2 (2*(p+1)+3) (fun j => record_size (good.2.2 j))
  have fullFacts (y : Request b) (hy : y∈fu) :
      valid y ∧ y.width = f i ∧ y.recordWidth = q.recordWidth ∧ y.rows.count=q.rows.count := by
    obtain ⟨ok,width,recw,rows,cells⟩ := fullOK y hy
    refine ⟨⟨ok,by rw [width]; exact lanes_pos hn hw,?_⟩,width,recw,rows⟩
    exact recw.symm ▸ cells
  obtain ⟨paid,shrink⟩ := step_account i (l*n) limit (2*a) hW smallBank valid
    sm fu countSmall countFull.le smallOK fullFacts
  refine ⟨sm,fu,paid,shrink,?_⟩
  have left : cubic i x = .fork header (stream i (l*n) id) := enc id
  have right := enc op
  rw [left,right] at run
  have under := run.under_header tag
  have first := bank.sequence under
  have next := first.sequence unbank
  have all := next.sequence (starRun parent)
  simpa only [stage,List.nil_append,List.append_nil,Nat.max_self,Nat.zero_max, show max (max (max (0+1) 0+1) 0+1) 1 = (3:ℕ) by decide]
    using all

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
