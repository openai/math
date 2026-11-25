import OAI.Computability.NearSquareRoot.InterchangeROMBankWires
import OAI.Computability.NearSquareRoot.InterchangeBatchFrame

/-! # Native batch-frame calls to the compiled bank and unbank commands

The prefix view identifies a leading digit with the final coordinate of the
native prefix tape. It preserves the order of every record in each wing.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims

variable {I J : Type} {n b W : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Tape) (f : I → ℕ)

abbrev nativeRuler (k : ℕ) (i : I) :=
  ruler (BatchFrame.outer P i) (Series.natural k) (BatchFrame.tail (b:=b) ord G B f i)

theorem nativeRuler_eq (k : ℕ) (i : I) : nativeRuler (b:=b) ord P G B f k i =
    send (tally (room (P i)),tally k,tally (BatchFrame.tail (b:=b) ord G B f i).count) := by
  simp only [nativeRuler,ruler,BatchFrame.outer,Series.count_natural,space]

abbrev rawRecord (k : ℕ) (i : I) (v : BatchFrame.Value (J:=J) (b:=b) P G B f k) :=
  v i ∘ (BatchFrame.view (b:=b) ord P G B f k i).cast

theorem stripe_raw (k : ℕ) (i : I) (v : BatchFrame.Value (J:=J) (b:=b) P G B f k) :
    stripe (BatchFrame.rows (b:=b) ord P G B f k i) (v i) =
      flat (BatchFrame.outer P i) (Series.natural k) (BatchFrame.tail (b:=b) ord G B f i)
        (rawRecord ord P G B f k i v) :=
  (BatchFrame.view (b:=b) ord P G B f k i).packet _

theorem packet_raw (i : I)
    (v : Fin W → BatchFrame.Value (J:=J) (b:=b) P G B f (BatchRows.groups b W)) :
    let q := BatchRows.groups b W
    BatchFrame.packet ord P G B f v i = stripe (Series.natural W) (fun u =>
      flat (BatchFrame.outer P i) (Series.natural q) (BatchFrame.tail (b:=b) ord G B f i)
        (rawRecord ord P G B f q i (v u))) := by
  apply congrArg (stripe (Series.natural W))
  funext u
  exact stripe_raw ord P G B f _ i (v u)

theorem padded_raw (i : I) (hb : 0 < b) (v : BatchFrame.Value (J:=J) (b:=b) P G B f b) :
    let q := BatchRows.groups b W
    let r := rawRecord ord P G B f b i v
    BatchFrame.packet ord P G B f (BatchFrame.padded (W:=W) P G B f hb v) i =
      stripe (Series.natural W) (fun u =>
        flat (BatchFrame.outer P i) (Series.natural q) (BatchFrame.tail (b:=b) ord G B f i)
          (fun z => r ((z.1.1,BatchRows.select hb u z.1.2),z.2))) := by
  dsimp only
  rw [packet_raw]
  apply congrArg (stripe (Series.natural W))
  funext u
  apply congrArg (stripe _)
  funext a
  rcases a with ⟨⟨x,d⟩,z⟩
  simp [BatchFrame.padded,BatchFrame.view,Adopt.split,rawRecord]

theorem gather_raw (i : I) (hW : 0 < W)
    (v : Fin W → BatchFrame.Value (J:=J) (b:=b) P G B f (BatchRows.groups b W)) :
    let q := BatchRows.groups b W
    let src (u : Fin W) := rawRecord ord P G B f q i (v u)
    stripe (BatchFrame.rows (b:=b) ord P G B f b i) (BatchFrame.gather P G B f hW v i) =
      flat (BatchFrame.outer P i) (Series.natural b) (BatchFrame.tail (b:=b) ord G B f i)
        (fun z => src (BatchRows.row hW z.1.2) ((z.1.1,BatchRows.group hW z.1.2),z.2)) := by
  dsimp only
  rw [stripe_raw]
  apply congrArg (stripe _)
  funext a
  rcases a with ⟨⟨x,d⟩,z⟩
  simp [BatchFrame.gather,BatchFrame.view,Adopt.split,rawRecord]

/-- Put native records into the literal row bank, with every padding digit
chosen by the frame's native selector. -/
theorem bank_run (i : I) (hp : 0 < (BatchFrame.outer P i).count)
    (ht : 0 < (BatchFrame.tail (b:=b) ord G B f i).count) (hb : 0 < b) (hW : 0 < W)
    (v : BatchFrame.Value (J:=J) (b:=b) P G B f b) :
    Run (bank b W) (bankTime b W) bankSpace
      ((nativeRuler (b:=b) ord P G B f b i).fork
        (stripe (BatchFrame.rows (b:=b) ord P G B f b i) (v i)))
      (BatchFrame.packet ord P G B f (BatchFrame.padded (W:=W) P G B f hb v) i) := by
  rw [padded_raw,stripe_raw]
  exact bankRaw_run _ _ hp ht hb hW _

/-- Merge any processed bank using the row and quotient belonging to each
genuine leading digit of the original native layout. -/
theorem unbank_run (i : I) (hp : 0 < (BatchFrame.outer P i).count)
    (ht : 0 < (BatchFrame.tail (b:=b) ord G B f i).count) (hb : 0 < b) (hW : 0 < W)
    (v : Fin W → BatchFrame.Value (J:=J) (b:=b) P G B f (BatchRows.groups b W)) :
    Run (unbank b W) (unbankTime b W) unbankSpace
      ((nativeRuler (b:=b) ord P G B f (BatchRows.groups b W) i).fork
        (BatchFrame.packet ord P G B f v i))
      (stripe (BatchFrame.rows (b:=b) ord P G B f b i) (BatchFrame.gather P G B f hW v i)) := by
  rw [gather_raw,packet_raw]
  exact unbankRaw_run _ _ hp ht hb hW _

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
