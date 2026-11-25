import OAI.Computability.NearSquareRoot.InterchangeROMStageJoin

/-! # Native packed tapes at movement boundaries -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM InterchangeROMStageTable Space

variable {g : Frame} (r : Realization g)

private noncomputable def fill (n d : ℕ) (x : r.Boundary n → Fin d → Tree) (v : Role) (j : ℕ) : Tree :=
  Function.extend (slot r n d) (fun z => x z.1 z.2) (fun _ => .atom false) (v,j)

private theorem fill_code (n d : ℕ) (x : r.Boundary n → Fin d → Tree) (v : r.Boundary n) (j : Fin d) :
    r.fill n d x (r.code n v) j.val = x v j :=
  (slot_injective r n d).extend_apply _ _ (v,j)

private theorem blocks_fill (n d : ℕ) (x : r.Boundary n → Fin d → Tree) :
    Task.forest id (blocks (bank g n) d (r.fill n d x)) = r.Tape n d x := by
  rw [← r.cells_map]
  simp only [fill_code]
  rfl

theorem execute_route_typed {n lanes : ℕ} {src : r.Boundary (n+1) → r.Boundary n}
    {mv : r.Boundary (n+1) → r.NativeMove} (ok : r.CorrectRoute n src mv)
    (impl : Frame.Move → Cmd) (hdr : Tree) (x : r.Boundary n → Fin lanes → Tree)
    (y : r.Boundary (n+1) → Fin lanes → Tree)
    (time : r.Boundary (n+1) × Fin lanes → ℕ) (S D : ℕ) (env : Env)
    (child : ∀ (b : r.Boundary (n+1)) (k : Fin lanes) rest base, DeckCap base rest →
      BoundedFits env (impl (r.operand (mv b))) (pile 0 (.fork hdr (x (src b) k)) rest)
        (pile 0 (y b k) rest) (time (b,k)) (base+S) D)
    (rest : Deck) (base : ℕ) (hbase : DeckCap base rest) :
    let v := Tree.fork hdr (r.Tape n lanes x)
    let w := Tree.fork hdr (r.Tape (n+1) lanes y)
    BoundedFits env (routeCommand impl (route g lanes n)) (pile 0 v rest) (pile 0 w rest)
      (((bank g (n+1)).length*lanes+2)*(160*(v.count+1)) + costSum time (r.cells (n+1) lanes))
      (base+170*(v.count+1)+w.count+S) (170*(v.count+1)+D) := by
  have h := r.execute_route ok impl hdr (r.fill n lanes x) (r.fill (n+1) lanes y) time S D env
    (fun b k rest base hb => by simpa only [fill_code] using child b k rest base hb)
    rest base hbase
  simpa only [packet,blocks_fill] using h

end InterchangeROMStage.Frame.Realization

end NearSquareRoot
end Computability
end OAI
