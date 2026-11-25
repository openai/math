import OAI.Computability.NearSquareRoot.PhysicalWalshTotalFibres
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRoute

/-! # Shape-dependent cost bounds for unpriced whole-axis Walsh passes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorRoute

open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode

/-- A complete row and its transformed row both have a shape-determined
physical extent. Thus a total flat pass can be charged to the shape alone. -/
theorem Flat.priceByShape {a W : ℕ} {F : (s : Shape) → Data s → Data s} {c : Cmd}
    (h : PhysicalWalshCompileInterior.Ends c (fun t : XorInput W =>
      send (Header.wire (a+1) t.shape, laneFlat (a+1) W t.shape t.row))
      (fun t => send (laneFlat (a+1) W t.shape (F t.shape t.row)))) :
    ∃ b : Shape → ℕ, Flat (a:=a) (W:=W) b b F c := by
  obtain ⟨_,_,run⟩ := h
  apply run.priceBy XorInput.shape (fun s => Header.scale (a+1) s + 16*allowance (a+1) 1 s + 2)
  intro t
  have row (v : Data t.shape) : size (laneFlat (a+1) W t.shape v) ≤ 16*allowance (a+1) 1 t.shape+1 :=
    SwapPrefix.stream_cost (a+1) W 1 t.shape _ v (SwapPrefix.length_le ..)
  have hin := row t.row
  have hout := row (F t.shape t.row)
  change max (Header.scale (a+1) t.shape+size (laneFlat (a+1) W t.shape t.row)+1)
    (size (laneFlat (a+1) W t.shape (F t.shape t.row))) ≤ _
  omega

end PhysicalWalshCompileXorRoute

namespace PhysicalWalshCompileXorPacket

open IntegerMultiplication Code PhysicalWalshNode

/-- A reached XOR command with unrestricted execution costs has a common
clock and arena for each shape, regardless of its row contents. -/
theorem priceByShape {a W : ℕ} {g : Fin (a+1) × Fin (a+1)} {c : Cmd}
    (h : FrontDispatch.flatTotal (W:=W) g c) : ∃ b : Shape → ℕ, FlatRuns (W:=W) b b g c :=
  PhysicalWalshCompileXorRoute.Flat.priceByShape (F:=PhysicalWalshNode.xor a g) h

end PhysicalWalshCompileXorPacket

end NearSquareRoot
end Computability
end OAI
