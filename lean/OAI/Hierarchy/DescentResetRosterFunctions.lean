import OAI.Hierarchy.DescentCommonPalette

namespace OAI
/-! # Calendar sizes of the original reset cable roster -/
noncomputable section
namespace Hierarchy
open scoped Classical
namespace DescentResetCableSlots

/-- Common private-wire address bound used by both constructors of `privateWire`. -/
def cableCap {n h : ℕ} (board : NonlinearExpanders.Graph n h) (height : ℕ) :=
  max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(height+1))

end DescentResetCableSlots

namespace DescentResetLocalRoster
def rootSlots (r Y : ℕ) := 2^(r+1)+2^(r+1)*(Y+1)

noncomputable def rosterFactor {n d : ℕ} (board : NonlinearExpanders.Graph n d) (height : ℕ) :=
  let Y:=2^n
  let Q:=DescentResetCableSlots.cableCap board height
  3+4*(Y+2)*(Y+2^height+Q)

/-- Program size before any actor flags or external values have been read. -/
noncomputable def publicSlots {n d : ℕ} (board : NonlinearExpanders.Graph n d) (height k cap : ℕ) :=
  let Y:=2^n
  let roots:=rootSlots k Y
  2*(2^k*(2*cap))+(1+(2*(roots*(Y+2^height))+2*(roots*DescentResetCableSlots.cableCap board height)))

theorem same_slots {n n' d : ℕ} (A : NonlinearExpanders.Graph n d) (B : NonlinearExpanders.Graph n' d)
    (dim : n=n') (board : HEq A B) (h k cap : ℕ) : publicSlots A h k cap=publicSlots B h k cap := by
  subst n'
  rw [eq_of_heq board]

theorem same_factor {n n' d : ℕ} (A : NonlinearExpanders.Graph n d) (B : NonlinearExpanders.Graph n' d)
    (dim : n=n') (board : HEq A B) (h : ℕ) : rosterFactor A h=rosterFactor B h := by
  subst n'
  rw [eq_of_heq board]
end DescentResetLocalRoster
end Hierarchy
end

end OAI
