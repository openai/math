import OAI.Computability.BorderVNP.CubeISAHeaderSpellingCard
import OAI.Computability.BorderVNP.CubeISAHeaderInstallGeometry
import OAI.Computability.BorderVNP.CubeISALocalRowArena
import Mathlib.Data.Nat.Choose.Bounds

/-! # Word and address bounds of the native declaration decoder

The last compact cursor is determined by the length of the declaration in the
copied common spelling. The two dense tables begin after the whole copy. The
reservation for all ordered pair views bounds even the sum of arbitrary legal
claims, prior to the comparison with physical row lengths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube BorderVNP.Cube.Physical CubeHeaderInstall TeamContraction.JointHeader

/-- The decoder stops after the coordinate and the genuine upper-triangle
fields, exactly at the end of the declaration portion of the common header. -/
theorem decoderEnd_eq (stat : Inputs) (n saved : ℕ) (decl : Broadcast n stat.d stat.cap)
    (axes : stat.a = n+1) :
    (stat.decoder saved).start (stat.decoder saved).entries =
      saved+1+stat.profile+(DeclarationBits.spelling decl).length := by
  simp [HeaderDecode.Layout.start,HeaderDecode.Layout.entries,Inputs.decoder,
    DeclarationBits.fieldStart,axes,DeclarationBits.fieldsBefore_last,DeclarationBits.spelling_length,
    DeclarationBits.length,Nat.add_assoc]

/-- Static installation and the addressed extent of the common copy supply
every decoder width, counter, and disjointness condition. -/
theorem decoderFits_of_copy (stat : Inputs) (w n bits frame saved : ℕ)
    (geometry : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast n stat.d stat.cap)
    (axes : stat.a = n+1) (profile : stat.profile = geometry.length)
    (extent : saved+(padded (TeamContraction.JointHeader.spelling
      (geometry++DeclarationBits.spelling decl) claims) pad).length ≤ stat.header)
    (fit : stat.Fits w n bits frame) : HeaderDecode.Fits (stat.decoder saved) w := by
  have finish : (stat.decoder saved).start (stat.decoder saved).entries ≤ stat.header := by
    rw [decoderEnd_eq stat n saved decl axes,profile]
    simp [TeamContraction.JointHeader.padded,TeamContraction.JointHeader.spelling] at extent
    omega
  have bank := fit.bank
  change stat.header+13+2*stat.entries+stat.a < 2^w at bank
  refine ⟨by omega,fit.cap,Nat.clog_le_of_le_pow (by change stat.a ≤ 2^w; omega),
    Nat.clog_le_of_le_pow fit.cap.le,by change 0 < stat.a; omega,?_,?_,?_,?_,?_,?_,?_⟩
  · change stat.entries < 2^w
    omega
  · change stat.header+13+stat.entries+stat.entries ≤ 2^w
    omega
  · change stat.header+5 < 2^w
    omega
  · omega
  · left
    change stat.header+5 < stat.header+13+stat.entries
    omega
  · left
    change _ ≤ stat.header+13+stat.entries
    omega
  · right
    change _ ≤ stat.header+5
    omega

/-- An arbitrary column of legal claims fits before the native checker knows
whether those claims agree with the selectors. Each ordered pair view reserves
at least the declaration cap in the actual arena. -/
theorem columnSum_room (a : CubeArena.Layout) (w : ℕ) (high : a.stop < 2^w) :
    a.header.d*a.header.d*a.header.cap < 2^w := by
  have width : a.header.cap ≤ a.pairStride := by unfold CubeArena.Layout.pairStride; omega
  have h := Nat.mul_le_mul_left (a.header.d^2) width
  have ⟨_,_,_,_,eq,le⟩ := a.separated
  rw [pow_two] at h eq
  omega

/-- The packet bank covers all partial packet counts, even when a genuine
two-symbol choice is impossible. Ordered pair reservations cover the complete
selector prefix and exclusive declaration bound. -/
theorem staticFits_of_arena (a : CubeArena.Layout) (w frame : ℕ)
    (primary : frame+112 ≤ a.header.header) (alphabet : 0 < a.header.d)
    (stride : 0 < Cube.Tally.bankWidth a.n a.b a.h a.K a.s) (high : a.stop < 2^w) :
    a.header.Fits w a.n (Cube.Tally.selectorWidth a.n a.K a.h) frame := by
  let sq := a.header.d*a.header.d
  have sqpos : 0 < sq := Nat.mul_pos alphabet alphabet
  have ⟨_,_,_,_,views,cell⟩ := a.separated
  rw [pow_two] at views
  have viewsFit : sq*a.pairStride < 2^w := by dsimp [sq]; omega
  have pairPos : 0 < a.pairStride := by unfold CubeArena.Layout.pairStride; omega
  have pairFit : a.pairStride < 2^w :=
    (Nat.le_mul_of_pos_left a.pairStride sqpos).trans_lt viewsFit
  have ⟨bank,space,powers⟩ := arenaExtents a
  have stopFit : a.packetEnd < 2^w := by
    change a.packetEnd+8+a.h ≤ a.powerBase at space
    omega
  have bankFit := bank.trans_lt stopFit
  refine ⟨?_,bankFit,(Nat.le_mul_of_pos_right sq pairPos).trans_lt viewsFit,?_,?_,?_⟩
  · unfold Inputs.packetBase at bankFit
    omega
  · have ch : a.header.d.choose 2 ≤ sq := by
      simpa only [sq,pow_two] using Nat.choose_le_pow a.header.d 2
    have power := (Nat.pow_le_pow_left ch a.n).trans (Nat.pow_le_pow_right sqpos (Nat.le_succ a.n))
    have cap : max 1 ((a.header.d.choose 2)^a.n) ≤ sq^(a.n+1) :=
      max_le (pow_pos sqpos _) power
    have room := (Nat.mul_le_mul_left (2*a.header.blocks) cap).trans
      (Nat.le_mul_of_pos_right _ stride)
    have endEq : a.packetEnd = a.header.packetBase+
        (2*a.header.blocks*sq^(a.n+1))*Cube.Tally.bankWidth a.n a.b a.h a.K a.s := by
      unfold CubeArena.Layout.packetEnd bankStop
      dsimp only [sq]
      ring
    omega
  · unfold CubeArena.Layout.pairStride at pairFit
    omega
  · unfold CubeArena.Layout.pairStride at pairFit
    omega

/-- The singleton bank bounds the physical block width and the public mean
array reserves one entry per product label. Thus both scalar operands of the
power/header boot fit whenever the actual arena fits. -/
theorem bootScalars_of_arena (a : CubeArena.Layout) (w : ℕ)
    (alphabet : 0 < a.header.d) (blocks : 0 < a.header.blocks) (high : a.stop < 2^w) :
    a.h*a.b < 2^w ∧ a.header.d^(a.n+1) < 2^w := by
  have labels : 0 < a.alphabet := pow_pos alphabet _
  have payload := (Nat.le_mul_of_pos_left (a.h*a.b) blocks).trans
    (Nat.le_mul_of_pos_left _ (pow_pos labels 2))
  have ⟨_,_,vertex,publicLe,views,cells⟩ := a.separated
  have single : a.alphabet^2*(a.header.blocks*(a.h*a.b)) ≤ a.vertexBase :=
    Nat.le_add_left _ _
  have counts := (arenaExtents a).2.2
  have table : a.alphabet ≤ a.powerBase := by
    unfold CubeArena.Layout.powerBase CubeArena.Layout.ordinalBase CubeArena.Layout.widthBase
    omega
  change _ ∧ a.alphabet < 2^w
  omega

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
