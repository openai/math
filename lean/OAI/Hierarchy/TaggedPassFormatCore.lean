import OAI.Hierarchy.TaggedRadixScales

namespace OAI
/-! # Heights, copy counts and payloads of a physical radix pass -/
namespace Hierarchy.Tagged.Radix

structure PassFormat where
  first : ℕ
  second : ℕ
  wide : ℕ
  copies : ℕ
  firstW : ℕ
  secondW : ℕ
  wideW : ℕ

structure FormatBounds (a B : ℝ) (h d c K : ℕ) (g : PassFormat) : Prop where
  firstLow : 2*digitBits a h ≤ g.first
  firstHigh : g.first ≤ 2*digitBits a h+d
  secondLow : 2*digitBits a h ≤ g.second
  secondHigh : g.second ≤ 2*digitBits a h+d
  wideLow : h-packBits B h ≤ g.wide
  wideHigh : g.wide ≤ h-packBits B h+d
  positive : 0<g.copies
  firstMass : 2^h ≤ g.copies*2^g.first
  firstRoom : g.copies*2^g.first ≤ K*2^h
  secondMass : 2^h ≤ g.copies*2^g.second
  secondRoom : g.copies*2^g.second ≤ K*2^h
  firstPayload : 0<g.firstW ∧ g.firstW≤c*h
  secondPayload : 0<g.secondW ∧ g.secondW≤c*h
  widePayload : 0<g.wideW ∧ g.wideW≤c*h*2^packBits B h

end Hierarchy.Tagged.Radix

end OAI
