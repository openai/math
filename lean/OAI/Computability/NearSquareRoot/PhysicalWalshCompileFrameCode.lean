import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFrameHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileScan
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileEffective
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRegisters

/-! # Linear header-preserving framing around an emitted lane scanner -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.FrameCode

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode CommonRegisters GeneratorSyntax
open private left_within from OAI.Computability.NearSquareRoot.PhysicalWalshCompileRegisters
open private computable_leftFile leftFile_file from OAI.Computability.NearSquareRoot.PhysicalWalshCompileEffective

abbrev Saved := PhysicalWalshGrid.Header × Header.Wire
abbrev Cuts := List Tally

/-- Leave the grid and descriptor parked while the lane scanner reads its rulers. -/
def arrange {X : Type} (p : FrameHeader.Fields × X) : (Cuts × X) × Saved := ((p.1.1,p.2),p.1.2)

theorem arrange_easy (X : Type) [Codec X] : Easy (arrange (X := X)) :=
  (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd))

def make (header arrangeCmd lane finish : Cmd) : Cmd :=
  (((left header).join arrangeCmd).join (left lane)).join finish

private theorem effective_left {J : Type} [Primcodable J] {p : J → Cmd} (h : Effective ltr p) :
    Effective ltr (fun j => left (p j)) :=
  (computable_leftFile.comp h).of_eq (fun _ => leftFile_file _)

theorem effective {J : Type} [Primcodable J] {header lane : J → Cmd} (arrangeCmd finish : Cmd)
    (hh : Effective ltr header) (hl : Effective ltr lane) :
    Effective ltr (fun j => make (header j) arrangeCmd (lane j) finish) :=
  (((effective_left hh).join (effective_const ltr arrangeCmd)).join (effective_left hl)).join (effective_const ltr finish)

theorem within {n : ℕ} {h a l f : Cmd} (hn : 0 < n) (hh : Within n h) (ha : Within n a)
    (hl : Within n l) (hf : Within n f) : Within n (make h a l f) :=
  ⟨⟨⟨left_within hn hh,ha⟩,left_within hn hl⟩,hf⟩

/-- Exact time and packet semantics of the named program, with a general final projection. -/
theorem scan {I X Y Z : Type} [Codec X] [Codec Y] [Codec Z] {V : I → ℕ}
    {header arrangeCmd lane finish : Cmd} {wire : I → Header.Wire} {cuts : I → Cuts} {key : I → Saved}
    {trans : Cuts × X → Y} {out : Y × Saved → Z} {x : I → X}
    (hh : Scan header V (send ∘ wire) (fun i => send (cuts i,key i)))
    (ha : KernelEffectiveFamily.Runs arrangeCmd (arrange (X := X)))
    (hl : KernelEffectiveFamily.Runs lane trans) (hf : KernelEffectiveFamily.Runs finish out)
    (hs : Small V (send ∘ x)) :
    Scan (make header arrangeCmd lane finish) V (fun i => send (wire i,x i))
      (fun i => send (out (trans (cuts i,x i),key i))) := by
  have h₀ := hh.park (send ∘ x) hs
  have h₁ := Scan.linear ha (fun i => ((cuts i,key i),x i)) h₀.output
  have h₂ := (Scan.linear hl (fun i => (cuts i,x i)) h₁.output.left).park (send ∘ key) h₁.output.right
  have h₃ := Scan.linear hf (fun i => (trans (cuts i,x i),key i)) h₂.output
  exact ((h₀.seq h₁).seq h₂).seq h₃

end PhysicalWalshCompile.FrameCode

end NearSquareRoot
end Computability
end OAI
