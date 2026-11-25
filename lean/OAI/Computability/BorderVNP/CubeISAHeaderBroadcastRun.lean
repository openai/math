import OAI.Computability.BorderVNP.CubeISAHeaderBroadcast

/-! # Physical execution of the compact cube header parser

The mode bit, geometry profile, and previous saved common-header copy fix the
source addresses. On a physical broadcast segment the native decoder rejects
precisely the out-of-range fields. Every returned row and total is read from
the shared memory produced by the actual ordinary team instruction sequence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.DeclarationBits

open Physical RoutingISA VPVNP.BurstRAM TeamContraction.JointHeader

variable {n d cap w : ℕ}

/-- Execute the parser on the actual copied common header. The native test
accepts exactly the legal raw coordinate and entry values, and its concrete
memory image supplies the physical declaration arrays and their sums. -/
theorem program_from_copy (f : Broadcast n d cap) (geometry : List Bool) (claims : List (List Bool))
    (extra header saved dense totals : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w)
    (copied : FlatAt m saved (TeamContraction.JointHeader.padded
      (TeamContraction.JointHeader.spelling (geometry++spelling f) claims) extra)) :
    let source := saved+1+geometry.length
    let l := layout n d cap header source dense totals
    0 < w → HeaderDecode.Fits l w → HeaderDecode.AtFrame l (readings pub) (readings m) →
      (pub 0).val+63 < 2^w → header+12 < 2^w → totals+(n+1) ≤ 2^w →
      (dense+l.entries ≤ totals ∨ totals+(n+1) ≤ dense) →
      (header+5 < totals ∨ totals+(n+1) ≤ header+5) → d*d*cap < 2^w →
      TestRun pub mac HeaderDecode.program r m (HeaderDecode.cost l + HeaderTotals.cost (n+1) (d*d))
        (readCode (n+1) f.1 < n+1 ∧ ∀ pair j, readCode (cap+1) (f.2 pair j) < cap+1)
        (fun z => z.mem = l.finalImage (readings m) ∧ z.mem (header+5) = readCode (n+1) f.1 ∧
          CubeLengths.StoredRows z.mem dense (fun pair j => readCode (cap+1) (f.2 pair j)) ∧
          ∀ j : Fin (n+1), z.mem (totals+j.val) = ∑ pair, readCode (cap+1) (f.2 pair j)) := by
  intro source l hw fit atFrame primary head dst apart different sum
  have raw : FlatAt m source (spelling f) := from_common_header geometry claims extra copied
  apply (HeaderDecode.program_run (mac := mac) l r m fit atFrame primary head dst apart sum).mono le_rfl
    (valid_iff header source dense totals hw raw)
  intro z image
  rw [image]
  exact ⟨rfl,(l.finalCoordinate _ fit.different different).trans (read_bits (coordinate_bits hw raw)),
    final_rows header source dense totals hw raw apart,final_totals header source dense totals hw raw apart⟩

/-- Only the paper's unique passing raw word can represent a successful cube
length declaration. Conversely that word gives a successful length declaration. -/
theorem word_passes_iff {blocks B K h s : ℕ} (select : Packet n d blocks → Selector n K h)
    (raw : Fin (length n d (declarationCap n d blocks B h s)) → Bool) :
    passesBroadcast B s select ((wordEquiv n d _).symm raw) ↔
      raw = spellingWord (broadcast B s select) := by
  rw [passesBroadcast_iff,Equiv.symm_apply_eq]
  rfl

end Cube.DeclarationBits

end BorderVNP
end Computability
end OAI
