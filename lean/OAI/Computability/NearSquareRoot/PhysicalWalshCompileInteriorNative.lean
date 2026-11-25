import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshXorInterior

/-! # One three-slot native command for all arities at a fixed exponent -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode Interior SwapPrefix
open PhysicalWalshCompileSwapRulers (World)
open PhysicalWalshCompileInteriorHeader (nativeRegime nativeP nativeL native_scale_le)
open PhysicalWalsh.XorThreshold

/-- The two compact address widths are the only geometry in the native
instruction controller. The unary rulers frame its input and output. -/
def rawHeader (a W : ℕ) (s : Shape) :=
  XorWindow.duskHeader (send (tally (P (a+1) W s),tally (L (a+1) s))) (rows a W s) (S a s) s.w

def padded {a W : ℕ} (u : XorInput W) := stream (paddedSize (a+1) W u.shape) (extend (a+1) W u.shape u.row)

noncomputable def moved {a W : ℕ} (u : XorInput W) : Data u.shape :=
  extend (a+1) W u.shape u.row ∘ XorSweep.directedRead (L (a+1) u.shape) (S a u.shape)

/-- The native runtime on any specified set of admissible inputs. -/
def NativeOn (a W : ℕ) (ρ : ℝ) (pred : Shape → Prop) (c : Cmd) : Prop :=
  ClosedRuns c (fun u : {t : XorInput W // pred t.shape} => extra a W ρ u.val.shape)
    (fun u => volume a W u.val.shape)
    (fun u => .fork (rawHeader a W u.val.shape) (send (padded (a:=a) u.val)))
    (fun u => send (stream (paddedSize (a+1) W u.val.shape) (moved (a:=a) u.val)))

def Native (ρ : ℝ) (D : ℕ) (c : Cmd) : Prop :=
  ∀ a W (_ : 4 ≤ a), NativeOn a W ρ (fun s => cutoff D (Header.scale (a+1) s) ≤ L (a+1) s) c

structure Job (D : ℕ) where
  a : ℕ
  W : ℕ
  arity : 4 ≤ a
  u : Large a W D

private def select {D : ℕ} (j : Job D) : World :=
  ⟨j.a,j.W,0,0,D,j.u.val.shape⟩

/-- The exponent is fixed before choosing the native command. All Walsh
dimensions and all reached data, including the prefix and suffix lengths,
vary in a single execution contract. -/
theorem exists_native {ρ : ℝ} (lower : 1/2 < ρ) (upper : ρ ≤ 1) :
    ∃ (D : ℕ) (c : Cmd), Native ρ D c := by
  let pre (t : World) := P (t.a+1) t.W t.shape
  let bits (t : World) := L (t.a+1) t.shape
  let stride (t : World) := S t.a t.shape
  let width (t : World) := t.shape.w
  obtain ⟨D,run⟩ := XorWindow.boundedDuskOn lower pre bits stride width nativeP nativeL
  let s (j : Job D) := j.u.val.shape
  let b (j : Job D) := B j.a (s j)
  let m (j : Job D) := (s j).suff*(2*((s j).w+1))
  let q (j : Job D) := Header.scale (j.a+1) (s j)
  let price (j : Job D) := factor ρ (bits (select j))
  let z (j : Job D) := extend (j.a+1) j.W (s j) j.u.val.row
  have raw := run (Y:=Job D) select b m q price
    (fun j => by change ((s j).suff*2^(b j)) * (2*((s j).w+1)) = 2^(b j)*m j; dsimp only [m]; ring)
    (fun j => native_scale_le (select j) j.arity j.u.val.positive)
    (fun j => Nat.mul_pos (s j).suff_pos (by omega))
    (fun j => by
      simpa only [b,B,show j.a+1-4=j.a-3 by omega]
        using payload_le_suffix (A:=j.a+1) (by have := j.arity; omega) j.u.property)
    (fun j => factor_pays ρ bits (select j))
    (fun j => factor_le_prefix upper j.u.property (Nat.le_add_left ..)) z
  let t (j : Job D) := extra j.a j.W ρ (s j)
  let v (j : Job D) := volume j.a j.W (s j)
  have physical : BoundedTask t v
      (fun j => .fork (rawHeader j.a j.W (s j)) (send (padded (a:=j.a) j.u.val)))
      (fun j => send (stream (paddedSize (j.a+1) j.W (s j)) (moved (a:=j.a) j.u.val))) := by
    apply raw.conform
    · intro j
      change (4+3*Controlled.guardWidth (3*L (j.a+1) (s j)))*
        (XorReserve.volume (P (j.a+1) j.W (s j)) (3*L (j.a+1) (s j)) (b j) (m j)*(price j+1))+1=_
      rw [show XorReserve.volume (P (j.a+1) j.W (s j)) (3*L (j.a+1) (s j)) (b j) (m j)=v j
        from volume_eq j.a j.W j.arity (s j) j.u.val.positive]
      rfl
    · exact fun j => volume_eq j.a j.W j.arity (s j) j.u.val.positive
    · intro j
      change Tree.fork (rawHeader j.a j.W (s j)) (send (stream (rows j.a j.W (s j)*S j.a (s j)) (z j))) = _
      rw [rows_mul_S (W:=j.W) j.arity j.u.val.positive]
      rfl
    · intro j
      change send (stream (rows j.a j.W (s j)*S j.a (s j)) (moved (a:=j.a) j.u.val)) = _
      rw [rows_mul_S (W:=j.W) j.arity j.u.val.positive]
  obtain ⟨c,hc⟩ := physical
  refine ⟨D,c,fun a W ha => ?_⟩
  exact ClosedRuns.on (c:=c) hc (fun u : Large a W D => (⟨a,W,ha,u⟩ : Job D))

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
