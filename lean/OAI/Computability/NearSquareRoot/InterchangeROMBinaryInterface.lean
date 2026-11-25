import OAI.Computability.NearSquareRoot.PhysicalWalshOpen
import OAI.Computability.NearSquareRoot.CRTControlledXor

/-! # A named command contract for the binary rectangle

The public header contains the common moving width followed by the three
spectator dimension lists. The same command acts on all record streams.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary

open IntegerMultiplication Code Strip Strip.Dims Loom Adic

abbrev Header := Tally × List Tally × List Tally × List Tally

def header (n : ℕ) (P G B : Tape) : Tree := send ((tally n,shape P,shape G,shape B) : Header)

def charge (N w h D : ℕ) := N*(w+(h+1)^D)

noncomputable def time (ρ : ℝ) (M n : ℕ) : ℕ := ⌈(M : ℝ)*((n+1 : ℕ) : ℝ)^ρ⌉₊

structure Packet where
  P : Tape
  G : Tape
  B : Tape
  n : ℕ
  w : ℕ
  admissible : ∀ d ∈ P ++ G ++ B, 2 ≤ d ∧ d ≤ Net.Shuttle.base
  bits : SpanKey P G B (Block 2 n) → List Bool
  exactWidth : ∀ u, (bits u).length = w

namespace Packet

abbrev rows (x : Packet) := stock 2 x.P x.G x.B x.n
abbrev description (x : Packet) := header x.n x.P x.G x.B

def input (x : Packet) := Tree.fork x.description (stripe x.rows (send ∘ x.bits))

def output (x : Packet) := stripe x.rows (fun u => send (x.bits (swapper _ _ _ u)))

def mass (D : ℕ) (x : Packet) := charge x.rows.count x.w x.description.count D

end Packet

/-- One time and space constant applies to all geometries and all payloads. -/
def RectPhysical (c : Cmd) (ρ : ℝ) (D : ℕ) := PhysicalWalsh.ClosedRuns c
  (fun x : Packet => time ρ (x.mass D) x.n) (Packet.mass D) Packet.input Packet.output

/-- Specialize the single physical program to any family of ordinary bead stripes. -/
theorem RectPhysical.beads {c : Cmd} {ρ : ℝ} {D : ℕ} (h : RectPhysical c ρ D)
    {I : Type} (n : I → ℕ) (P G B : I → Tape)
    (good : ∀ i d, d ∈ P i ++ G i ++ B i → 2 ≤ d ∧ d ≤ Net.Shuttle.base)
    {T : I → Type} (u : (i : I) → Series (T i))
    (v : (i : I) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → T i → Bead) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    let M i := charge (s i).count (u i).count (header (n i) (P i) (G i) (B i)).count D
    PhysicalWalsh.ClosedRuns c (fun i => time ρ (M i) (n i)) M
      (fun i => Tree.fork (header (n i) (P i) (G i) (B i)) (cloth s u v i))
      (cloth s u fun i => v i ∘ swapper _ _ _) := by
  let x (i : I) : Packet := ⟨P i,G i,B i,n i,(u i).count,good i,
    fun a => (u i).tab (notify ∘ v i a),fun a => (u i).card _⟩
  have row (i : I) (a) : send ((x i).bits a) = strip (u i) (v i a) := by
    change send ((u i).tab (notify ∘ v i a)) = stripe (u i) (send ∘ v i a)
    exact (stripe_eq' (u i) (notify ∘ v i a)).symm
  obtain ⟨C,hC⟩ := h
  refine ⟨C,fun i env deck base ok => ?_⟩
  have h' := hC (x i) env deck base ok
  unfold Packet.input Packet.output at h'
  rw [show (send ∘ (x i).bits) = (fun a => strip (u i) (v i a)) from funext (row i)] at h'
  simp only [row] at h'
  exact h'

end InterchangeROMBinary

end NearSquareRoot
end Computability
end OAI
