import OAI.Hierarchy.DescentTerminalPacketSort

namespace OAI
/-! # Read the actual original copy pins through the paid complete-word exterior shelf -/
namespace Hierarchy.DescentTerminalExteriorPackets
open DescentExterior DescentExteriorFetch DescentGL DescentColonies DescentInitialHost DescentSixParty
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open DescentTerminalDenseWindow DescentTerminalDenseGraphRead Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.FragmentBucket
open scoped Classical Fin.CommRing
noncomputable section
variable {F:Type} [Field F] {j r t arity data H : ℕ} (X:Approximation F arity data)
variable (M : Fin (ExteriorCount X) → Layout (j + (j + r)))
    (x : Catalyst.Port ((2^(j+(j+r))*t)*data)
      (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width) → Bool)
    (z : Hidden (ExteriorCount X) j r t → Bool)
    (valid : ∀ a : Fin (ExteriorCount X), stagesOK (j := j) (r := r) (M a)
      (publicRows (j := j) (r := r) (t := t) X x a)
      (projected (e := ExteriorCount X) (j := j) (r := r) (t := t) z false a)
      (projected (e := ExteriorCount X) (j := j) (r := r) (t := t) z true a))

def original (a : Σ _ : Fin (2^(j+(j+r))), Fin (ExteriorCount X)) (b : Fin t) :=
  packagePins X (2^(j+(j+r))) t x a (finProdFinEquiv (b,(0 : Fin 1)))

def flight (i : Fin (ExteriorCount X * 2^(j+r))) : Word (2^j*t) :=
  DescentExterior.pack (j := j) (t := t) (fun l => DescentExterior.output (j := j) (r := r)
    (M (DescentExteriorFetch.slab (e := ExteriorCount X) (j := j) (r := r) i))
    (projected (e := ExteriorCount X) (j := j) (r := r) (t := t) z true
      (DescentExteriorFetch.slab (e := ExteriorCount X) (j := j) (r := r) i))
    (l,DescentExteriorFetch.dest (e := ExteriorCount X) (j := j) (r := r) i))

include valid in
omit [Field F] in
theorem flight_read (port : Σ _ : Fin (2^(j+(j+r))), Fin (ExteriorCount X)) (b : Fin t) :
    wordBits (2^j*t)
      (flight (j := j) (r := r) (t := t) X M z ((chart (j := j) (r := r) M port).1))
      (finProdFinEquiv ((chart (j := j) (r := r) M port).2,b)) =
      original (j := j) (r := r) (t := t) X x port b := by
  obtain ⟨c, sl⟩ := port
  let i := (DescentColonies.address (j+(j+r))).symm c
  let coord := coords j r (M sl i)
  change wordBits (2^j*t) (flight (j := j) (r := r) (t := t) X M z
    (finProdFinEquiv (sl,rowOrd j r coord.2))) (pos j t (coord.1,b)) = _
  simp only [flight, DescentExteriorFetch.slab, DescentExteriorFetch.dest,
    Equiv.symm_apply_apply, pack_bit]
  change DescentExterior.output (j := j) (r := r) (M sl)
    (projected (e := ExteriorCount X) (j := j) (r := r) (t := t) z true sl) coord b =
    packagePins X (2^(j+(j+r))) t x ⟨c,sl⟩ (finProdFinEquiv (b, (0 : Fin 1)))
  exact (final_public_read (j := j) (r := r) (t := t) X M x z valid sl i b).trans
    (congrArg (fun a : Fin (2^(j+(j+r))) =>
      packagePins X (2^(j+(j+r))) t x ⟨a,sl⟩ (finProdFinEquiv (b, (0 : Fin 1))))
      ((DescentColonies.address (j+(j+r))).apply_symm_apply c))

include valid in
omit [Field F] in
theorem original_dense (home : Fin (ExteriorCount X * 2^(j+r)) → Fin H)
    (i : Fin (ExteriorCount X * 2^(j+r))) :
    dense (2^j*t) (publicStream (bits := fun _ : Σ _ : Fin (2^(j+(j+r))), Fin (ExteriorCount X) => t)
      (code (chart (j := j) (r := r) M) home) (original (j := j) (r := r) (t := t) X x)) i.val =
      flight (j := j) (r := r) (t := t) X M z ((Computability.BorderVNP.FragmentBucket.dest home).symm i) :=
  dense_value (chart (j := j) (r := r) M) home (original (j := j) (r := r) (t := t) X x)
    (flight (j := j) (r := r) (t := t) X M z) (flight_read (j := j) (r := r) (t := t) X M x z valid) i

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
