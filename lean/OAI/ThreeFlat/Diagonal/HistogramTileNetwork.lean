import OAI.ThreeFlat.Diagonal.MotifPackedTile
import OAI.ThreeFlat.Diagonal.HistogramPortKernel

namespace OAI
/-! # Trivalent realization of the histogram kernel's base tile product

Each copy has a fixed header containing its selector and all its old
half-ports, and variable-length payloads in the order of the incident
supply ports. All encodings used in a header have constant arity.
-/

namespace ThreeFlat.Diagonal.HistogramTileNetwork

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector MotifOuterTerms MotifBinaryPacking MotifOrderedCells
open scoped BigOperators Classical

variable {J E S H F : Type*} [CommRing F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r : ℕ}

/-- Canonical fixed-arity header for one base coefficient. The port ordering
is an enumeration of a single constant motif. -/
structure Header (P H : Type*) (width : P → ℕ) (k n : ℕ) where
  ports : Fin n ≃ P
  code : H ↪ Fin (2^k)

namespace Header

variable {P : Type*} {width : P → ℕ} (B : Header P H width k n)

def arity := k + ∑ i, width (B.ports i)

private def payload := (Equiv.piCongrLeft (fun p => Fin (2^width p)) B.ports).symm.trans
  ((Equiv.piCongrRight (fun i => (word (width (B.ports i))).symm)).trans (flatten (fun i => width (B.ports i))))

def encodeRaw (a : Fin (2^k)) (x : ∀ p, Fin (2^width p)) : Fin B.arity → Bool :=
  Fin.append ((word k).symm a) (B.payload x)

private theorem flatten_slot {m : ℕ} (w : Fin m→ℕ) (x : (i : Fin m)→Fin (w i)→Bool)
    (i : Fin m) (b : Fin (w i)) : flatten w x (finSigmaFinEquiv ⟨i,b⟩)=x i b :=
  congrArg (fun q : (a : Fin m) × Fin (w a)=>x q.1 q.2) (finSigmaFinEquiv.symm_apply_apply ⟨i,b⟩)

omit [Fintype H] [DecidableEq H] [Nonempty H] in
theorem encodeRaw_payload (a : Fin (2^k)) (x : ∀ p, Fin (2^width p)) (i : Fin n) (b : Fin (width (B.ports i))) :
    B.encodeRaw a x (Fin.natAdd k (finSigmaFinEquiv ⟨i,b⟩)) = (word _).symm (x (B.ports i)) b := by
  rw [encodeRaw,Fin.append_right]
  simp only [payload,Equiv.trans_apply,flatten_slot,Equiv.piCongrRight_apply,Pi.map_apply,Equiv.piCongrLeft_symm_apply]


def encode (h : H) (x : ∀ p, Fin (2^width p)) : Fin B.arity → Bool := B.encodeRaw (B.code h) x

noncomputable def letter (z : Fin B.arity → Bool) := Function.invFun B.code (word k fun i => z (i.castAdd _))

def old (z : Fin B.arity → Bool) := B.payload.symm fun i => z (Fin.natAdd k i)

omit [Fintype H] [DecidableEq H] in
@[simp] theorem letter_encode (h : H) (x : ∀ p, Fin (2^width p)) : B.letter (B.encode h x) = h := by
  simp [letter,encode,encodeRaw,Function.leftInverse_invFun B.code.injective h]

omit [Fintype H] [DecidableEq H] [Nonempty H] in
@[simp] theorem old_encode (h : H) (x : ∀ p, Fin (2^width p)) : B.old (B.encode h x) = x := by
  simp [old,encode,encodeRaw]

end Header

variable (D : PortGraph J E) (G : Supply J S) (j : J) (base : E → ℕ)
  (B : Header (D.Port j) H (fun p => base p.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ) (fits : ∀ h a, sw h (portsAt a).1.1 ≤ d)
  (M : ∀ h v, D.State (fun a => Fin (2^base a)) v → (ports G).State (fun a => Fin (2^sw h a)) v → F)

noncomputable def tile : Tile F H e d B.arity where
  symbol := B.letter
  width := fun h a => sw h (portsAt a).1.1
  fits := fits
  value := fun z x => M (B.letter z) j (B.old z)
    (Equiv.piCongrLeft (fun p : (ports G).Port j => Fin (2^sw (B.letter z) p.1.1)) portsAt x)

variable (w : E → ℕ) (hpad : ∀ a, w a ≤ base a*r)

/-- Selector values and actual padded digits are the physical header bits. -/
def heads (s : Fin r → H) (x : D.State (fun a => Fin (2^w a)) j) (i : Fin r) :=
  B.encode (s i) (MotifDemandPadding.readSlice D (fun a => MotifDemandPadding.digits (w a) (base a) r (hpad a)) i j x)

omit [CommRing F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [Nonempty H] in
/-- Rewrite the selector family before instantiating any of its dependent
packed arguments. This also handles arbitrary coincident physical ports. -/
private theorem packed_entry {labels s : Fin r→H} (same : labels=s) (i : Fin r)
    (input : D.State (fun a=>Fin (2^base a)) j)
    (y : (ports G).State (fun a=>Fin (2^histWidth sw (histogram s) a)) j)
    (sizes : ∀a : Fin e,2^histWidth sw (histogram s) (portsAt a).1.1=
      2^(∑l : Fin r,sw (labels l) (portsAt a).1.1)) :
    M (labels i) j input (Equiv.piCongrLeft
      (fun p : (ports G).Port j=>Fin (2^sw (labels i) p.1.1)) portsAt (fun a=>
        (pack (fun l=>sw (labels l) (portsAt a).1.1)).symm (Fin.cast (sizes a) (y (portsAt a))) i))=
      M (s i) j input (fun p=>unpackHistAt sw (histogram s) ⟨s,rfl⟩ p.1.1 (y p) i) := by
  subst labels
  apply congrArg (M (s i) j input)
  apply (Equiv.piCongrLeft (fun p : (ports G).Port j => Fin (2^sw (s i) p.1.1)) portsAt).symm.injective
  funext a
  simp only [Equiv.piCongrLeft_symm_apply, Equiv.piCongrLeft_apply_apply]; rfl

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] in
/-- A valid selector history identifies the output of a concrete tile network
with the coefficient in `histogram_port_kernel`. The payload is given on
physical supply edges and zero-filled after its advertised width. -/
theorem eval_tile (s : Fin r → H) (x : D.State (fun a => Fin (2^w a)) j)
    (y : (ports G).State (fun a => Fin (2^histWidth sw (histogram s) a)) j)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) =
      if Y = Routing.StableCompaction.compact M X then 1 else 0) :
    let K := tile D G j base B portsAt sw fits M
    let z := heads D j base B w hpad s x
    let input (a : Fin e) : Fin (2^∑ i, K.lengths z a i) := Fin.cast (by
      dsimp [K,z,Tile.lengths,tile,heads]
      simp only [Header.letter_encode]
      exact congrArg (2 ^ ·) (histogram_width sw s (portsAt a).1.1)) (y (portsAt a))
    (K.network C).eval (arguments z (K.packedInput z input)) =
      histogramTileProduct D G w base hpad sw M (histogram s) j x ⟨s,rfl⟩ y := by
  dsimp only
  rw [Tile.eval_packed _ _ hC]
  unfold histogramTileProduct
  apply Finset.prod_congr rfl
  intro i _
  let z:=heads D j base B w hpad s x
  let u:=MotifDemandPadding.readSlice D (fun a=>MotifDemandPadding.digits (w a) (base a) r (hpad a)) i j x
  have same : (fun l=>B.letter (z l))=s := funext (fun l=>B.letter_encode _ _)
  have old : B.old (z i)=u := B.old_encode _ _
  have size (a : Fin e) : 2^histWidth sw (histogram s) (portsAt a).1.1=
      2^(∑l : Fin r,sw (B.letter (z l)) (portsAt a).1.1) := by
    have hh:=congrArg (fun t : Fin r→H=>2^(∑l,sw (t l) (portsAt a).1.1)) same
    exact (congrArg (2 ^ ·) (histogram_width sw s (portsAt a).1.1)).trans hh.symm
  have call:=packed_entry D G j base portsAt sw M same i (B.old (z i)) y size
  exact call.trans (congrArg (fun a=>M (s i) j a
    (fun p=>unpackHistAt sw (histogram s) ⟨s,rfl⟩ p.1.1 (y p) i)) old)

end ThreeFlat.Diagonal.HistogramTileNetwork

end OAI
