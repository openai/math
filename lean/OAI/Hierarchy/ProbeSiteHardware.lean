import OAI.Hierarchy.ProbeBatchReplacement
import OAI.ThreeFlat.Diagonal.MotifNativeCompactors

namespace OAI
/-! # Native coefficient network for one site of a finite signed packet

A single bounded lookup implements each copy. Stable compaction places
the chosen width of each incident field at the prefix offset of that copy.
Each public pin is either a single selector bit or a bit of one incident
packed data field. -/

noncomputable section
namespace Hierarchy.Probe.SiteHardware

open ThreeFlat ThreeFlat.Diagonal
open MotifBinaryPacking MotifOrderedCells MotifNativeCompactors
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical BigOperators

variable {F H V : Type*} [Field F] [Fintype H] [Fintype V] {r k b : ℕ}

/-- Bit number zero at the RAM pin is the least significant wire bit. -/
theorem word_bit {n : ℕ} (x : Fin (2^n)) (j : Fin n) :
    (word n).symm x j=x.val.testBit j.val := rfl

/-- The old native compactor and the actual raw product contraction split
exactly the same bits of each mixed-width port. -/
theorem unpack_raw (g : Fin r→Widths k) (e : Chord k) (x : Index (∑ j,g j) e) (j : Fin r) :
    (pack (fun i => g i e)).symm
        (x.cast (by simp only [Finsupp.finsetSum_apply] : 2^((∑ i,g i) e)=2^∑ i,g i e)) j =
      blockWireIndex g e x j := by
  apply (word (g j e)).symm.injective
  funext bit
  let w (i : Fin r):=g i e
  let total : Fin (2^∑ i,w i):=Fin.cast (by simp only [w,Finsupp.finsetSum_apply]) x
  have h:=unpack_bit w total j bit
  refine h.trans ?_
  rw [word_bit,word_bit,blockWireIndex_testBit,bit_offset]
  exact congrArg x.val.testBit (Nat.add_comm _ _)

/-- A single-copy upper bound for all fields of a fixed signed local table. -/
def widthCap (width : H→V→ℕ) : ℕ := Finset.univ.sup (fun p : H × V => width p.1 p.2)

theorem width_fits (width : H→V→ℕ) (h : H) (v : V) : width h v ≤ widthCap width :=
  Finset.le_sup (f:=fun p : H×V => width p.1 p.2) (Finset.mem_univ (h,v))

private def atNamed {β : V→ℕ} (ord : V ≃ Fin (Fintype.card V))
    (xs : ∀ i, Fin (2^β (ord.symm i))) (v : V) : Fin (2^β v) :=
  Fin.cast (by rw [Equiv.symm_apply_apply]) (xs (ord v))

/-- Arbitrary finite single-copy signed table, presented to the three-pin
hardware compiler in the fixed order of its actual incident fields. -/
def tile (symbol : (Fin b → Bool)→H) (width : H→V→ℕ)
    (value : ∀ h, (∀ v, Fin (2^width h v))→F) : Tile F H (Fintype.card V) (widthCap width) b :=
  {symbol:=symbol
   width:=fun h j => width h ((Fintype.equivFin V).symm j)
   fits:=fun h _j => width_fits width h _
   value:=fun z xs => value (symbol z) (atNamed (Fintype.equivFin V) xs)}

def scale (n : ℕ) := Nat.log 2 (n+1)+1

theorem scale_room (n : ℕ) : n ≤ 2^(scale n) :=
  (Nat.le_succ _).trans (Nat.lt_pow_succ_log_self (by decide : 1<2) _).le

theorem scale_small (n : ℕ) : 2^(scale n) ≤ 2*(n+1) := by
  rw [scale,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))

def network {n d : ℕ} (K : Tile F H n d b) (r : ℕ) := K.network (partialInput F (r*d) (scale (r*d)))

omit [Fintype H] in
theorem network_size {n d : ℕ} (K : Tile F H n d b) (r : ℕ) :
    let net := network K r
    net.cells+net.internal ≤ r*(2^(b+(n*d+n*d))*((b+(n*d+n*d))+2)) + 2*(n*(r*d)) +
      128000*n*(r*d+1)*(Nat.log 2 (r*d+1)+2)^3 := by
  dsimp only [network]
  refine (tile_size K r (scale (r*d))).trans ?_
  have linear := Nat.mul_le_mul_right (32000*(scale (r*d)+1)^3) (scale_small (r*d))
  have full := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n linear)
  calc
    _ ≤ r*(2^(b+(n*d+n*d))*((b+(n*d+n*d))+2)) + 2*(n*(r*d)) +
        2*(n*(2*(r*d+1)*(32000*(scale (r*d)+1)^3))) := Nat.add_le_add_left full _
    _ = _ := by dsimp [scale]; ring

def numbered (width : H→V→ℕ) (w : Fin r→H) (x : ∀ v, Fin (2^∑ j,width (w j) v))
    (e : Fin (Fintype.card V)) := x ((Fintype.equivFin V).symm e)

/-- Native verification on the zero-extended external pins. Exactly one
stable compacted data assignment contributes to the signed site product. -/
theorem eval (symbol : (Fin b→Bool)→H) (width : H→V→ℕ)
    (value : ∀ h,(∀ v,Fin (2^width h v))→F) (z : Fin r→Fin b→Bool)
    (x : ∀ v, Fin (2^∑ j,width (symbol (z j)) v)) :
    let K := tile symbol width value
    (network K r).eval (arguments z (K.packedInput z (numbered width (fun j=>symbol (z j)) x))) =
      ∏ j, value (symbol (z j)) (fun v => (pack (fun i => width (symbol (z i)) v)).symm (x v) j) := by
  dsimp only
  have run := (tile symbol width value).eval_packed (partialInput F (r*widthCap width) (scale (r*widthCap width)))
    (partialInput_eval _ _ (scale_room _)) z (numbered width (fun j=>symbol (z j)) x)
  refine run.trans (Finset.prod_congr rfl (fun j _ => ?_))
  apply congrArg (value (symbol (z j)))
  funext v
  apply Fin.ext
  change ((pack (fun i=>width (symbol (z i)) ((Fintype.equivFin V).symm ((Fintype.equivFin V) v)))).symm
    (x ((Fintype.equivFin V).symm ((Fintype.equivFin V) v))) j).val=_
  exact congrArg (fun a : V=>((pack (fun i=>width (symbol (z i)) a)).symm (x a) j).val)
    ((Fintype.equivFin V).symm_apply_apply v)

abbrev Sockets (i : Fin k) := (portGraph k).Port i ⊕ (portGraph k).Port i

def socketWidth (a : Widths k) (U : H→Widths k) (i : Fin k) (h : H) : Sockets i→ℕ
  | .inl p => a p.1.1
  | .inr p => U h p.1.1

def socketValue {a : Widths k} {U : H→Widths k}
    (M : ∀ h i,State a i→State (U h) i→F) (i : Fin k) (h : H)
    (fields : ∀ p,Fin (2^socketWidth a U i h p)) : F :=
  M h i (fun p => fields (.inl p)) (fun p => fields (.inr p))

def socketFields (a : Widths k) (U : H→Widths k) (w : Fin r→H) (i : Fin k)
    (x : State (∑ _ : Fin r,a) i) (y : State (∑ j,U (w j)) i) :
    ∀ p, Fin (2^∑ j,socketWidth a U i (w j) p)
  | .inl p => (x p).cast (by simp only [socketWidth,Finsupp.finsetSum_apply])
  | .inr p => (y p).cast (by simp only [socketWidth,Finsupp.finsetSum_apply])

/-- The local hardware coefficient is the exact tiled matrix used in
the tensor restriction. Every typed input or output socket is an
actual packed chord, with the same index convention at the other end. -/
theorem tiled_eval (symbol : (Fin b→Bool)→H) (a : Widths k) (U : H→Widths k)
    (M : ∀ h i,State a i→State (U h) i→F) (i : Fin k) (z : Fin r→Fin b→Bool)
    (x : State (∑ _ : Fin r,a) i) (y : State (∑ j,U (symbol (z j))) i) :
    let w := fun j=>symbol (z j)
    let W := socketWidth a U i
    let K := tile symbol W (socketValue M i)
    let source := socketFields a U w i x y
    (network K r).eval (arguments z (K.packedInput z (numbered W w source))) =
      tiledTable (g:=fun _ : Fin r => a) (fun j=>M (w j)) i x y := by
  refine (eval symbol (socketWidth a U i) (socketValue M i) z (socketFields a U _ i x y)).trans ?_
  apply Finset.prod_congr rfl
  intro j _
  apply congrArg₂ (M (symbol (z j)) i)
  · funext p
    exact unpack_raw (fun _ : Fin r=>a) p.1.1 (x p) j
  · funext p
    exact unpack_raw (fun j=>U (symbol (z j))) p.1.1 (y p) j

end Hierarchy.Probe.SiteHardware
end

end OAI
