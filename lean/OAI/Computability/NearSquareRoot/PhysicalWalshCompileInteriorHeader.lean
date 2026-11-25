import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapLiteral
import OAI.Computability.NearSquareRoot.PhysicalWalshXorInteriorHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshXorDusk
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileScan

/-! # Uniform descriptor for a physical three-slot XOR

The native program receives just its two address widths. Both tallies fit
inside the original compact Walsh descriptor at every active interior node.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInteriorHeader

open IntegerMultiplication Code Space Strip Staff Carry PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompileSwapRulers CommonRegisters GeneratorSyntax

/-- The native three-slot program's two address widths. -/
def native (t : World) :=
  (tally (Interior.P (t.a+1) t.W t.shape),tally (Interior.L (t.a+1) t.shape))

def nativeRegime : Regime World := ⟨size ∘ native,send ∘ native,Dom.base _⟩

theorem nativeP : Realizes nativeRegime (fun t : World => Interior.P (t.a+1) t.W t.shape) :=
  (show nativeRegime.Has native from nativeRegime.self).ez Easy.fst

theorem nativeL : Realizes nativeRegime (fun t : World => Interior.L (t.a+1) t.shape) :=
  (show nativeRegime.Has native from nativeRegime.self).ez Easy.snd

theorem native_scale_le (t : World) (ha : 4 ≤ t.a) (hl : 0 < t.shape.level) :
    nativeRegime.scale t ≤ Header.scale (t.a+1) t.shape := by
  have g : groups t.W t.shape ≤ t.shape.pref+1 := (max_le t.shape.pref_pos (Nat.div_le_self ..)).trans (Nat.le_succ _)
  have hg := Nat.clog_mono_right 2 g
  have level : (t.a+1)*Interior.L (t.a+1) t.shape = grow (t.a+1) t.shape.level := by
    unfold Interior.L grow
    rw [Nat.mul_left_comm,← pow_succ',Nat.sub_add_cancel hl]
  have two := Nat.mul_le_mul_right (Interior.L (t.a+1) t.shape) (by omega : 2 ≤ t.a+1)
  rw [level] at two
  change size (tally (Nat.clog 2 (groups t.W t.shape)+Interior.L (t.a+1) t.shape),tally (Interior.L (t.a+1) t.shape)) ≤ _
  rw [Header.scale_exact]
  simp only [size_prod,size_tally,tally_length]
  omega

def keys (t : World) :=
  ((tally (Interior.rows t.a t.W t.shape),tally (Interior.S t.a t.shape*(2*(t.shape.w+1)))),
    native t,tally (Interior.rows t.a t.W t.shape*Interior.S t.a t.shape),tally (2*(t.shape.w+1)))

theorem keys_eq (t : World) : send (keys t) =
    XorWindow.duskHeader (nativeRegime.header t) (Interior.rows t.a t.W t.shape)
      (Interior.S t.a t.shape) t.shape.w := rfl

private theorem rowWidth : Figure regime (fun t : World => Interior.S t.a t.shape) := by
  have b : Realizes regime (fun t : World => t.a-3) := by
    convert arity.minused (Realizes.fix 4) using 1
    funext t; omega
  exact suff.multiplied ((Figure.natural 2).repeated (b.times slot))

/-- The body reads every layout parameter from its input. The large record
and payload rulers cost their emitted length. -/
theorem mint : Mint regime keys := by
  have p : Realizes regime (fun t : World => Interior.P (t.a+1) t.W t.shape) := group.short_log.plus slot
  have h : regime.Has native := p.pair slot
  have n : Figure regime (fun t : World => Interior.rows t.a t.W t.shape) :=
    (Figure.natural 2).repeated (p.plus ((Realizes.fix 3).times slot))
  have bits := (Realizes.fix 2).times width
  exact ((Mint.tally n).pair (Mint.tally (rowWidth.multiplied (Figure.of_spoken bits)))).pair
    ((Mint.of_has h).pair ((Mint.tally (n.multiplied rowWidth)).pair (Mint.of_has bits)))

open private hdr_bound from OAI.Computability.NearSquareRoot.PhysicalWalshXorInteriorHeader

theorem keys_size (t : World) (d : ℕ) (ha : 4 ≤ t.a) (hl : 0 < t.shape.level) :
    size (keys t) ≤ 25*(allowance (t.a+1) (d+1) t.shape+1) := by
  have small := native_scale_le t ha hl
  change size (native t) ≤ size (Header.wire (t.a+1) t.shape) at small
  have b := hdr_bound (W:=t.W) (d:=d) ha hl
  simp only [Interior.header,size_prod] at b
  simp only [keys,size_prod]
  change size (tally (Interior.P (t.a+1) t.W t.shape),tally (Interior.L (t.a+1) t.shape)) ≤ _ at small
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right small _) _) _) _) b

/-- Every literal specialization emits the native packing and unpacking
keys from the ordinary Walsh wire using a common register bound and degree. -/
theorem compiled : ∃ (R d : ℕ) (c : Control → Cmd), 1 ≤ d ∧ Effective ltr c ∧
    (∀ k, Within R (c k)) ∧ ∀ a W (i j : Fin (a+1)) D, 4 ≤ a → ∃ C : ℕ,
      ∀ (s : Shape), 0 < s.level → let t : World := ⟨a,W,i,j,D,s⟩
        (∀ env park, Fits env (c (control t)) (pile 0 (send (descriptor t)) park)
          (pile 0 (send (keys t)) park) (C*(allowance (a+1) d s+1))) ∧
        size (keys t) ≤ C*(allowance (a+1) d s+1) := by
  obtain ⟨R,d,c,hd,eff,reg,h⟩ := configuredMint mint
  refine ⟨R,d+1,c,by omega,eff,reg,?_⟩
  intro a W i j D ha
  obtain ⟨C,run⟩ := h a W i j D
  refine ⟨C*26+25,fun s hl => ?_⟩
  let t : World := ⟨a,W,i,j,D,s⟩
  let v := allowance (a+1) (d+1) s+1
  have hsize : size (keys t) ≤ 25*v := keys_size t d ha hl
  have power : (Header.scale (a+1) s+1)^d ≤ v :=
    (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)).trans ((Nat.le_add_left ..).trans (Nat.le_succ _))
  have bound := Nat.mul_le_mul_left C (show (Header.scale (a+1) s+1)^d+size (keys t) ≤ 26*v by omega)
  rw [← Nat.mul_assoc] at bound
  constructor
  · intro env park
    apply (run s env park).mono
    change C*((Header.scale (a+1) s+1)^d+size (keys t)) ≤ (C*26+25)*v
    rw [Nat.add_mul]; omega
  · change size (keys t) ≤ (C*26+25)*v
    rw [Nat.add_mul]; omega

end PhysicalWalshCompileInteriorHeader

end NearSquareRoot
end Computability
end OAI
