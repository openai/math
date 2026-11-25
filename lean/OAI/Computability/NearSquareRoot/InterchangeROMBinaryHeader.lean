import OAI.Computability.NearSquareRoot.InterchangeROMBinaryWidth
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryInterface
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloTypes
import OAI.Computability.NearSquareRoot.InterchangeBeadThreshold

/-! # A single descriptor program for binary rectangular interchange

The radix is a runtime input to this program. The five expanded unary counts
are charged to the allocated grid and the remaining work to the compact header.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary

open IntegerMultiplication Code Strip Strip.Dims Adic Loom Staff

structure Ticket extends Packet where
  b : ℕ
  large : Net.Shuttle.base ≤ b

namespace Ticket

abbrev e (x : Ticket) := width x.b x.n
abbrev radix_ok (x : Ticket) : 2 ≤ x.b := Net.Shuttle.base_large.le.trans x.large

def compact (x : Ticket) : Tally × Header := (tally x.b,tally x.n,shape x.P,shape x.G,shape x.B)

def regime : Regime Ticket := ⟨fun x => size x.compact, fun x => send x.compact,Dom.base _⟩

def grid (x : Ticket) : BinaryHalo.Shape := ⟨room x.P,2^x.n,room x.G,x.b^x.e,room x.B⟩

abbrev total (x : Ticket) := x.grid.volume

def digitCount (x : Ticket) := x.P.length + x.e + x.G.length + x.e + x.B.length

def pad (k : ℕ) (x : Ticket) := (x.b*digitCount x+1)^k

private theorem has_compact : regime.Has compact := regime.self

theorem has_b : Realizes regime Ticket.b := has_compact.ez Easy.fst

theorem has_n : Realizes regime (fun x : Ticket => x.n) := has_compact.ez (Easy.snd.compose Easy.fst)

theorem has_e : Realizes regime Ticket.e := by
  change regime.Has (fun x => tally x.e)
  rw [show (fun x : Ticket => tally x.e) = (fun x => chooseWidth (tally x.b,tally x.n)) from
    funext fun x => (chooseWidth_tally x.radix_ok x.n).symm]
  exact (has_b.pair has_n).thenDo chooseWidth_poly

theorem toldP : Told regime (fun x : Ticket => x.P) := ⟨fun x d hd => (x.admissible d (by simp [hd])).1,
  has_compact.ez (Easy.snd.compose (Easy.snd.compose Easy.fst))⟩

theorem toldG : Told regime (fun x : Ticket => x.G) := ⟨fun x d hd => (x.admissible d (by simp [hd])).1,
  has_compact.ez (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst)))⟩

theorem toldB : Told regime (fun x : Ticket => x.B) := ⟨fun x d hd => (x.admissible d (by simp [hd])).1,
  has_compact.ez (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.snd)))⟩

open private realized_power told_length room_bounded from OAI.Computability.NearSquareRoot.InterchangeBeadThreshold

theorem has_pad (k : ℕ) : Realizes regime (pad k) := by
  have hd : Realizes regime digitCount := ((((told_length toldP).plus has_e).plus
    (told_length toldG)).plus has_e).plus (told_length toldB)
  exact realized_power ((has_b.times hd).plus (Realizes.fix 1)) k

theorem grid_good (x : Ticket) : BinaryHalo.Good x.grid := ⟨wide _ (toldP.solid x),Nat.two_pow_pos _,
  wide _ (toldG.solid x),wide _ (toldB.solid x),(width_bounds x.radix_ok x.n).2.2.1⟩

private theorem grid_limits (x : Ticket) :
    max (max (room x.P) (2^x.n)) (max (room x.G) (max (x.b^x.e) (room x.B))) ≤ x.total := by
  obtain ⟨hp,hd,hg,hB,hdE⟩ := grid_good x
  change 0 < room x.P at hp
  change 0 < room x.G at hg
  change 0 < room x.B at hB
  change 0 < 2^x.n at hd
  change 2^x.n ≤ x.b^x.e at hdE
  have hE : 0 < x.b^x.e := hd.trans_le hdE
  have bar : ∀ a b c d f : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d → 1 ≤ f →
      max a (max b (max c f)) ≤ a*b*c*d*f := by
    intro a b c d f ha hb hc he hf
    have h1 := Nat.le_mul_of_pos_right a hb
    have h2 := Nat.le_mul_of_pos_left b ha
    have h3 := Nat.le_mul_of_pos_right (a*b) hc
    have h4 := Nat.le_mul_of_pos_left c (Nat.mul_pos ha hb)
    have h5 := Nat.le_mul_of_pos_right (a*b*c) he
    have h6 := Nat.le_mul_of_pos_right (a*b*c*d) hf
    have h7 := Nat.le_mul_of_pos_left f (by positivity : 0 < a*b*c*d)
    omega
  have bound := bar _ _ _ _ _ hp hE hg hE hB
  change _ ≤ room x.P*(x.b^x.e)*room x.G*(x.b^x.e)*room x.B
  omega

private theorem repeatPoly : Poly (fun z : Tally × Tally => List.replicate z.1.length z.2) := by
  apply Poly.of_bound (Code.generate (X:=Tally))
  refine ⟨2,1,fun z => ?_⟩
  rw [one_mul,size_prod,size_tally z.1,pow_two]
  apply Nat.mul_le_mul <;> omega

private theorem fieldShape (b e : ℕ) : shape (field b e) = List.replicate e (tally b) := by
  induction e with
  | zero => rfl
  | succ e ih => simp [field,shape,List.replicate_succ,shape] at ih ⊢; exact ih

private theorem toldNative : Told regime (fun x => field x.b x.e) := by
  refine ⟨fun x d hd => ?_,?_⟩
  · exact (ivory x.radix_ok d hd).1
  · simpa only [Realizes,Function.comp_def,box,tally_length,fieldShape] using
      (has_e.pair has_b).thenDo repeatPoly

/-- Produce the actual unary ordinal counts used by the lexicographic mask. -/
theorem halo_header : Rip regime total (fun _ => 0) regime.header (fun x => send x.grid.header) := by
  have lim := grid_limits
  have p := toldP.station.supply (n:=total) (l:=fun _=>0) (fun x => by rw [space]; have := lim x; omega)
  have g := toldG.station.supply (n:=total) (l:=fun _=>0) (fun x => by rw [space]; have := lim x; omega)
  have z := toldB.station.supply (n:=total) (l:=fun _=>0) (fun x => by rw [space]; have := lim x; omega)
  have h2 := terminal (p:=2) (by decide) (fun x : Ticket => x.n) has_n
  have d := h2.supply (n:=total) (l:=fun _=>0) (fun x => by rw [lineSize]; have := lim x; omega)
  have rfield (b e : ℕ) : room (field b e) = b^e := (population _).symm.trans (Adic.count (p:=b) (l:=e))
  have e := toldNative.station.supply (n:=total) (l:=fun _=>0) (fun x => by rw [space,rfield]; have := lim x; omega)
  have all := p.twice (d.twice (g.twice (e.twice z)))
  simp only [space,rfield] at all
  exact all

end Ticket
end InterchangeROMBinary

end NearSquareRoot
end Computability
end OAI
