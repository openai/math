import OAI.Computability.BorderVNP.FiniteWideBoot
import OAI.Computability.BorderVNP.GeometryAdviceLiteral
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame

/-! # Native installation of the finite-field extended frame at all batch sizes

The boot loader copies the true processor literal bits and installs their decoded
81-word suffix in frame slots 31 through 111. Both phases are deterministic, use
the same addressed memory as the team program, and take linear time in the
number of delivered bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteBoot

open GeometryAdvice RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalTallyBits

/-- Execute the multi-bit loader on the actual initialized frame. -/
theorem read_run {w : ℕ} (a : AdviceLayout) (f : BroadcastFrame) (words : ℕ) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (frame : f.At (readings pub) (readings m)) (layout : a.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (hc : 0 < a.count) (count : a.count = words*w)
    (space : (bootStripe a f words).Fits f w (pub 0).val) :
    ∃ es z, Runs pub mac readWideLiteralAdvice s m es z ((bootStripe a f words).image f.stride m a.count) ∧
      traceCost es ≤ setup.slots+a.count*(copyStripeBit.slots+1)+1 := by
  obtain ⟨es,t,first,ct,hone,hoff,hb,hd,hs,hn,hz⟩ := setup_run a f pub mac s m frame layout fit hc
    (by simpa only [count,bootStripe] using space.denseFit)
  obtain ⟨fs,z,last,ft⟩ := copyStripeLoop_runs (bootStripe a f words) f pub mac t m fit space
    hone hoff hb hd hs (hn.trans count) hz
  refine ⟨es++fs,z,?_,?_⟩
  · rw [count]; exact first.seq last
  · rw [show traceCost (es++fs) = traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    change traceCost fs ≤ (words*w)*(copyStripeBit.slots+1)+1 at ft
    rw [count]
    omega

/-- One fixed program loads the wide literal advice and decodes the extended frame. -/
def installFrame : Code := .seq readWideLiteralAdvice ExtendedFrame.install

/-- Dense source slots lie in the occupied part of the serialized field list. -/
private theorem suffixBits {w : ℕ} (a : AdviceLayout) (f : BroadcastFrame)
    (m : Memory w) (preamble : List (Word w)) (fields : Fin 81 → Word w)
    (count : a.count = (preamble.length+81)*w)
    (physical : ∀ i : Fin (serialized (preamble++List.ofFn fields)).length,
      (m ((bootStripe a f (preamble.length+81)).src f.stride i.val)).val =
        (serialized (preamble++List.ofFn fields))[i.val].toNat) :
    WordsAt ((bootStripe a f (preamble.length+81)).image f.stride m a.count)
      (a.dst+preamble.length*w) ((List.ofFn fields).map wordBits) := by
  apply DiagonalResidueRAM.wordsAt_of_flat
  intro i
  have hl : (serialized (preamble++List.ofFn fields)).length = a.count := by
    simp only [serialized_length,List.length_append,List.length_ofFn,count]
  have hs : (((List.ofFn fields).map wordBits).flatten.length) = 81*w :=
    by simpa only [serialized,List.length_ofFn] using serialized_length (List.ofFn fields)
  have hi : preamble.length*w+i.val < a.count := by have h := i.isLt.trans_eq hs; rw [count,Nat.add_mul]; omega
  let j : Fin (serialized (preamble++List.ofFn fields)).length := ⟨preamble.length*w+i.val,hl ▸ hi⟩
  have src := physical j
  rw [Nat.add_assoc]
  change ((bootStripe a f (preamble.length+81)).image f.stride m a.count
    ((bootStripe a f (preamble.length+81)).dense+(preamble.length*w+i.val))).val = _
  rw [Stripe.image_at m hi,src]
  have he : serialized (preamble++List.ofFn fields) = serialized preamble ++ serialized (List.ofFn fields) := by
    simp [serialized]
  dsimp only [j]
  simp only [he]
  rw [List.getElem_append_right (by rw [serialized_length]; omega)]
  apply congrArg Bool.toNat
  apply getElem_congr rfl
  rw [serialized_length,Nat.add_sub_cancel_left]

/-- Physical deterministic execution from frame 0–30, including the case of a
single processor. The input is the real literal stripe installed on the team. -/
theorem initialize_run {w : ℕ} {L : Pins.Layout} (a : AdviceLayout) (f : BroadcastFrame)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (preamble : List (Word w)) (fields : Fin 81 → Word w) (P : Pins.ProcessorFields L)
    (frame : f.At (readings pub) (readings m)) (pin : Pins.Frame L (readings pub) (readings m))
    (layout : a.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (loaded : ExtendedFrame.Loaded (readings pub) (readings m) a.dst preamble.length w)
    (count : a.count = (preamble.length+81)*w)
    (room : a.offset+width a.count f.processors ≤ f.literal)
    (space : ExtendedFrame.Fits w (pub 0).val a.dst preamble.length)
    (literal : ((bootStripe a f (preamble.length+81)).install P (serialized (preamble++List.ofFn fields))).ContainsInput m) :
    let dest := (bootStripe a f (preamble.length+81)).image f.stride m a.count
    ∃ es z, Runs pub mac installFrame s m es z (ExtendedFrame.installed dest (pub 0).val fields) ∧
      traceCost es ≤ setup.slots+a.count*(copyStripeBit.slots+1)+1 +
        (ExtendedFrame.setup.slots+8*81*(w+1)+8) ∧ ∀ e ∈ es, e.choices = [] ∧ e.sign = .plus := by
  intro dest
  let stripe := bootStripe a f (preamble.length+81)
  have hpos : 0 < w := by
    cases w with
    | zero => have h := space.frameBound; simp at h
    | succ k => exact Nat.zero_lt_succ k
  have hc : 0 < a.count := count ▸ Nat.mul_pos (by omega) hpos
  have hs : stripe.Fits f w (pub 0).val := ⟨Nat.zero_lt_succ _,room,count ▸ capacity a.count f.processors fit.procs,
    space.separate,by simpa only [stripe,bootStripe,Nat.add_mul,Nat.add_assoc] using space.inputBound⟩
  obtain ⟨es,t,first,ct⟩ := read_run a f (preamble.length+81) pub mac s m frame layout fit hc count hs
  obtain ⟨_,teams,proc,lit,link,_,_⟩ := frame
  have procs := proc.symm.trans pin.processors
  have lits := lit.symm.trans pin.literal
  have str : f.stride = L.stride := by
    rw [BroadcastFrame.stride,Pins.Layout.stride,Pins.Layout.offset,teams.symm.trans pin.teams,lits,link.symm.trans pin.link]
    omega
  have physical (i : Fin (serialized (preamble++List.ofFn fields)).length) :
      (m (stripe.src f.stride i.val)).val = (serialized (preamble++List.ofFn fields))[i.val].toNat := by
    have cap := capacity a.count f.processors fit.procs
    have hx := stripe.installed_bit P _ m literal hs.positive (lits ▸ room)
      (by simpa only [serialized_length,List.length_append,List.length_ofFn,←count,←procs,stripe,bootStripe] using cap) i
    rw [str,hx]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Bool.toNat_le _) (Nat.one_lt_two_pow hpos.ne'))
  have words := suffixBits a f m preamble fields count physical
  have unchanged (i : ℕ) (hi : i ≤ 30) :
      frameField (readings pub) (readings dest) i = frameField (readings pub) (readings m) i := by
    change (stripe.image f.stride m a.count ((pub 0).val+i)).val = _
    rw [Stripe.image_outside m (Or.inl (by change (pub 0).val+i < a.dst; have := space.separate; omega))]
    rfl
  have hl : ExtendedFrame.Loaded (readings pub) (readings dest) a.dst preamble.length w :=
    ⟨(unchanged 28 (by decide)).trans loaded.1,(unchanged 29 (by decide)).trans loaded.2.1,
      (unchanged 30 (by decide)).trans loaded.2.2⟩
  obtain ⟨fs,z,last,ft, _unsigned⟩ := ExtendedFrame.install_run pub mac t dest a.dst preamble.length fields hl space words
  let run : Runs pub mac installFrame s m (es++fs) z (ExtendedFrame.installed dest (pub 0).val fields) := first.seq last
  exact ⟨es++fs,z,run,(show traceCost (es++fs)=traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..).trans_le
    (Nat.add_le_add ct ft),run.unsigned_events (by decide)⟩

end FiniteBoot

end BorderVNP
end Computability
end OAI
