import OAI.Computability.BorderVNP.DiagonalTallyRAMSerialize
import OAI.Computability.BorderVNP.DiagonalTallyRAMAcceptance

/-! # The compiled distributed tally table and its literal output bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ}

/-- Result bank obtained before bit serialization. -/
def resultBank (f : Frame) (rs : List (ℕ × ℕ)) (xs : List (List Bool)) (m : Memory w) :
    Memory w :=
  let packed := DiagonalTallyBits.outputMemory (DiagonalTallyScatter.after f.localBase rs m) f.claims xs
  writeTotals f.toTotalsFrame (fun j => ∑ i : Fin f.teams, claimWord f xs i.val j) packed 0 f.dim

/-- The linked native program checks the current team's common row, sums *every* team
on each coordinate, and returns the literal bits of the resulting word totals. -/
theorem complete_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (g : DiagonalTallyUnpack.Frame)
    (rs : List (ℕ × ℕ)) (xs : List (List Bool)) (hi : Input f pub m rs xs)
    (hm : ∀ j < f.dim, DiagonalTallyScatter.after f.localBase rs m (f.localBase+j) =
      claimWord f xs f.team j)
    (hf : g.fits w) (hdir : (pub 0).val+43 < 2^w) (hs : g.src = f.totals)
    (hg : serializeFrame pub (resultBank f rs xs m) g f.dim) :
    ∃ es t m', Runs pub mac complete s m es t m' ∧
      traceCost es ≤ costBound f + serializeSetup.slots+10*g.total+1 ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) ∧
      ∀ c < f.dim, ∀ j < g.width, m' (g.dst+(c*g.width+j)) =
        word w (((∑ i : Fin f.teams, claimWord (w := w) f xs i.val c).val.testBit j).toNat) := by
  obtain ⟨a,u,ra,ha,_⟩ := stage_runs pub mac s m f rs xs hi hm
  obtain ⟨b,t,mt,rb,hb,bits⟩ := serialize_runs pub mac u (resultBank f rs xs m) g f.dim hg hf hdir
  have run : Runs pub mac complete s m (a++b) t mt := ra.seq rb
  refine ⟨a++b,t,mt,run,?_,ordinary_run (by decide) run,?_⟩
  · unfold traceCost
    rw [VPVNP.RAMBuckets.cost_append]; change traceCost a+traceCost b ≤ _; omega
  · intro c hc j hj
    rw [bits c hc j hj, hs, resultBank, writeTotals_at _ _ _ _ _ _ (Nat.zero_le _) (by omega)]

/-- In every accepting execution, including executions of the subsequent bit encoder,
each claim of the current team agrees with the actual subtotal. -/
theorem complete_sound (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (rs : List (ℕ × ℕ)) (xs : List (List Bool))
    (hi : Input f pub m rs xs) {es t mt} (r : Runs pub mac complete s m es t mt) :
    ∀ j < f.dim, DiagonalTallyScatter.after f.localBase rs m (f.localBase+j) =
      claimWord f xs f.team j := by
  cases r with
  | atom h _ _ => cases h
  | seq check _ => exact stage_sound pub mac s m f rs xs hi check

/-- Under the machine-word bound the produced bit is the corresponding bit of the
natural sum, even when the final index offset uses many more bits. -/
theorem claimSum_val (f : Frame) (xs : List (List Bool)) (c : ℕ)
    (a : Fin f.teams → ℕ) (h : ∀ i, claimWord (w := w) f xs i.val c = word w (a i))
    (hfit : ∑ i, a i < 2^w) :
    (∑ i : Fin f.teams, claimWord (w := w) f xs i.val c).val = ∑ i, a i := by
  simp_rw [h]
  exact congrArg Fin.val (word_sum a) |>.trans (word_val _ _ hfit)

/-- The complete compiled table admits exactly its chronological tape of empty
choice lists. Every instruction event on a constructed run has positive sign. -/
theorem complete_execute_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s t : Bank w} {m mt : Memory w} {es} (r : Runs pub mac complete s m es t mt)
    (bits : List (List Bool)) (fs : List (TeamRAM.Event w)) :
    TeamRAM.execute (complete.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
      fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  rw [Code.execute_iff_runs (c := complete) (by decide)]
  constructor
  · rintro ⟨⟨z,mz,run⟩,rfl⟩
    obtain ⟨rfl,_,_⟩ := complete_unique r run
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨t,mt,r⟩,rfl⟩

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
