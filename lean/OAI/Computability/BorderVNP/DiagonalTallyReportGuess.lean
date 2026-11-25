import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay
import OAI.Computability.BorderVNP.DiagonalResidueRAMLoad
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Exactly one native guess per actual supplemental report bit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

/-- The public length has already been computed from the owned cell's actual
weighted positions and fixed gadget fields. Registers 22 and 18 are its base and length. -/
def guessSetup : Code := .block [.copy 33 18,.constant 38 1,.constant 39 0,.copy 40 22,.constant 41 0]

/-- Guess the compact report bank once, before the cell's private macro reads it. -/
def guessReports : Code := .seq guessSetup (.whileLt 41 33 guessBody)

/-- Any prescribed sequence of raw report bits has one positive native run; only
its compact external interval is written. Registers below 33 remain caller-owned. -/
theorem guessReports_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (start : ℕ) (bs : List Bool) (hs : (s 22).val=start)
    (hn : (s 18).val=bs.length) (hspace : start+bs.length<2^w) :
    ∃ es z, Runs pub mac guessReports s m es z (putBits m start bs) ∧
      TraceOK es bs (6*bs.length+6) ∧ (∀ j : Reg, j.val<33 → z j=s j) := by
  let a := effect false s m guessSetup
  let d : Frame := ⟨(s 32).val,bs.length,(s 34).val,(s 35).val,(s 36).val,(s 37).val⟩
  have valword (x : Word w) : x=word w x.val := Fin.ext (word_val w x.val x.isLt).symm
  have header : d.stable a.bank ∧ a.bank 41=word w 0 ∧ a.bank 40=word w start ∧ a.mem=m ∧
      TraceOK a.trace [] 5 := by
    simp [a,d,guessSetup,Code.block,effect,Frame.stable,Frame.loaded,Function.update,TraceOK,tick,
      ← hn,← hs]
    exact ⟨⟨⟨valword _,valword _,valword _,valword _,valword _,valword _⟩,rfl⟩,valword _⟩
  obtain ⟨stable,i,cur,mem,tr⟩ := header
  obtain ⟨z,⟨es,rr,hr⟩,_,_⟩ := guess_loop pub mac d bs a.bank m 0 start
    stable i cur (by simp [d]) (by change bs.length<2^w; omega) hspace
  have first := effect_runs pub mac false s m guessSetup (by decide)
  change Runs pub mac guessSetup s m a.trace a.bank a.mem at first
  rw [mem] at first
  refine ⟨_,z,first.seq rr,?_,?_⟩
  · rw [show 6*bs.length+6=5+(6*bs.length+1) by omega]
    simpa only [List.nil_append] using tr.append hr
  intro j hj
  have keeps : ∀ r : Reg, r.val<33 → guessReports.keeps r=true := by decide
  exact (first.seq rr).keepsReg (keeps j hj)

/-- Every returning path guesses exactly the bits it wrote. This includes arbitrary
machine tapes, even if a caller supplies extra choices. -/
theorem guessReports_cover {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (start len : ℕ) (hs : (s 22).val=start) (hn : (s 18).val=len)
    (hspace : start+len<2^w) {es z mt} (run : Runs pub mac guessReports s m es z mt) :
    ∃ bs, bs.length=len ∧ TraceOK es bs (6*len+6) ∧ mt=putBits m start bs := by
  let stream := es.flatMap TeamRAM.Event.choices ++ List.replicate len false
  have hlen : len ≤ stream.length := by simp [stream]
  let bs := stream.take len
  have hb : bs.length=len := by simp [bs,hlen]
  obtain ⟨fs,t,r,tr,_⟩ := guessReports_runs pub mac s m start bs hs (hn.trans hb.symm) (hb ▸ hspace)
  have he : es.flatMap TeamRAM.Event.choices ++ List.replicate len false =
      fs.flatMap TeamRAM.Event.choices ++ stream.drop len := by rw [tr.2.1]; exact (List.take_append_drop ..).symm
  obtain ⟨rfl,_,hm⟩ := unique_returns (c := guessReports) (by decide) run r he
  exact ⟨bs,hb,hb ▸ tr,hm⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
