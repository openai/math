import OAI.Computability.BorderVNP.TransmissionHeaderFields
import OAI.Computability.BorderVNP.TransmissionHeaderNative

/-! # The copied public branch, auxiliary and tally fields on the native evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA DiagonalResidueRAM

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- Recover the actual bit words at the destination of the native common-prefix read. -/
theorem flatAt_of_values (hw : 0 < w) (m : Memory w) (dst : ℕ) (bits : List Bool)
    (values : ∀ i : Fin bits.length, readings m (dst+i.val) = bits[i.val].toNat) : FlatAt m dst bits := by
  intro i
  apply Fin.ext
  rw [word_val _ _ ((Bool.toNat_lt _).trans_le (Nat.one_lt_pow hw.ne' (by decide)))]
  exact values i

/-- Starting from the real processor input and a populated scalar frame, the
evaluation header is read from the physical exterior blocks. Its mode, auxiliary
and subtotal fields occupy separate fixed offsets in the native copy. -/
theorem evaluation_copy {h labels : ℕ} (L : WireLayout (R+1) r link) (G : Wiring R r t d link inner n Edge)
    (u : Fin (R+1)) (pin : Fin d → Bool) (aux : List Bool) (b extra : ℕ)
    (claims : Fin (R+1) → Fin (h+labels) → ℕ)
    (length : 1+aux.length+(R+1)*(h+labels)*b+extra = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool)
    (ibase hbase starbase dst : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hw : 0 < w) :
    let bits := padded (evaluation aux b claims) extra
    let fits : bits.length = L.header := by simpa [bits,padded,evaluation_length] using length
    let ext := exterior L bits fits payload
    let f := G.transferFrame u L.header dst
    (G.processorFields u pin ext ibase hbase starbase).ContainsInput m →
    f.At (readings pub) (readings m) → f.Fits w (pub 0).val →
    ∃ es q mq, Runs pub mac readBroadcast s m es q mq ∧ traceCost es ≤ f.readTicks ∧
      readings mq = f.copied (readings m) L.header ∧ FlatAt mq dst bits ∧
      mq dst = word w 1 ∧ FlatAt mq (dst+1) aux ∧
      DiagonalTallyBits.WordsAt mq (dst+1+aux.length) (DiagonalTallyRAM.broadcast b claims) := by
  intro bits fits ext f physical resident room
  obtain ⟨es,q,mq,run,cost,_,mem,vals⟩ := native_copy L G u pin ext bits fits
    (exterior_header L bits fits payload) ibase hbase starbase dst pub mac s m hw physical resident room
  have flat := flatAt_of_values hw mq dst bits vals
  have fields : FlatAt mq dst (spelling aux (DiagonalTallyRAM.broadcast b claims)) := flat.left
  have mode := fields (⟨0,by simp [spelling]⟩)
  have aux' := (FlatAt.right (xs := [true]) (ys := aux++(DiagonalTallyRAM.broadcast b claims).flatten) fields).left
  exact ⟨es,q,mq,run,cost,mem,flat,by simpa [spelling] using mode,aux',fieldsAt_padded hw dst aux _ extra flat⟩

/-- Supply all tally-stage input hypotheses from scalar layout, stored increment
records and a genuine copied evaluation header. The local scatter preserves those
raw words by the disjoint half-open ranges, giving the stage's required `bitsAt`. -/
theorem tally_input {teams h labels b : ℕ} (claims : Fin teams → Fin (h+labels) → ℕ)
    (aux : List Bool) (extra dst : ℕ) (f : DiagonalTallyRAM.Frame)
    (pub : Arg → Word w) (m : Memory w) (rs : List (ℕ × ℕ)) (hw : 0 < w)
    (copy : FlatAt m dst (padded (evaluation aux b claims) extra))
    (rawBase : f.rawBits = dst+1+aux.length) (nTeams : f.teams = teams)
    (nDim : f.dim = h+labels) (width : f.width = b)
    (fit : f.addressesFit w (pub 0).val) (resident : f.resident pub m)
    (records : DiagonalTallyScatter.RecordsAt m f.records rs) (count : rs.length = f.count)
    (coords : ∀ r ∈ rs, r.1 < f.dim)
    (valuesFit : ∀ a, (m a).val + DiagonalTallyScatter.incrementAt f.localBase a rs < 2^w)
    (recordsDisjoint : DiagonalTallyRAM.separated f.records (2*f.count) f.localBase f.dim)
    (localDir : DiagonalTallyRAM.separated f.localBase f.dim ((pub 0).val+32) 12)
    (claimDir : DiagonalTallyRAM.separated f.claims (f.teams*f.dim) ((pub 0).val+32) 12)
    (rawLocal : DiagonalTallyRAM.separated f.localBase f.dim f.rawBits ((f.teams*f.dim)*f.width))
    (rawClaim : DiagonalTallyRAM.separated f.rawBits ((f.teams*f.dim)*f.width) f.claims (f.teams*f.dim))
    (claimLocal : DiagonalTallyRAM.separated f.localBase f.dim f.claims (f.teams*f.dim))
    (claimBeforeTotal : f.claims+f.dim*f.teams ≤ f.totals) :
    DiagonalTallyRAM.Input f pub m rs (DiagonalTallyRAM.broadcast b claims) := by
  apply DiagonalTallyRAM.Input.of_disjoint f pub m rs _ fit resident records count coords valuesFit
    _ _ _ recordsDisjoint localDir claimDir rawLocal rawClaim claimLocal claimBeforeTotal
  · rw [rawBase]
    exact fieldsAt_padded hw dst aux _ extra copy
  · rw [nTeams,nDim]
    exact field_count claims b
  · rw [width]
    exact field_width claims b

/-- The all-zero branch has the same physical header capacity. Its unique exterior
also zeros every transmission and padding bit, and the copied native branch is zero. -/
theorem unit_copy (L : WireLayout (R+1) r link) (G : Wiring R r t d link inner n Edge)
    (u : Fin (R+1)) (pin : Fin d → Bool) (ibase hbase starbase dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (hw : 0 < w) :
    let bits := unit L.header
    let fits : bits.length = L.header := List.length_replicate
    let ext := exterior L bits fits (fun _ _ _ => false)
    let f := G.transferFrame u L.header dst
    (G.processorFields u pin ext ibase hbase starbase).ContainsInput m →
    f.At (readings pub) (readings m) → f.Fits w (pub 0).val →
    ∃ es q mq, Runs pub mac readBroadcast s m es q mq ∧ traceCost es ≤ f.readTicks ∧
      FlatAt mq dst bits ∧ mq dst = word w 0 := by
  intro bits fits ext f physical resident room
  obtain ⟨es,q,mq,run,cost,_,_,vals⟩ := native_copy L G u pin ext bits fits
    (exterior_header L bits fits _) ibase hbase starbase dst pub mac s m hw physical resident room
  have flat := flatAt_of_values hw mq dst bits vals
  have h : 0 < bits.length := fits ▸ room.branch
  exact ⟨es,q,mq,run,cost,flat,by simpa [bits,unit] using flat ⟨0,h⟩⟩

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
