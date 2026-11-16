module
public import Qsag.Exec.RssParticipantNetwork
public import Qsag.Exec.RssParticipantSponge
public import Qsag.Protocol.Threshold.ThresholdMpc

/-! Executable nonzero participant executions and hostile transcript regressions.
These checks establish computation and state-transition examples, not a randomness
or active-security bound. The wrong-product example is expected to reach pending
unverified evidence; it must not be interpreted as an authorized cut. -/

public section
namespace Qsag.RssParticipant.Checks
set_option autoImplicit false
set_option maxRecDepth 4096

def binding : List UInt8 := [81, 83, 65, 71, 1, 9]
def input : RssKState :=
  ⟨{ zeroKState with a0 := 0x11335577, a7 := 0x91, a22 := 0xab },
   { zeroKState with a0 := 0x22446688, a7 := 0x82, a22 := 0xcd },
   { zeroKState with a0 := 0x33227711, a7 := 0x73, a22 := 0xef }⟩

def tape (round lane : Nat) : RssPrfZeroSeeds :=
  ⟨UInt64.ofNat (17 + 29 * round + lane), UInt64.ofNat (41 + 31 * round + lane),
   UInt64.ofNat (83 + 37 * round + lane)⟩

def localTape (party : Fin 3) (round : Nat) : LocalMasks :=
  if party.val = 0 then mask0 (tape round)
  else if party.val = 1 then mask1 (tape round) else mask2 (tape round)

def honestCommands : List Command :=
  (List.range 24).flatMap fun round =>
    [.compute 0, .compute 1, .compute 2,
     .deliver (3 * round + 1), .deliver (3 * round + 2), .deliver (3 * round)]

def honestExecution : Network :=
  runCommands (some 0) localTape
    ⟨initialNodes binding input keccakRoundConstants 0, []⟩ honestCommands

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

/--72 actual addressed messages,24 retained round records at each party, and
agreement with the existing Keccak evaluator on distinct nonzero share inputs. -/
def permutationCheck : IO Unit := do
  let result := honestExecution
  require (decide (result.emitted.length = 72)) "missing round messages"
  require (decide (result.nodes.n0.evidence.length = 24 ∧
    result.nodes.n1.evidence.length = 24 ∧ result.nodes.n2.evidence.length = 24))
    "missing retained gate evidence"
  require (decide (reconstructedOutput result.nodes =
    some (reconstructRssKState (mpcKeccakF1600Rss input tape))))
    "participant network differed from shared Keccak"
  require (decide ((observe (some 0) result).visiblePayloads.length = 48))
    "corrupt observer saw wrong set of private messages"
  require (decide ((observe none result).visiblePayloads = []))
    "private honest-to-honest payload leaked"
  IO.println "RSS participants:24 rounds,72 addressed messages,600 pending gates per party; shared Keccak equality and private observer projection passed"

def spongeInput : RssByteShares :=
  ⟨List.replicate 96 0x17, List.replicate 96 0x29, List.replicate 96 0x43⟩

def spongeCheck : IO Unit := do
  let customization : List UInt8 := [82, 83, 83, 46, 80, 65, 82, 84, 89]
  let (nodes, output) := cshakeParticipant 32 binding customization spongeInput tape
  let some shares := output | throw (IO.userError "participant cSHAKE aborted")
  require (decide (reconstructRssBytes shares =
    cshake256Xof 32 customization (reconstructRssBytes spongeInput)))
    "participant cSHAKE output mismatch"
  require (decide (nodes.n0.evidence.length = 48 ∧ nodes.n0.cursor = 48))
    "cSHAKE lost evidence or reused round labels across blocks"
  require (decide ((cshakeParticipant 137 binding customization spongeInput tape).2 = none))
    "unsupported output size became a successful cut"
  IO.println "RSS participant cSHAKE:32-byte result matches actual cSHAKE; two blocks retain48 round records; unsupported output is explicit failure"

def hostileTranscriptCheck : IO Unit := do
  let localNode := initialNode 0 binding ⟨zeroKState, zeroKState⟩ [0] 0
  let pending := (prepare localNode (fun _ => (0, 0))).1
  let wrong : Envelope := ⟨1, 0, binding, 0, { zeroKState with a0 := 1 }⟩
  let accepted := receive pending wrong
  require (decide (accepted.phase = .ready ⟨zeroKState, wrong.share⟩))
    "counterexample no longer enters unverified evidence"
  require (decide (accepted.evidence.length = 1)) "wrong value omitted from evidence"
  require (decide ((receive pending { wrong with binding := binding ++ [1] }).phase = .aborted))
    "wrong binding accepted"
  require (decide ((receive pending { wrong with round := 1 }).phase = .aborted))
    "wrong round accepted"
  require (decide ((receive pending { wrong with sender := 2 }).phase = .aborted))
    "wrong sender accepted"
  require (decide ((receive accepted wrong).phase = .aborted)) "replayed message accepted"
  let network : Network := ⟨initialNodes binding zeroRssKState [0] 0, []⟩
  require (decide (networkStep (some 1) localTape network
    (.corruptSend { wrong with sender := 0 }) = network)) "corrupt sender forged honest identity"
  let sent := networkStep (some 1) localTape network (.corruptSend wrong)
  let aborted := networkStep (some 1) localTape sent (.abort 0)
  require (decide (aborted.emitted = [wrong])) "abort erased external history"
  IO.println "RSS hostile transcripts:wrong binding/round/sender and replay abort; forged sender blocked; authenticated wrong value remains pending and requires active gate check"


-- Network invariants are audited at their definition site in RssParticipantNetwork.
end Qsag.RssParticipant.Checks
