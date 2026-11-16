module
/-
# Qsag.Top.ProbPkgGames — the keyed-ROM hiding game as probabilistic packages

The package calculus of `Qsag.Oracle.ProbPkgBridge` instantiated on a game the library already
bounds: the keyed random-oracle hiding game of `Qsag.Oracle.Qrom`.

The library game. A key slot `kStar : Fin cardB` is drawn uniformly. In the real world the
oracle `Fin cardB × TagDom → Cod` answers `(k, tag)` with `secretFn tag` when `k = kStar` and
with `baseO (k, tag)` otherwise; in the ideal world it answers `baseO (k, tag)` always. The
accept counts over the `cardB` keys are `keyedPrfRealAccept` and `keyedPrfIdealAccept`, and
`hidingAdv_le` bounds their difference by `Q` for every `QueryBounded Q` adversary: advantage
at most `Q / cardB`. The library uses this game three times: the Silent-OT punctured GGM leaf
(`ggm_punctured_tree_hiding`), the punctured lattice-preprocessing seed at `2^128`
(`ggm_punctured_seed_keyed_rom_hiding`), and the hidden production coin share at `2^256`
(`production_coin_ro_query_hybrid_bound`).

What is here.
* `keyedRomReal`, `keyedRomIdeal`: the two worlds as `Spec.ProbPkg`s with coin space
  `Fin cardB` (the hidden key) over the oracle interface. `keyedRomReal_winCount` and
  `keyedRomIdeal_winCount` identify their win counts against an embedded `OracleComp`
  adversary with `keyedPrfRealAccept` and `keyedPrfIdealAccept`.
* `keyedRom_hiding_advBoundedOn`: `ProbPkg.AdvBoundedOn` for the class `DistClass.within Q`
  with bound `Q / cardB`, from `hidingAdv_le`.
* `keyedRom_hiding_multiSession`: `K` sessions, bound `K · Q / cardB`. A session is one
  independently keyed copy of the oracle: session `sid` has its own hidden key
  `Spec.sessCoin K ω sid`, and all sessions share the fixed functions `baseO` and `secretFn`
  (`keyedRomReal_session_answer`, `keyedRomIdeal_session_answer`). The distinguisher addresses
  any session at each step, adaptively; `Q` bounds its total number of queries.
  `keyedRom_hiding_multiSession_gameBound` is the same bound as a `Spec.GameBound` on
  `Spec.AdvDist`.
* `productionCoin_hiding_advBoundedOn`, `productionCoin_hiding_multiSession`: the same two
  statements for the hidden production coin share. The key slot is a candidate `256`-bit share,
  the tag is the `(context, party)` frame, and `productionCoinBase oracle` answers with the
  random oracle on `productionCoinCommitFrame`. The single-session bound `Q / 2^256` is taken
  from `production_coin_ro_query_hybrid_bound`. A session is one hidden coin share.

What is not covered. `baseO` and `secretFn` are fixed functions, as in `hidingAdv_le`; the
bound holds for each of them and no averaging over a random `baseO` is done here. Distinguishers
are classical and deterministic. The factor `K` comes from the hybrid argument and is not
tight for this game (a direct count would give `Q / cardB` for a total budget `Q`; that
sharper statement is not proved here). In the `K`-session packages each session has its own
copy of the oracle, programmed at its own hidden key; a single oracle programmed at `K` hidden
keys at once is a different system and is not treated. As in
`production_coin_ro_query_hybrid_bound`, replacing the oracle by concrete cSHAKE and relating
the game to the signing transcript are not part of these statements.
-/

public import Qsag.Oracle.ProbPkgBridge
public import Qsag.Protocol.Threshold.RssSlhFullSecurity
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-- Interface of the keyed oracle: a query is a key slot and a tag. -/
abbrev keyedRomIface (cardB : Nat) (TagDom Cod : Type) : Spec.Iface :=
  Spec.Iface.ofOracle (Fin cardB × TagDom) Cod

/-- The real-world oracle with hidden key `kStar`: slot `kStar` answers with `secretFn`, every
    other slot with `baseO`. -/
@[expose] def keyedRomRealOracle {TagDom Cod : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod) (kStar : Fin cardB) :
    Fin cardB × TagDom → Cod :=
  fun q => if q.1 = kStar then secretFn q.2 else baseO q

/-- Real world of the keyed-ROM hiding game: the coin is the hidden key. -/
def keyedRomReal {TagDom Cod : Type} {cardB : Nat} (baseO : Fin cardB × TagDom → Cod)
    (secretFn : TagDom → Cod) :
    Spec.ProbPkg cardB (keyedRomIface cardB TagDom Cod) Spec.Iface.empty Unit :=
  Spec.ProbPkg.ofOracle (keyedRomRealOracle baseO secretFn)

/-- Ideal world of the keyed-ROM hiding game: `baseO` on every slot, for every coin. -/
def keyedRomIdeal {TagDom Cod : Type} {cardB : Nat} (baseO : Fin cardB × TagDom → Cod) :
    Spec.ProbPkg cardB (keyedRomIface cardB TagDom Cod) Spec.Iface.empty Unit :=
  Spec.ProbPkg.ofOracle (fun _ => baseO)

theorem keyedRomReal_eq {TagDom Cod : Type} {cardB : Nat} (baseO : Fin cardB × TagDom → Cod)
    (secretFn : TagDom → Cod) :
    keyedRomReal baseO secretFn = Spec.ProbPkg.ofOracle (keyedRomRealOracle baseO secretFn) := by
  rfl

theorem keyedRomIdeal_eq {TagDom Cod : Type} {cardB : Nat} (baseO : Fin cardB × TagDom → Cod) :
    keyedRomIdeal baseO = Spec.ProbPkg.ofOracle (fun _ : Fin cardB => baseO) := by rfl

/-- The real package game against an embedded `OracleComp` adversary is the library's real
    accept count. -/
theorem keyedRomReal_winCount {TagDom Cod : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) :
    (keyedRomReal baseO secretFn).winCount (Spec.OracleComp.toCode A) =
      keyedPrfRealAccept cardB baseO secretFn A := by
  rw [keyedPrfRealAccept_def]
  exact Spec.ProbPkg.winCount_ofOracle (keyedRomRealOracle baseO secretFn) A

/-- The ideal package game against an embedded `OracleComp` adversary is the library's ideal
    accept count. -/
theorem keyedRomIdeal_winCount {TagDom Cod : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (A : OracleComp (Fin cardB × TagDom) Cod Bool) :
    (keyedRomIdeal baseO).winCount (Spec.OracleComp.toCode A) =
      keyedPrfIdealAccept cardB baseO A := by
  rw [keyedPrfIdealAccept_def]
  exact Spec.ProbPkg.winCount_ofOracle (fun _ : Fin cardB => baseO) A

/-- **Keyed-ROM hiding as a package bound.** Every distinguisher making at most `Q` queries has
    advantage at most `Q / cardB` between the real and the ideal keyed oracle. The bound is the
    first conjunct of `hidingAdv_le`. -/
theorem keyedRom_hiding_advBoundedOn {TagDom Cod : Type} (cardB Q : Nat) (hCardPos : 0 < cardB)
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod) :
    Spec.ProbPkg.AdvBoundedOn
      ((Spec.DistClass.within Q).mem (keyedRomIface cardB TagDom Cod))
      (keyedRomReal baseO secretFn) (keyedRomIdeal baseO) ⟨Q, cardB, hCardPos⟩ :=
  Spec.ProbPkg.advBoundedOn_ofOracle_within (keyedRomRealOracle baseO secretFn)
    (fun _ => baseO) Q ⟨Q, cardB, hCardPos⟩ (fun A hA => by
      have h := (hidingAdv_le cardB Q hCardPos baseO secretFn A hA).1
      rw [keyedPrfRealAccept_def, keyedPrfIdealAccept_def] at h
      exact Nat.mul_le_mul_right cardB h)

/-- In the `K`-session real world, the query `(k, tag)` to session `sid` is answered with
    `secretFn tag` exactly when `k` is that session's own hidden key. -/
theorem keyedRomReal_session_answer {TagDom Cod : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod) (K : Nat)
    (ω : Fin (Spec.coinPow cardB K)) (st : Spec.SessState Unit K) (sid : Fin K)
    (k : Fin cardB) (tag : TagDom) :
    Spec.Iface.sessResp (I := keyedRomIface cardB TagDom Cod) K sid (k, tag)
        ((((keyedRomReal baseO secretFn).multiSession K).sample ω).closedHandler st
          (Spec.Iface.sessQuery K sid (k, tag))).1 =
      (if k = Spec.sessCoin K ω sid then secretFn tag else baseO (k, tag)) := by
  have h := (Spec.ProbPkg.multiSession_step (keyedRomReal baseO secretFn) K ω st sid (k, tag)).1
  have e := (congrArg
      (fun P : Spec.Pkg (keyedRomIface cardB TagDom Cod) Spec.Iface.empty Unit =>
        P.closedHandler (Spec.SessState.get K st sid) (k, tag))
      (Spec.ProbPkg.ofOracle_sample (keyedRomRealOracle baseO secretFn)
        (Spec.sessCoin K ω sid))).trans
    (Spec.Pkg.ofOracle_closedHandler
      (keyedRomRealOracle baseO secretFn (Spec.sessCoin K ω sid))
      (Spec.SessState.get K st sid) (k, tag))
  exact h.trans (congrArg Prod.fst e)

/-- In the `K`-session ideal world, every session answers with `baseO`. -/
theorem keyedRomIdeal_session_answer {TagDom Cod : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (K : Nat)
    (ω : Fin (Spec.coinPow cardB K)) (st : Spec.SessState Unit K) (sid : Fin K)
    (k : Fin cardB) (tag : TagDom) :
    Spec.Iface.sessResp (I := keyedRomIface cardB TagDom Cod) K sid (k, tag)
        ((((keyedRomIdeal baseO).multiSession K).sample ω).closedHandler st
          (Spec.Iface.sessQuery K sid (k, tag))).1 = baseO (k, tag) := by
  have h := (Spec.ProbPkg.multiSession_step (keyedRomIdeal baseO) K ω st sid (k, tag)).1
  have e := (congrArg
      (fun P : Spec.Pkg (keyedRomIface cardB TagDom Cod) Spec.Iface.empty Unit =>
        P.closedHandler (Spec.SessState.get K st sid) (k, tag))
      (Spec.ProbPkg.ofOracle_sample (fun _ : Fin cardB => baseO)
        (Spec.sessCoin K ω sid))).trans
    (Spec.Pkg.ofOracle_closedHandler baseO (Spec.SessState.get K st sid) (k, tag))
  exact h.trans (congrArg Prod.fst e)

/-- **`K` independently keyed sessions.** Every distinguisher making at most `Q` queries in
    total, spread adaptively over `K` sessions with independent hidden keys, has advantage at
    most `K · Q / cardB` between `K` real and `K` ideal keyed oracles. -/
theorem keyedRom_hiding_multiSession {TagDom Cod : Type} (cardB Q : Nat) (hCardPos : 0 < cardB)
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod) (K : Nat) :
    Spec.ProbPkg.AdvBoundedOn
      ((Spec.DistClass.within Q).mem (Spec.Iface.sessions (keyedRomIface cardB TagDom Cod) K))
      ((keyedRomReal baseO secretFn).multiSession K) ((keyedRomIdeal baseO).multiSession K)
      (Spec.RatBound.scale K ⟨Q, cardB, hCardPos⟩) :=
  Spec.ProbPkg.multiSession_hybrid (Spec.DistClass.within Q) (keyedRomReal baseO secretFn)
    (keyedRomIdeal baseO) ⟨Q, cardB, hCardPos⟩
    (keyedRom_hiding_advBoundedOn cardB Q hCardPos baseO secretFn) K

/-- The `K`-session bound as a `Spec.GameBound` on the `Spec.AdvDist` of the two distinguishing
    games over the coin space `cardB ^ K`. -/
theorem keyedRom_hiding_multiSession_gameBound {TagDom Cod : Type} (cardB Q : Nat)
    (hCardPos : 0 < cardB) (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod)
    (K : Nat) (D : Spec.Code (Spec.Iface.sessions (keyedRomIface cardB TagDom Cod) K) Bool)
    (hD : Spec.Within Q D) :
    Spec.GameBound
      (Spec.AdvDist
        (((keyedRomReal baseO secretFn).multiSession K).game (Spec.coinPow_pos hCardPos K) D)
        (((keyedRomIdeal baseO).multiSession K).game (Spec.coinPow_pos hCardPos K) D))
      ⟨K * Q, cardB, hCardPos⟩ :=
  (Spec.ProbPkg.advBoundedOn_iff_gameBound (Spec.coinPow_pos hCardPos K) _ _ _ _).mp
    (keyedRom_hiding_multiSession cardB Q hCardPos baseO secretFn K) D
    ((Spec.DistClass.mem_within_iff Q D).mpr hD)

/-! ## The hidden production coin share -/

/-- The production coin oracle as a keyed oracle: slot `k` and tag `(ctx, party)` are answered
    by the random oracle on the commit frame of the share `k`. -/
@[expose] def productionCoinBase (oracle : List UInt8 → List UInt8) :
    Fin (2 ^ 256) × (ProductionCoinContext × UInt64) → List UInt8 :=
  fun q => oracle (productionCoinCommitFrame q.2.1 q.2.2 (BitVec.ofFin q.1))

/-- **Hidden production coin share, one session.** Every distinguisher making at most `Q`
    queries has advantage at most `Q / 2^256` between the oracle programmed at the hidden share
    and the unprogrammed oracle. The bound is `production_coin_ro_query_hybrid_bound`. -/
theorem productionCoin_hiding_advBoundedOn (Q : Nat) (oracle : List UInt8 → List UInt8)
    (programmed : ProductionCoinContext × UInt64 → List UInt8) :
    Spec.ProbPkg.AdvBoundedOn
      ((Spec.DistClass.within Q).mem
        (keyedRomIface (2 ^ 256) (ProductionCoinContext × UInt64) (List UInt8)))
      (keyedRomReal (productionCoinBase oracle) programmed)
      (keyedRomIdeal (productionCoinBase oracle)) ⟨Q, 2 ^ 256, Nat.two_pow_pos 256⟩ :=
  Spec.ProbPkg.advBoundedOn_ofOracle_within
    (keyedRomRealOracle (productionCoinBase oracle) programmed)
    (fun _ => productionCoinBase oracle) Q ⟨Q, 2 ^ 256, Nat.two_pow_pos 256⟩ (fun A hA => by
      have h := (production_coin_ro_query_hybrid_bound Q oracle programmed A hA).1
      rw [keyedPrfRealAccept_def, keyedPrfIdealAccept_def] at h
      exact Nat.mul_le_mul_right (2 ^ 256) h)

/-- **`K` hidden production coin shares.** Every distinguisher making at most `Q` queries in
    total over `K` sessions, each with its own independent hidden share, has advantage at most
    `K · Q / 2^256`. -/
theorem productionCoin_hiding_multiSession (Q : Nat) (oracle : List UInt8 → List UInt8)
    (programmed : ProductionCoinContext × UInt64 → List UInt8) (K : Nat) :
    Spec.ProbPkg.AdvBoundedOn
      ((Spec.DistClass.within Q).mem (Spec.Iface.sessions
        (keyedRomIface (2 ^ 256) (ProductionCoinContext × UInt64) (List UInt8)) K))
      ((keyedRomReal (productionCoinBase oracle) programmed).multiSession K)
      ((keyedRomIdeal (productionCoinBase oracle)).multiSession K)
      ⟨K * Q, 2 ^ 256, Nat.two_pow_pos 256⟩ :=
  Spec.ProbPkg.multiSession_hybrid (Spec.DistClass.within Q)
    (keyedRomReal (productionCoinBase oracle) programmed)
    (keyedRomIdeal (productionCoinBase oracle)) ⟨Q, 2 ^ 256, Nat.two_pow_pos 256⟩
    (productionCoin_hiding_advBoundedOn Q oracle programmed) K

#verify_constructive
  Qsag.Top.keyedRomReal_winCount
  Qsag.Top.keyedRomIdeal_winCount
  Qsag.Top.keyedRom_hiding_advBoundedOn
  Qsag.Top.keyedRomReal_session_answer
  Qsag.Top.keyedRomIdeal_session_answer
  Qsag.Top.keyedRom_hiding_multiSession
  Qsag.Top.keyedRom_hiding_multiSession_gameBound
  Qsag.Top.productionCoin_hiding_advBoundedOn
  Qsag.Top.productionCoin_hiding_multiSession

end Qsag.Top
end
