module
/-
# Qsag.Custody.MacaroonAttenuation: chained-MAC bearer capabilities

A model of `crates/qsag-policy/src/macaroon.rs` over an abstract keyed function, and three
results about it.

The keyed function is a `MacSuite B T`: `root` (the cSHAKE256 call under `QSAG.MACAROON.ROOT.V1`
on key, discharge flag, identifier, audience), `chain` (the call under `QSAG.MACAROON.CAVEAT.V1`
on the previous tag and one caveat) and `bind` (the call under `QSAG.MACAROON.BIND.V1` on a
final tag). `B` stands for the 32-byte strings (keys, identifiers, audiences, resources,
binding commitments) and `T` for tags. The checker `verify` follows `SpongeMacaroon::verify`
statement by statement, error codes included; `verifierVerify` follows `MacaroonVerifier::verify`.

1. Attenuation is monotone. `authorized_of_caveat_subset` is the general form: a genuine token
   whose caveats all occur in an authorized token, or hold for the request, is authorized.
   `attenuation_narrows` and `attenuation_firstParty_exact` are the appended-caveat cases.
   Discharges are bound to the tag of the token they serve, so the presentation changes with
   the token; `Authorized` therefore quantifies over the discharges presented, each checked
   under the key the deployment's registry holds for its identifier.
2. Editing a chain is a forgery. `editWitness` is a function of the two caveat lists and the
   presented tag only. For any two chains accepted under one root tag where the second caveat
   list does not extend the first, it wins the prefix-free forgery game of the cascade
   `chainFrom` under the hidden link key at the point where the lists part
   (`edit_yields_cascade_forgery`). `Edit` covers removal, truncation, reordering and
   modification. Truncation and a changed last caveat give a forgery against one `chain` call
   (`truncation_exposes_link_key`, `last_caveat_swap_is_one_step_forgery`).
3. Discharges. An accepted discharge is authentic under the key supplied for it, carries the
   commitment `bind` of the presenting token's tag and no other (`accepted_discharge_bound`),
   so it cannot serve a second token unless `bind` agrees on both tags
   (`discharge_not_transplantable`). Binding and checking use the parent tag through `bind`
   only (`bindDischarge_factors_through_binding`, `checkPrimary_factors_through_binding`).

Not covered: the wire format (`to_bytes`, `from_bytes`) and the caveat byte encoding, so `chain`
takes the caveat itself; the reduction from the cascade game to the pseudorandomness of cSHAKE256;
any statement about what `bind` hides, which is a one-wayness assumption on the suite.
-/

public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.MacaroonAttenuation
set_option autoImplicit false

/-! ## 1. Model -/

inductive CapError where
  | malformed | tooManyCaveats | invalidTag | denied
  | missingDischarge | unboundDischarge | unusedDischarge
  deriving DecidableEq

inductive Caveat (B : Type) where
  | expiresAt (t : BitVec 64)
  | notBefore (t : BitVec 64)
  | resource (v : B)
  | actions (mask : BitVec 64)
  | maxAmount (max : BitVec 128)
  | bindToParent (binding : B)
  | thirdParty (id : B)
  deriving DecidableEq

structure Request (B : Type) where
  audience : B
  resource : B
  actions : BitVec 64
  amount : BitVec 128
  now : BitVec 64

structure Token (B T : Type) where
  discharge : Bool
  identifier : B
  audience : B
  caveats : List (Caveat B)
  tag : T

/-- A discharge with the key the verifier's authority registry selected for it. -/
structure Discharge (B T : Type) where
  token : Token B T
  rootKey : B

structure MacSuite (B T : Type) where
  root : B → Bool → B → B → T
  chain : T → Caveat B → T
  bind : T → B

variable {B T : Type}

def maxCaveats : Nat := 64

def Caveat.isBind : Caveat B → Bool
  | .bindToParent _ => true
  | _ => false

def Caveat.isThirdParty : Caveat B → Bool
  | .thirdParty _ => true
  | _ => false

/-- The request test of a first-party caveat; `false` on the two structural caveats. -/
def Caveat.holds [DecidableEq B] (r : Request B) : Caveat B → Bool
  | .expiresAt t => decide (r.now < t)
  | .notBefore t => decide (t ≤ r.now)
  | .resource v => decide (v = r.resource)
  | .actions mask => decide (r.actions &&& ~~~mask = 0#64)
  | .maxAmount max => decide (r.amount ≤ max)
  | .bindToParent _ => false
  | .thirdParty _ => false

instance : DecidableEq (Except CapError Unit) := fun a b =>
  match a, b with
  | .ok _, .ok _ => isTrue rfl
  | .error e, .error e' =>
    if h : e = e' then isTrue (congrArg Except.error h)
    else isFalse fun h' => h (by cases h'; rfl)
  | .ok _, .error _ => isFalse fun h => nomatch h
  | .error _, .ok _ => isFalse fun h => nomatch h

def require (b : Bool) (e : CapError) : Except CapError Unit :=
  if b then .ok () else .error e

def andThen (x y : Except CapError Unit) : Except CapError Unit :=
  match x with
  | .ok _ => y
  | .error e => .error e

/-- One iteration of the caveat loop of `check`; the value says whether a binding matched. -/
def caveatStep [DecidableEq B] (r : Request B) (parent : Option B)
    (tp : B → Except CapError Unit) (c : Caveat B) : Except CapError Bool :=
  match c with
  | .bindToParent b => if parent = some b then .ok true else .error .denied
  | .thirdParty id =>
    if parent.isSome then .error .denied
    else match tp id with
      | .ok _ => .ok false
      | .error e => .error e
  | _ => if c.holds r then .ok false else .error .denied

def checkLoop [DecidableEq B] (r : Request B) (parent : Option B)
    (tp : B → Except CapError Unit) : Bool → List (Caveat B) → Except CapError Bool
  | bound, [] => .ok bound
  | bound, c :: cs =>
    match caveatStep r parent tp c with
    | .error e => .error e
    | .ok m => checkLoop r parent tp (bound || m) cs

/-- `SpongeMacaroon::check`, with the third-party branch abstracted as `tp`. -/
def checkToken [DecidableEq B] (tok : Token B T) (r : Request B) (parent : Option B)
    (tp : B → Except CapError Unit) : Except CapError Unit :=
  andThen (require (decide (tok.audience = r.audience)) .denied)
    (match checkLoop r parent tp false tok.caveats with
      | .error e => .error e
      | .ok bound => require (!(tok.discharge && !bound)) .unboundDischarge)

@[expose] def chainFrom (S : MacSuite B T) (t : T) (cs : List (Caveat B)) : T :=
  cs.foldl S.chain t

def rootTag (S : MacSuite B T) (key : B) (tok : Token B T) : T :=
  S.root key tok.discharge tok.identifier tok.audience

def Authentic (S : MacSuite B T) (key : B) (tok : Token B T) : Prop :=
  chainFrom S (rootTag S key tok) tok.caveats = tok.tag

def authenticateFrom [DecidableEq T] (S : MacSuite B T) (rootT : T) (tok : Token B T) :
    Except CapError Unit :=
  require (decide (chainFrom S rootT tok.caveats = tok.tag)) .invalidTag

def authenticate [DecidableEq T] (S : MacSuite B T) (key : B) (tok : Token B T) :
    Except CapError Unit :=
  authenticateFrom S (rootTag S key tok) tok

def deny (_ : B) : Except CapError Unit := .error .denied

/-- The discharge side of the third-party branch: authenticate, then check against the
commitment `pb` of the presenting token. -/
def dischargeCheck [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (r : Request B) (pb : B)
    (d : Discharge B T) : Except CapError Unit :=
  andThen (authenticate S d.rootKey d.token) (checkToken d.token r (some pb) deny)

def lookupResult (dcheck : Discharge B T → Except CapError Unit) :
    List (Discharge B T) → Except CapError Unit
  | [] => .error .missingDischarge
  | [d] => if d.token.discharge then dcheck d else .error .denied
  | _ :: _ :: _ => .error .denied

def tpLookup [DecidableEq B] (dcheck : Discharge B T → Except CapError Unit)
    (ds : List (Discharge B T)) (id : B) : Except CapError Unit :=
  lookupResult dcheck (ds.filter fun d => decide (d.token.identifier = id))

def hasThirdParty [DecidableEq B] (cs : List (Caveat B)) (id : B) : Bool :=
  cs.any fun c => decide (c = .thirdParty id)

/-- `SpongeMacaroon::check_primary`, with the discharge check as a parameter. -/
def checkPrimaryWith [DecidableEq B] (dcheck : Discharge B T → Except CapError Unit)
    (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) : Except CapError Unit :=
  andThen (require (decide (ds.length ≤ tok.caveats.length)) .unusedDischarge)
    (andThen (checkToken tok r none (tpLookup dcheck ds))
      (require (!ds.any fun d => !hasThirdParty tok.caveats d.token.identifier)
        .unusedDischarge))

def checkPrimary [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (tok : Token B T)
    (r : Request B) (ds : List (Discharge B T)) : Except CapError Unit :=
  checkPrimaryWith (dischargeCheck S r (S.bind tok.tag)) tok r ds

/-- `SpongeMacaroon::verify`. -/
@[expose] def verify [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B) (tok : Token B T)
    (r : Request B) (ds : List (Discharge B T)) : Except CapError Unit :=
  andThen (require (!tok.discharge) .denied)
    (andThen (authenticate S key tok) (checkPrimary S tok r ds))

/-- One issued session and the registry of third-party keys the service trusts. -/
structure Deployment (B : Type) where
  key : B
  identifier : B
  audience : B
  registry : B → B

/-- `MacaroonVerifier::verify` for the verifier built from `dep`. -/
def verifierVerify [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (dep : Deployment B)
    (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) : Except CapError Unit :=
  andThen
    (require (!(tok.discharge || !decide (dep.identifier = tok.identifier)
      || !decide (dep.audience = tok.audience))) .denied)
    (andThen (authenticateFrom S (S.root dep.key false dep.identifier dep.audience) tok)
      (checkPrimary S tok r ds))

def issue (S : MacSuite B T) (key id aud : B) : Token B T :=
  ⟨false, id, aud, [], S.root key false id aud⟩

def issueDischarge (S : MacSuite B T) (key id aud : B) : Token B T :=
  ⟨true, id, aud, [], S.root key true id aud⟩

def attenuate (S : MacSuite B T) (tok : Token B T) (c : Caveat B) : Except CapError (Token B T) :=
  if maxCaveats ≤ tok.caveats.length then .error .tooManyCaveats
  else if (!tok.discharge && c.isBind) || (tok.discharge && c.isThirdParty) then .error .denied
  else .ok { tok with caveats := tok.caveats ++ [c], tag := S.chain tok.tag c }

/-- `bind_discharge` as a function of what it reads from the parent: its flag, its audience
and the commitment to its tag. -/
def bindDischargeWith [DecidableEq B] (S : MacSuite B T) (parentIsDischarge : Bool)
    (parentAudience binding : B) (d : Token B T) : Except CapError (Token B T) :=
  if parentIsDischarge || !d.discharge || !decide (parentAudience = d.audience) then .error .denied
  else attenuate S d (.bindToParent binding)

def bindDischarge [DecidableEq B] (S : MacSuite B T) (parent d : Token B T) :
    Except CapError (Token B T) :=
  bindDischargeWith S parent.discharge parent.audience (S.bind parent.tag) d

/-! ## 2. What acceptance means -/

theorem require_ok_iff (b : Bool) (e : CapError) : require b e = .ok () ↔ b = true := by
  cases b
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem andThen_ok_iff (x y : Except CapError Unit) :
    andThen x y = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | ok u => exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

def CaveatOk [DecidableEq B] (r : Request B) (parent : Option B)
    (tp : B → Except CapError Unit) (c : Caveat B) : Prop :=
  ∃ m, caveatStep r parent tp c = .ok m

theorem caveatStep_ok_isBind [DecidableEq B] {r : Request B} {p : Option B}
    {tp : B → Except CapError Unit} {c : Caveat B} {m : Bool}
    (h : caveatStep r p tp c = .ok m) : m = c.isBind := by
  cases c <;> simp only [caveatStep, Caveat.isBind] at h ⊢ <;> split at h <;>
    first
      | (cases h; rfl)
      | (cases h; done)
      | (split at h <;> first | (cases h; rfl) | (cases h; done))

theorem checkLoop_ok_iff [DecidableEq B] (r : Request B) (p : Option B)
    (tp : B → Except CapError Unit) (cs : List (Caveat B)) (b b' : Bool) :
    checkLoop r p tp b cs = .ok b' ↔
      (∀ c ∈ cs, CaveatOk r p tp c) ∧ b' = (b || cs.any Caveat.isBind) := by
  induction cs generalizing b with
  | nil =>
    simp only [checkLoop, List.any_nil, Bool.or_false]
    constructor
    · intro h
      cases h
      exact ⟨fun c hc => (nomatch hc), rfl⟩
    · intro h
      rw [h.2]
  | cons c cs ih =>
    cases hstep : caveatStep r p tp c with
    | error e =>
      simp only [checkLoop, hstep]
      constructor
      · intro h
        cases h
      · intro h
        obtain ⟨m, hm⟩ := h.1 c List.mem_cons_self
        rw [hstep] at hm
        cases hm
    | ok m =>
      simp only [checkLoop, hstep]
      rw [ih, caveatStep_ok_isBind hstep, List.any_cons, Bool.or_assoc]
      constructor
      · intro h
        refine ⟨fun c' hc' => ?_, h.2⟩
        rcases List.mem_cons.mp hc' with heq | hmem
        · rw [heq]
          exact ⟨m, hstep⟩
        · exact h.1 c' hmem
      · intro h
        exact ⟨fun c' hc' => h.1 c' (List.mem_cons_of_mem _ hc'), h.2⟩

theorem checkToken_ok_iff [DecidableEq B] (tok : Token B T) (r : Request B) (p : Option B)
    (tp : B → Except CapError Unit) :
    checkToken tok r p tp = .ok () ↔
      tok.audience = r.audience ∧ (∀ c ∈ tok.caveats, CaveatOk r p tp c) ∧
        (tok.discharge = true → tok.caveats.any Caveat.isBind = true) := by
  unfold checkToken
  rw [andThen_ok_iff, require_ok_iff, decide_eq_true_iff]
  refine and_congr_right fun _ => ?_
  cases hloop : checkLoop r p tp false tok.caveats with
  | error e =>
    constructor
    · intro h
      cases h
    · intro h
      have := (checkLoop_ok_iff r p tp tok.caveats false (false || tok.caveats.any Caveat.isBind)).mpr
        ⟨h.1, rfl⟩
      rw [hloop] at this
      cases this
  | ok bound =>
    have hb := (checkLoop_ok_iff r p tp tok.caveats false bound).mp hloop
    simp only [require_ok_iff]
    rw [hb.2, Bool.false_or]
    constructor
    · intro h
      refine ⟨hb.1, fun hd => ?_⟩
      rw [hd] at h
      cases hany : tok.caveats.any Caveat.isBind
      · rw [hany] at h
        cases h
      · rfl
    · intro h
      cases hd : tok.discharge
      · rfl
      · rw [h.2 hd]
        rfl

theorem lookupResult_ok_iff (dcheck : Discharge B T → Except CapError Unit)
    (l : List (Discharge B T)) :
    lookupResult dcheck l = .ok () ↔
      ∃ d, l = [d] ∧ d.token.discharge = true ∧ dcheck d = .ok () := by
  match l with
  | [] => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | [d] =>
    simp only [lookupResult]
    constructor
    · intro h
      cases hd : d.token.discharge
      · rw [hd] at h
        cases h
      · rw [hd] at h
        exact ⟨d, rfl, hd, h⟩
    · intro ⟨d', heq, hd, h⟩
      cases heq
      rw [hd]
      exact h
  | _ :: _ :: _ => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩

theorem dischargeCheck_ok_iff [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (r : Request B)
    (pb : B) (d : Discharge B T) :
    dischargeCheck S r pb d = .ok () ↔
      Authentic S d.rootKey d.token ∧ checkToken d.token r (some pb) deny = .ok () := by
  unfold dischargeCheck authenticate authenticateFrom Authentic
  rw [andThen_ok_iff, require_ok_iff, decide_eq_true_iff]

theorem hasThirdParty_iff [DecidableEq B] (cs : List (Caveat B)) (id : B) :
    hasThirdParty cs id = true ↔ Caveat.thirdParty id ∈ cs := by
  unfold hasThirdParty
  rw [List.any_eq_true]
  constructor
  · intro ⟨c, hc, h⟩
    rw [← of_decide_eq_true h]
    exact hc
  · intro h
    exact ⟨_, h, decide_eq_true rfl⟩

/-- The authorization half of acceptance: everything `check_primary` tests. -/
def PrimaryOk [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (tok : Token B T)
    (r : Request B) (ds : List (Discharge B T)) : Prop :=
  ds.length ≤ tok.caveats.length ∧
    checkToken tok r none (tpLookup (dischargeCheck S r (S.bind tok.tag)) ds) = .ok () ∧
    ∀ d ∈ ds, Caveat.thirdParty d.token.identifier ∈ tok.caveats

theorem checkPrimary_ok_iff [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (tok : Token B T)
    (r : Request B) (ds : List (Discharge B T)) :
    checkPrimary S tok r ds = .ok () ↔ PrimaryOk S tok r ds := by
  unfold checkPrimary checkPrimaryWith PrimaryOk
  rw [andThen_ok_iff, andThen_ok_iff, require_ok_iff, require_ok_iff, decide_eq_true_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h d hd
    cases hx : hasThirdParty tok.caveats d.token.identifier
    · have : (ds.any fun d => !hasThirdParty tok.caveats d.token.identifier) = true :=
        List.any_eq_true.mpr ⟨d, hd, by rw [hx]; rfl⟩
      rw [this] at h
      cases h
    · exact (hasThirdParty_iff _ _).mp hx
  · intro h
    cases hany : ds.any fun d => !hasThirdParty tok.caveats d.token.identifier
    · rfl
    · obtain ⟨d, hd, hx⟩ := List.any_eq_true.mp hany
      rw [(hasThirdParty_iff _ _).mpr (h d hd)] at hx
      cases hx

theorem verify_ok_iff [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B)
    (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) :
    verify S key tok r ds = .ok () ↔
      tok.discharge = false ∧ Authentic S key tok ∧ PrimaryOk S tok r ds := by
  unfold verify authenticate authenticateFrom Authentic
  rw [andThen_ok_iff, andThen_ok_iff, require_ok_iff, require_ok_iff, decide_eq_true_iff,
    checkPrimary_ok_iff, Bool.not_eq_true']

/-- A token of the deployment's session whose tag is the chain over its caveats. -/
def Genuine (S : MacSuite B T) (dep : Deployment B) (tok : Token B T) : Prop :=
  tok.discharge = false ∧ dep.identifier = tok.identifier ∧ dep.audience = tok.audience ∧
    chainFrom S (S.root dep.key false dep.identifier dep.audience) tok.caveats = tok.tag

theorem Genuine.bindings {S : MacSuite B T} {dep : Deployment B} {tok : Token B T}
    (h : Genuine S dep tok) : dep.identifier = tok.identifier ∧ dep.audience = tok.audience :=
  ⟨h.2.1, h.2.2.1⟩

theorem verifierVerify_ok_iff [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) :
    verifierVerify S dep tok r ds = .ok () ↔ Genuine S dep tok ∧ PrimaryOk S tok r ds := by
  unfold verifierVerify authenticateFrom Genuine
  rw [andThen_ok_iff, andThen_ok_iff, require_ok_iff, require_ok_iff, decide_eq_true_iff,
    checkPrimary_ok_iff]
  constructor
  · intro ⟨hhdr, hchain, hprim⟩
    cases hd : tok.discharge
    · by_cases hi : dep.identifier = tok.identifier
      · by_cases ha : dep.audience = tok.audience
        · exact ⟨⟨rfl, hi, ha, hchain⟩, hprim⟩
        · rw [hd, decide_eq_true hi, decide_eq_false ha] at hhdr
          cases hhdr
      · rw [hd, decide_eq_false hi] at hhdr
        cases hhdr
    · rw [hd] at hhdr
      cases hhdr
  · intro ⟨⟨hd, hi, ha, hchain⟩, hprim⟩
    refine ⟨?_, hchain, hprim⟩
    rw [hd, decide_eq_true hi, decide_eq_true ha]
    rfl

/-- The verifier handle and the keyed entry point accept the same presentations. -/
theorem verifierVerify_eq_verify_ok [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : Request B) (ds : List (Discharge B T))
    (hi : dep.identifier = tok.identifier) (ha : dep.audience = tok.audience) :
    verifierVerify S dep tok r ds = .ok () ↔ verify S dep.key tok r ds = .ok () := by
  rw [verifierVerify_ok_iff, verify_ok_iff]
  unfold Genuine Authentic rootTag
  constructor
  · intro ⟨⟨hd, _, _, hc⟩, hp⟩
    refine ⟨hd, ?_, hp⟩
    rw [hd, ← hi, ← ha]
    exact hc
  · intro ⟨hd, hc, hp⟩
    refine ⟨⟨hd, hi, ha, ?_⟩, hp⟩
    rw [hd, ← hi, ← ha] at hc
    exact hc

/-! ## 3. Attenuation is monotone -/

theorem caveatOk_of_holds [DecidableEq B] {r : Request B} {p : Option B}
    {tp : B → Except CapError Unit} {c : Caveat B} (h : c.holds r = true) : CaveatOk r p tp c := by
  cases c <;> first
    | exact ⟨false, by simp only [caveatStep]; rw [h]; rfl⟩
    | exact nomatch h

theorem caveatOk_none_cases [DecidableEq B] {r : Request B} {tp : B → Except CapError Unit}
    {c : Caveat B} (h : CaveatOk r none tp c) :
    c.holds r = true ∨ ∃ id, c = .thirdParty id ∧ tp id = .ok () := by
  obtain ⟨m, hm⟩ := h
  cases c with
  | bindToParent b =>
    simp only [caveatStep] at hm
    split at hm
    · rename_i hc
      cases hc
    · cases hm
  | thirdParty id =>
    refine .inr ⟨id, rfl, ?_⟩
    simp only [caveatStep] at hm
    split at hm
    · rename_i hc
      cases hc
    · cases htp : tp id with
      | error e =>
        rw [htp] at hm
        cases hm
      | ok u => rfl
  | expiresAt t | notBefore t | resource v | actions mask | maxAmount max =>
    left
    simp only [caveatStep] at hm
    split at hm
    · assumption
    · cases hm

theorem caveatOk_thirdParty [DecidableEq B] {r : Request B} {tp : B → Except CapError Unit}
    {id : B} (h : tp id = .ok ()) : CaveatOk r none tp (.thirdParty id) := by
  refine ⟨false, ?_⟩
  simp only [caveatStep, h]
  rfl

theorem caveatOk_bind_iff [DecidableEq B] {r : Request B} {tp : B → Except CapError Unit}
    {p b : B} : CaveatOk r (some p) tp (.bindToParent b) ↔ b = p := by
  constructor
  · intro ⟨m, hm⟩
    simp only [caveatStep] at hm
    split at hm
    · rename_i hc
      exact (Option.some.inj hc).symm
    · cases hm
  · intro h
    refine ⟨true, ?_⟩
    simp only [caveatStep, h]
    rfl

def rebindCaveat (b : B) : Caveat B → Caveat B
  | .bindToParent _ => .bindToParent b
  | c => c

/-- The same discharge re-issued for another parent commitment. It is built with the
discharge's own root key: only the third party can do this, and `Authorized` asks whether a
presentation exists, not who can produce it. -/
def rebind (S : MacSuite B T) (b : B) (d : Discharge B T) : Discharge B T :=
  ⟨{ d.token with
      caveats := d.token.caveats.map (rebindCaveat b)
      tag := chainFrom S (rootTag S d.rootKey d.token) (d.token.caveats.map (rebindCaveat b)) },
    d.rootKey⟩

/-- The discharges of a presentation that `tok` still asks for, re-bound to `tok`. -/
def shrink [DecidableEq B] (S : MacSuite B T) (tok : Token B T) (ds : List (Discharge B T)) :
    List (Discharge B T) :=
  (ds.filter fun d => hasThirdParty tok.caveats d.token.identifier).map (rebind S (S.bind tok.tag))

theorem caveatOk_rebind [DecidableEq B] {r : Request B} {b' b : B} {c : Caveat B}
    (h : CaveatOk r (some b') deny c) : CaveatOk r (some b) deny (rebindCaveat b c) := by
  cases c with
  | bindToParent x => exact caveatOk_bind_iff.mpr rfl
  | thirdParty id =>
    obtain ⟨m, hm⟩ := h
    simp only [caveatStep] at hm
    split at hm
    · cases hm
    · rename_i hc
      exact absurd rfl hc
  | expiresAt t | notBefore t | resource v | actions mask | maxAmount max =>
    obtain ⟨m, hm⟩ := h
    exact ⟨m, hm⟩

theorem isBind_rebindCaveat (b : B) (c : Caveat B) : (rebindCaveat b c).isBind = c.isBind := by
  cases c <;> rfl

theorem rebind_check [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (r : Request B)
    (b' b : B) (d : Discharge B T) (h : dischargeCheck S r b' d = .ok ()) :
    dischargeCheck S r b (rebind S b d) = .ok () := by
  rw [dischargeCheck_ok_iff] at h ⊢
  refine ⟨rfl, ?_⟩
  have hc := (checkToken_ok_iff _ _ _ _).mp h.2
  refine (checkToken_ok_iff _ _ _ _).mpr ⟨hc.1, ?_, ?_⟩
  · intro c hc'
    obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc'
    rw [← heq]
    exact caveatOk_rebind (hc.2.1 c₀ hc₀)
  · intro hd
    obtain ⟨c₀, hc₀, hb⟩ := List.any_eq_true.mp (hc.2.2 hd)
    exact List.any_eq_true.mpr
      ⟨rebindCaveat b c₀, List.mem_map.mpr ⟨c₀, hc₀, rfl⟩, by rw [isBind_rebindCaveat]; exact hb⟩

theorem tpLookup_shrink [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (r : Request B)
    (tok : Token B T) (b' : B) (ds : List (Discharge B T)) (id : B)
    (hid : Caveat.thirdParty id ∈ tok.caveats)
    (h : tpLookup (dischargeCheck S r b') ds id = .ok ()) :
    tpLookup (dischargeCheck S r (S.bind tok.tag)) (shrink S tok ds) id = .ok () := by
  unfold tpLookup at h ⊢
  obtain ⟨d, hf, hflag, hd⟩ := (lookupResult_ok_iff _ _).mp h
  refine (lookupResult_ok_iff _ _).mpr ⟨rebind S (S.bind tok.tag) d, ?_, hflag, rebind_check S r _ _ d hd⟩
  have hdid : d.token.identifier = id := by
    have hmem : d ∈ ds.filter fun d => decide (d.token.identifier = id) := by
      rw [hf]
      exact List.mem_singleton.mpr rfl
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  unfold shrink
  rw [List.filter_map]
  have hswap : (ds.filter fun d => hasThirdParty tok.caveats d.token.identifier).filter
        ((fun d : Discharge B T => decide (d.token.identifier = id)) ∘ rebind S (S.bind tok.tag)) =
      (ds.filter fun d => decide (d.token.identifier = id)).filter
        fun d => hasThirdParty tok.caveats d.token.identifier := by
    rw [List.filter_filter, List.filter_filter]
    refine List.filter_congr fun x _ => ?_
    exact Bool.and_comm _ _
  rw [hswap, hf]
  have hkeep : hasThirdParty tok.caveats d.token.identifier = true := by
    rw [hdid]
    exact (hasThirdParty_iff _ _).mpr hid
  simp only [List.filter, hkeep, List.map]

theorem filter_length_lt {α : Type} (p : α → Bool) (l : List α) (a : α) (ha : a ∈ l)
    (hp : p a = false) : (l.filter p).length < l.length := by
  induction l with
  | nil => exact nomatch ha
  | cons x xs ih =>
    cases hx : p x
    · rw [List.filter_cons_of_neg (by rw [hx]; exact Bool.false_ne_true)]
      exact Nat.lt_succ_of_le (List.length_filter_le p xs)
    · rw [List.filter_cons_of_pos hx]
      rcases List.mem_cons.mp ha with heq | hmem
      · rw [heq, hx] at hp
        cases hp
      · exact Nat.succ_lt_succ (ih hmem)

/-- Every discharge answers a caveat and no two share an identifier, so there are at most
as many discharges as caveats. The explicit length test in `check_primary` is implied. -/
theorem discharges_le_caveats [DecidableEq B] (ds : List (Discharge B T)) (cs : List (Caveat B))
    (hmem : ∀ d ∈ ds, Caveat.thirdParty d.token.identifier ∈ cs)
    (huniq : ∀ d ∈ ds,
      (ds.filter fun x => decide (x.token.identifier = d.token.identifier)).length = 1) :
    ds.length ≤ cs.length := by
  induction ds generalizing cs with
  | nil => exact Nat.zero_le _
  | cons d ds ih =>
    have hne : ∀ d' ∈ ds, ¬ d'.token.identifier = d.token.identifier := by
      intro d' hd' heq
      have h := huniq d List.mem_cons_self
      rw [List.filter_cons_of_pos
        (p := fun x : Discharge B T => decide (x.token.identifier = d.token.identifier))
        (decide_eq_true rfl)] at h
      have hin : d' ∈ ds.filter fun x => decide (x.token.identifier = d.token.identifier) :=
        List.mem_filter.mpr ⟨hd', decide_eq_true heq⟩
      have hpos := List.length_pos_of_mem hin
      rw [List.length_cons] at h
      have h0 := Nat.succ.inj h
      rw [h0] at hpos
      exact Nat.lt_irrefl _ hpos
    let cs' := cs.filter fun c => !decide (c = Caveat.thirdParty d.token.identifier)
    have hlt : cs'.length < cs.length :=
      filter_length_lt _ cs _ (hmem d List.mem_cons_self) (by rw [decide_eq_true rfl]; rfl)
    have hle : ds.length ≤ cs'.length := by
      refine ih cs' (fun d' hd' => ?_) (fun d' hd' => ?_)
      · refine List.mem_filter.mpr ⟨hmem d' (List.mem_cons_of_mem _ hd'), ?_⟩
        have hc : ¬ Caveat.thirdParty d'.token.identifier = Caveat.thirdParty d.token.identifier :=
          fun h => hne d' hd' (Caveat.thirdParty.inj h)
        rw [decide_eq_false hc]
        rfl
      · have h := huniq d' (List.mem_cons_of_mem _ hd')
        rw [List.filter_cons_of_neg
          (p := fun x : Discharge B T => decide (x.token.identifier = d'.token.identifier))
          (by
            show ¬ decide (d.token.identifier = d'.token.identifier) = true
            rw [decide_eq_false (fun h => hne d' hd' h.symm)]
            exact Bool.false_ne_true)] at h
        exact h
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hle hlt)

/-- Transport of an accepted presentation to a token with fewer demands. -/
theorem primaryOk_transport [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok₁ tok₂ : Token B T) (r : Request B) (ds : List (Discharge B T))
    (h₁ : PrimaryOk S tok₁ r ds) (haud : tok₂.audience = tok₁.audience)
    (hflag : tok₂.discharge = false)
    (hsub : ∀ c ∈ tok₂.caveats, c ∈ tok₁.caveats ∨ c.holds r = true) :
    PrimaryOk S tok₂ r (shrink S tok₂ ds) := by
  have hc₁ := (checkToken_ok_iff _ _ _ _).mp h₁.2.1
  have hok : ∀ c ∈ tok₂.caveats,
      CaveatOk r none (tpLookup (dischargeCheck S r (S.bind tok₂.tag)) (shrink S tok₂ ds)) c := by
    intro c hc
    rcases hsub c hc with hin | hholds
    · rcases caveatOk_none_cases (hc₁.2.1 c hin) with hholds | ⟨id, heq, hlook⟩
      · exact caveatOk_of_holds hholds
      · rw [heq] at hc ⊢
        exact caveatOk_thirdParty (tpLookup_shrink S r tok₂ _ ds id hc hlook)
    · exact caveatOk_of_holds hholds
  have hused : ∀ d ∈ shrink S tok₂ ds, Caveat.thirdParty d.token.identifier ∈ tok₂.caveats := by
    intro d hd
    obtain ⟨d₀, hd₀, heq⟩ := List.mem_map.mp hd
    rw [← heq]
    exact (hasThirdParty_iff _ _).mp (List.mem_filter.mp hd₀).2
  refine ⟨?_, (checkToken_ok_iff _ _ _ _).mpr ⟨haud.trans hc₁.1, hok, fun h => ?_⟩, hused⟩
  · refine discharges_le_caveats _ _ hused fun d hd => ?_
    rcases caveatOk_none_cases (hok _ (hused d hd)) with hholds | ⟨id, heq, hlook⟩
    · exact nomatch hholds
    · cases heq
      unfold tpLookup at hlook
      obtain ⟨d', hf, _⟩ := (lookupResult_ok_iff _ _).mp hlook
      rw [hf]
      rfl
  · rw [hflag] at h
    cases h

/-- The requests a deployment grants a token: some presentation of discharges, each under the
registry's key for its identifier, is accepted by the deployment's verifier. -/
@[expose] def Authorized [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (tok : Token B T)
    (dep : Deployment B) (r : Request B) : Prop :=
  ∃ ds : List (Discharge B T), (∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) ∧
    verifierVerify S dep tok r ds = .ok ()

theorem authorized_genuine [DecidableEq B] [DecidableEq T] {S : MacSuite B T} {tok : Token B T}
    {dep : Deployment B} {r : Request B} (h : Authorized S tok dep r) : Genuine S dep tok := by
  obtain ⟨ds, _, hv⟩ := h
  exact ((verifierVerify_ok_iff _ _ _ _ _).mp hv).1

/-- Every caveat of an authorized token holds for the request or is a third-party demand. -/
theorem authorized_caveat [DecidableEq B] [DecidableEq T] {S : MacSuite B T} {tok : Token B T}
    {dep : Deployment B} {r : Request B} (h : Authorized S tok dep r) (c : Caveat B)
    (hc : c ∈ tok.caveats) : c.holds r = true ∨ c.isThirdParty = true := by
  obtain ⟨ds, _, hv⟩ := h
  have hp := ((verifierVerify_ok_iff _ _ _ _ _).mp hv).2
  rcases caveatOk_none_cases (((checkToken_ok_iff _ _ _ _).mp hp.2.1).2.1 c hc) with
    hholds | ⟨id, heq, _⟩
  · exact .inl hholds
  · rw [heq]
    exact .inr rfl

/-- **Semantic attenuation, general form.** A genuine token is authorized for every
deployment and request for which a token carrying all of its unmet caveats is. -/
theorem authorized_of_caveat_subset [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok₁ tok₂ : Token B T) (dep : Deployment B) (r : Request B)
    (hgen : Genuine S dep tok₂)
    (hsub : ∀ c ∈ tok₂.caveats, c ∈ tok₁.caveats ∨ c.holds r = true)
    (h : Authorized S tok₁ dep r) : Authorized S tok₂ dep r := by
  obtain ⟨ds, hreg, hv⟩ := h
  obtain ⟨hgen₁, hp⟩ := (verifierVerify_ok_iff _ _ _ _ _).mp hv
  refine ⟨shrink S tok₂ ds, fun d hd => ?_, (verifierVerify_ok_iff _ _ _ _ _).mpr
    ⟨hgen, primaryOk_transport S tok₁ tok₂ r ds hp (hgen.2.2.1.symm.trans hgen₁.2.2.1) hgen.1 hsub⟩⟩
  obtain ⟨d₀, hd₀, heq⟩ := List.mem_map.mp hd
  rw [← heq]
  exact hreg d₀ (List.mem_filter.mp hd₀).1

theorem attenuate_ok {S : MacSuite B T} {tok tok' : Token B T} {c : Caveat B}
    (h : attenuate S tok c = .ok tok') :
    tok' = { tok with caveats := tok.caveats ++ [c], tag := S.chain tok.tag c } := by
  unfold attenuate at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

theorem genuine_attenuate {S : MacSuite B T} {dep : Deployment B} {tok tok' : Token B T}
    {c : Caveat B} (h : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok) :
    Genuine S dep tok' := by
  rw [attenuate_ok h]
  refine ⟨hgen.1, hgen.2.1, hgen.2.2.1, ?_⟩
  show chainFrom S _ (tok.caveats ++ [c]) = S.chain tok.tag c
  unfold chainFrom
  rw [List.foldl_append]
  exact congrArg (fun t => S.chain t c) hgen.2.2.2

/-- **Semantic attenuation monotonicity.** Appending a caveat to a genuine token preserves or
narrows the set of (deployment, request) pairs it is authorized for. -/
theorem attenuation_narrows [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok tok' : Token B T) (c : Caveat B) (dep : Deployment B) (r : Request B)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (h : Authorized S tok' dep r) : Authorized S tok dep r := by
  refine authorized_of_caveat_subset S tok' tok dep r hgen (fun c' hc' => .inl ?_) h
  rw [attenuate_ok hatt]
  exact List.mem_append_left _ hc'

/-- A first-party caveat narrows by exactly its own request test. -/
theorem attenuation_firstParty_exact [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok tok' : Token B T) (c : Caveat B) (dep : Deployment B) (r : Request B)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (hfp : c.isThirdParty = false) :
    Authorized S tok' dep r ↔ Authorized S tok dep r ∧ c.holds r = true := by
  constructor
  · intro h
    refine ⟨attenuation_narrows S tok tok' c dep r hatt hgen h, ?_⟩
    have hc : c ∈ tok'.caveats := by
      rw [attenuate_ok hatt]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    rcases authorized_caveat h c hc with hholds | htp
    · exact hholds
    · rw [hfp] at htp
      cases htp
  · intro ⟨h, hholds⟩
    refine authorized_of_caveat_subset S tok tok' dep r (genuine_attenuate hatt hgen)
      (fun c' hc' => ?_) h
    rw [attenuate_ok hatt] at hc'
    rcases List.mem_append.mp hc' with hin | hlast
    · exact .inl hin
    · rw [List.mem_singleton.mp hlast]
      exact .inr hholds

/-- Without the premise that the attenuated token is genuine, an authorized attenuation of it
exhibits two chain keys that one caveat maps to the same tag. -/
theorem attenuation_narrows_or_chain_collision [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok tok' : Token B T) (c : Caveat B) (dep : Deployment B) (r : Request B)
    (hatt : attenuate S tok c = .ok tok') (h : Authorized S tok' dep r) :
    Authorized S tok dep r ∨
      ∃ k : T, k ≠ tok.tag ∧ S.chain k c = S.chain tok.tag c := by
  have hgen' := authorized_genuine h
  rw [attenuate_ok hatt] at hgen'
  by_cases hk : chainFrom S (S.root dep.key false dep.identifier dep.audience) tok.caveats = tok.tag
  · exact .inl (attenuation_narrows S tok tok' c dep r hatt
      ⟨hgen'.1, hgen'.2.1, hgen'.2.2.1, hk⟩ h)
  · refine .inr ⟨_, hk, ?_⟩
    have hc := hgen'.2.2.2
    unfold chainFrom at hc
    rw [List.foldl_append] at hc
    exact hc

/-! ## 4. Editing a chain is a forgery -/

def commonLen {α : Type} [DecidableEq α] : List α → List α → Nat
  | x :: xs, y :: ys => if x = y then commonLen xs ys + 1 else 0
  | _, _ => 0

/-- How a forged message relates to the queried one once their common prefix is removed:
the queried message has a first block, and the forged one is empty (the link key itself is
presented) or starts with a different block. -/
def Fresh {α : Type} : List α → List α → Prop
  | [], _ => False
  | _ :: _, [] => True
  | x :: _, y :: _ => x ≠ y

theorem fresh_not_prefix {α : Type} {a b : List α} (h : Fresh a b) : ¬ a <+: b := by
  match a, b, h with
  | x :: xs, [], _ =>
    intro hp
    have := hp.length_le
    exact Nat.not_succ_le_zero _ this
  | x :: xs, y :: ys, hne =>
    intro hp
    exact hne (List.cons_prefix_cons.mp hp).1

theorem take_commonLen {α : Type} [DecidableEq α] (a b : List α) :
    a.take (commonLen a b) = b.take (commonLen a b) := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · simp only [commonLen, h, ite_true, List.take_succ_cons]
        rw [ih ys]
      · simp only [commonLen, h, ite_false, List.take_zero]

theorem fresh_drop_commonLen {α : Type} [DecidableEq α] (a b : List α) (h : ¬ a <+: b) :
    Fresh (a.drop (commonLen a b)) (b.drop (commonLen a b)) := by
  induction a generalizing b with
  | nil => exact absurd List.nil_prefix h
  | cons x xs ih =>
    cases b with
    | nil => exact True.intro
    | cons y ys =>
      by_cases hxy : x = y
      · simp only [commonLen, hxy, ite_true, List.drop_succ_cons]
        refine ih ys fun hp => h ?_
        rw [hxy]
        exact List.cons_prefix_cons.mpr ⟨rfl, hp⟩
      · simp only [commonLen, hxy, ite_false, List.drop_zero]
        exact hxy

/-- A forgery against the cascade `chainFrom` under an unnamed link key: the message the
holder was given a tag for, a message, and a tag claimed for it. -/
structure CascadeForgery (B T : Type) where
  splitAt : Nat
  queried : List (Caveat B)
  forged : List (Caveat B)
  tag : T

/-- The extractor. Its inputs are the caveat lists of the issued and the edited token and
the edited token's tag; it takes no key and no intermediate tag. -/
def editWitness [DecidableEq B] (honest edited : List (Caveat B)) (editedTag : T) :
    CascadeForgery B T :=
  ⟨commonLen honest edited, honest.drop (commonLen honest edited),
    edited.drop (commonLen honest edited), editedTag⟩

/-- The prefix-free forgery game of the cascade under `linkKey`, after the single query
`w.queried` answered by `honestTag`. Extending the queried message is not a forgery: that is
attenuation. -/
def CascadeForgery.Wins (S : MacSuite B T) (linkKey honestTag : T) (w : CascadeForgery B T) :
    Prop :=
  chainFrom S linkKey w.queried = honestTag ∧ chainFrom S linkKey w.forged = w.tag ∧
    Fresh w.queried w.forged

theorem chainFrom_take_drop (S : MacSuite B T) (ρ : T) (cs : List (Caveat B)) (n : Nat) :
    chainFrom S (chainFrom S ρ (cs.take n)) (cs.drop n) = chainFrom S ρ cs := by
  unfold chainFrom
  rw [← List.foldl_append, List.take_append_drop]

/-- **Editing resistance.** Two chains accepted under one root tag, the second not an
extension of the first, give a win in the cascade forgery game under the link key at their
point of divergence. The witness is computed from public data. -/
theorem edit_yields_cascade_forgery [DecidableEq B] (S : MacSuite B T) (ρ : T)
    (cs cs' : List (Caveat B)) (t t' : T) (hne : ¬ cs <+: cs') (h : chainFrom S ρ cs = t)
    (h' : chainFrom S ρ cs' = t') :
    (editWitness cs cs' t').Wins S (chainFrom S ρ (cs.take (commonLen cs cs'))) t := by
  refine ⟨?_, ?_, fresh_drop_commonLen cs cs' hne⟩
  · show chainFrom S _ (cs.drop _) = t
    rw [chainFrom_take_drop]
    exact h
  · show chainFrom S _ (cs'.drop _) = t'
    rw [take_commonLen, chainFrom_take_drop]
    exact h'

/-- The edits a holder might try on a caveat list. -/
inductive Edit {α : Type} (cs cs' : List α) : Prop where
  | removed (i : Nat) (hi : i < cs.length) (h : cs' = cs.eraseIdx i)
  | truncated (n : Nat) (hn : n < cs.length) (h : cs' = cs.take n)
  | reordered (hp : cs'.Perm cs) (hne : cs' ≠ cs)
  | modified (i : Nat) (hi : i < cs.length) (c : α) (hc : c ≠ cs[i]) (h : cs' = cs.set i c)

theorem not_prefix_of_length_le_of_ne {α : Type} {cs cs' : List α}
    (hlen : cs'.length ≤ cs.length) (hne : cs' ≠ cs) : ¬ cs <+: cs' := by
  intro ⟨s, hs⟩
  cases s with
  | nil =>
    rw [List.append_nil] at hs
    exact hne hs.symm
  | cons x xs =>
    rw [← hs, List.length_append, List.length_cons] at hlen
    exact Nat.not_succ_le_self _ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ _)) hlen)

theorem Edit.not_prefix {α : Type} {cs cs' : List α} (e : Edit cs cs') : ¬ cs <+: cs' := by
  cases e with
  | removed i hi h =>
    intro hp
    have hl := hp.length_le
    rw [h, List.length_eraseIdx_of_lt hi] at hl
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hl
      (Nat.sub_one_lt (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hi))))
  | truncated n hn h =>
    intro hp
    have hl := hp.length_le
    rw [h, List.length_take] at hl
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.min_le_left _ _)) hn)
  | reordered hp hne => exact not_prefix_of_length_le_of_ne (Nat.le_of_eq hp.length_eq) hne
  | modified i hi c hc h =>
    refine not_prefix_of_length_le_of_ne (by rw [h, List.length_set]; exact Nat.le_refl _) ?_
    intro heq
    have hget : (cs.set i c)[i]? = cs[i]? := by rw [← h, heq]
    rw [List.getElem?_set_self hi, List.getElem?_eq_getElem hi] at hget
    exact hc (Option.some.inj hget)

/-- Removing, truncating, reordering or modifying caveats of an authentic chain, and
presenting any tag the verifier accepts for the result, wins the cascade forgery game. -/
theorem edited_chain_is_cascade_forgery [DecidableEq B] (S : MacSuite B T) (ρ : T)
    (cs cs' : List (Caveat B)) (t t' : T) (e : Edit cs cs') (h : chainFrom S ρ cs = t)
    (h' : chainFrom S ρ cs' = t') :
    (editWitness cs cs' t').Wins S (chainFrom S ρ (cs.take (commonLen cs cs'))) t :=
  edit_yields_cascade_forgery S ρ cs cs' t t' e.not_prefix h h'

/-- `m` is `q` with caveats appended: same header, caveat list extended. -/
def IsAttenuationOf (m q : Token B T) : Prop :=
  m.discharge = q.discharge ∧ m.identifier = q.identifier ∧ m.audience = q.audience ∧
    q.caveats <+: m.caveats

/-- The token-level game under the issuer's key: an authentic token that attenuates none of
the issued ones. -/
def TokenForgery (S : MacSuite B T) (key : B) (issued : List (Token B T)) (forged : Token B T) :
    Prop :=
  Authentic S key forged ∧ ∀ q ∈ issued, ¬ IsAttenuationOf forged q

theorem accepted_non_attenuation_is_token_forgery [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (key : B) (issued : List (Token B T)) (m : Token B T) (r : Request B)
    (ds : List (Discharge B T)) (hacc : verify S key m r ds = .ok ())
    (hnew : ∀ q ∈ issued, ¬ IsAttenuationOf m q) : TokenForgery S key issued m :=
  ⟨((verify_ok_iff _ _ _ _ _).mp hacc).2.1, hnew⟩

/-- An accepted token that shares the header of an issued one without attenuating it yields
the cascade forgery under the link key where their caveats part. -/
theorem accepted_edit_yields_cascade_forgery [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (key : B) (q m : Token B T) (r : Request B) (ds : List (Discharge B T))
    (hq : Authentic S key q) (hacc : verify S key m r ds = .ok ())
    (hd : m.discharge = q.discharge) (hi : m.identifier = q.identifier)
    (ha : m.audience = q.audience) (hnew : ¬ IsAttenuationOf m q) :
    (editWitness q.caveats m.caveats m.tag).Wins S
      (chainFrom S (rootTag S key q) (q.caveats.take (commonLen q.caveats m.caveats))) q.tag := by
  refine edit_yields_cascade_forgery S _ _ _ _ _ (fun hp => hnew ⟨hd, hi, ha, hp⟩) hq ?_
  have hm := ((verify_ok_iff _ _ _ _ _).mp hacc).2.1
  unfold Authentic rootTag at hm
  rw [hd, hi, ha] at hm
  exact hm

/-- A forgery against one call of `chain` under `k`, after the query `queried`. -/
def OneStepForgery (S : MacSuite B T) (k : T) (queried forgedMsg : Caveat B) (forgedTag : T) :
    Prop :=
  S.chain k forgedMsg = forgedTag ∧ forgedMsg ≠ queried

/-- A tag accepted for a strict prefix of the chain is the link key that authenticates the
next caveat, so it signs any other caveat in its place. -/
theorem truncation_exposes_link_key (S : MacSuite B T) (ρ : T) (pre : List (Caveat B))
    (x y : Caveat B) (t' : T) (h' : chainFrom S ρ pre = t') (hy : y ≠ x) :
    OneStepForgery S (chainFrom S ρ pre) x y (S.chain t' y) :=
  ⟨congrArg (fun t => S.chain t y) h', hy⟩

theorem last_caveat_swap_is_one_step_forgery (S : MacSuite B T) (ρ : T) (pre : List (Caveat B))
    (x y : Caveat B) (t' : T) (h' : chainFrom S ρ (pre ++ [y]) = t') (hy : y ≠ x) :
    OneStepForgery S (chainFrom S ρ pre) x y t' := by
  refine ⟨?_, hy⟩
  unfold chainFrom at h' ⊢
  rw [List.foldl_append] at h'
  exact h'

/-! ## 5. Discharges: binding and what the binding reads -/

/-- **Discharge binding.** For every third-party caveat of an accepted token, exactly one
presented discharge carries its identifier; it is a discharge for the request's audience,
authentic under the key supplied with it, and its binding caveats, of which there is at least
one, all equal the commitment to the presenting token's tag. -/
theorem accepted_discharge_bound [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B)
    (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) (id : B)
    (hacc : verify S key tok r ds = .ok ()) (hid : Caveat.thirdParty id ∈ tok.caveats) :
    ∃ d, (ds.filter fun d => decide (d.token.identifier = id)) = [d] ∧
      d.token.discharge = true ∧ d.token.audience = r.audience ∧
      Authentic S d.rootKey d.token ∧
      Caveat.bindToParent (S.bind tok.tag) ∈ d.token.caveats ∧
      ∀ b, Caveat.bindToParent b ∈ d.token.caveats → b = S.bind tok.tag := by
  have hp := ((verify_ok_iff _ _ _ _ _).mp hacc).2.2
  rcases caveatOk_none_cases (((checkToken_ok_iff _ _ _ _).mp hp.2.1).2.1 _ hid) with
    hholds | ⟨id', heq, hlook⟩
  · exact nomatch hholds
  · cases heq
    unfold tpLookup at hlook
    obtain ⟨d, hf, hflag, hd⟩ := (lookupResult_ok_iff _ _).mp hlook
    obtain ⟨hauth, hcheck⟩ := (dischargeCheck_ok_iff _ _ _ _).mp hd
    obtain ⟨haud, hcav, hbound⟩ := (checkToken_ok_iff _ _ _ _).mp hcheck
    have hall : ∀ b, Caveat.bindToParent b ∈ d.token.caveats → b = S.bind tok.tag :=
      fun b hb => caveatOk_bind_iff.mp (hcav _ hb)
    refine ⟨d, hf, hflag, haud, hauth, ?_, hall⟩
    obtain ⟨c, hc, hb⟩ := List.any_eq_true.mp (hbound hflag)
    cases c with
    | bindToParent b =>
      rw [← hall b hc]
      exact hc
    | expiresAt _ | notBefore _ | resource _ | actions _ | maxAmount _ | thirdParty _ =>
      exact nomatch hb

/-- A presented discharge is the one selected for its own identifier. -/
theorem presented_discharge_selected [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B)
    (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) (d : Discharge B T)
    (hacc : verify S key tok r ds = .ok ()) (hd : d ∈ ds) :
    Caveat.bindToParent (S.bind tok.tag) ∈ d.token.caveats := by
  have hp := ((verify_ok_iff _ _ _ _ _).mp hacc).2.2
  obtain ⟨d', hf, _, _, _, hmem, _⟩ :=
    accepted_discharge_bound S key tok r ds d.token.identifier hacc (hp.2.2 d hd)
  have hin : d ∈ ds.filter fun x => decide (x.token.identifier = d.token.identifier) :=
    List.mem_filter.mpr ⟨hd, decide_eq_true rfl⟩
  rw [hf] at hin
  rw [List.mem_singleton.mp hin]
  exact hmem

/-- An unbound discharge is never part of an accepted presentation. -/
theorem unbound_discharge_rejected [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B)
    (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) (d : Discharge B T)
    (hd : d ∈ ds) (hun : ∀ b, Caveat.bindToParent b ∉ d.token.caveats) :
    ¬ (verify S key tok r ds = .ok ()) :=
  fun hacc => hun _ (presented_discharge_selected S key tok r ds d hacc hd)

/-- **No transplanting.** One discharge accepted in presentations of two tokens forces the
two tokens to have the same binding commitment. -/
theorem discharge_not_transplantable [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (key₁ key₂ : B) (tok₁ tok₂ : Token B T) (r₁ r₂ : Request B)
    (ds₁ ds₂ : List (Discharge B T)) (d : Discharge B T)
    (h₁ : verify S key₁ tok₁ r₁ ds₁ = .ok ()) (h₂ : verify S key₂ tok₂ r₂ ds₂ = .ok ())
    (hd₁ : d ∈ ds₁) (hd₂ : d ∈ ds₂) : S.bind tok₁.tag = S.bind tok₂.tag := by
  have hp₂ := ((verify_ok_iff _ _ _ _ _).mp h₂).2.2
  obtain ⟨d', hf, _, _, _, _, hall⟩ :=
    accepted_discharge_bound S key₂ tok₂ r₂ ds₂ d.token.identifier h₂ (hp₂.2.2 d hd₂)
  have hin : d ∈ ds₂.filter fun x => decide (x.token.identifier = d.token.identifier) :=
    List.mem_filter.mpr ⟨hd₂, decide_eq_true rfl⟩
  rw [hf] at hin
  rw [← List.mem_singleton.mp hin] at hall
  exact hall _ (presented_discharge_selected S key₁ tok₁ r₁ ds₁ d h₁ hd₁)

/-- The same, with the alternative spelled out: equal tags, or a collision of `bind` whose
two inputs are the presented tags. -/
theorem transplant_gives_equal_tags_or_bind_collision [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (key₁ key₂ : B) (tok₁ tok₂ : Token B T) (r₁ r₂ : Request B)
    (ds₁ ds₂ : List (Discharge B T)) (d : Discharge B T)
    (h₁ : verify S key₁ tok₁ r₁ ds₁ = .ok ()) (h₂ : verify S key₂ tok₂ r₂ ds₂ = .ok ())
    (hd₁ : d ∈ ds₁) (hd₂ : d ∈ ds₂) :
    tok₁.tag = tok₂.tag ∨ (tok₁.tag ≠ tok₂.tag ∧ S.bind tok₁.tag = S.bind tok₂.tag) := by
  by_cases ht : tok₁.tag = tok₂.tag
  · exact .inl ht
  · exact .inr ⟨ht, discharge_not_transplantable S key₁ key₂ tok₁ tok₂ r₁ r₂ ds₁ ds₂ d h₁ h₂ hd₁ hd₂⟩

/-- What binding appends: one caveat holding the commitment, chained onto the discharge. -/
theorem bindDischarge_ok [DecidableEq B] {S : MacSuite B T} {parent d d' : Token B T}
    (h : bindDischarge S parent d = .ok d') :
    d' = { d with caveats := d.caveats ++ [.bindToParent (S.bind parent.tag)],
                  tag := S.chain d.tag (.bindToParent (S.bind parent.tag)) } := by
  unfold bindDischarge bindDischargeWith at h
  split at h
  · cases h
  · exact attenuate_ok h

/-- **Parent-tag non-exposure, holder side.** The bound discharge is a function of the
parent's flag, audience and commitment: two parents that agree on these give the same
discharge, whatever their tags. -/
theorem bindDischarge_factors_through_binding [DecidableEq B] (S : MacSuite B T)
    (p p' d : Token B T) (hflag : p.discharge = p'.discharge) (haud : p.audience = p'.audience)
    (hb : S.bind p.tag = S.bind p'.tag) : bindDischarge S p d = bindDischarge S p' d := by
  unfold bindDischarge
  rw [hflag, haud, hb]

/-- **Parent-tag non-exposure, verifier side.** The authorization check of a presentation
reads the token's tag through the commitment only. -/
theorem checkPrimary_factors_through_binding [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok tok' : Token B T) (r : Request B) (ds : List (Discharge B T))
    (haud : tok.audience = tok'.audience) (hflag : tok.discharge = tok'.discharge)
    (hcav : tok.caveats = tok'.caveats) (hb : S.bind tok.tag = S.bind tok'.tag) :
    checkPrimary S tok r ds = checkPrimary S tok' r ds := by
  unfold checkPrimary checkPrimaryWith checkToken
  rw [haud, hflag, hcav, hb]

/-- Why the commitment is not the tag: with a suite whose `bind` is the identity, the caveat a
bound discharge carries is a tag under which any further attenuation of the parent
authenticates. Whoever reads the discharge holds the parent capability. -/
theorem raw_tag_binding_exposes_bearer [DecidableEq B] (S : MacSuite B B) (hraw : ∀ t, S.bind t = t)
    (key : B) (parent d d' : Token B B) (c : Caveat B)
    (hbind : bindDischarge S parent d = .ok d') (hauth : Authentic S key parent) :
    ∃ b, Caveat.bindToParent b ∈ d'.caveats ∧
      Authentic S key { parent with caveats := parent.caveats ++ [c], tag := S.chain b c } := by
  refine ⟨parent.tag, ?_, ?_⟩
  · rw [bindDischarge_ok hbind, hraw]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · show chainFrom S _ (parent.caveats ++ [c]) = S.chain parent.tag c
    unfold chainFrom
    rw [List.foldl_append]
    exact congrArg (fun t => S.chain t c) hauth

/-! ## 6. Mutated verifiers and a worked instance

The two mutants drop one check each. The instance uses a suite whose tags record their
inputs, so every chain check is decided by structural equality. -/

/-- `verify` without the chained-tag check. -/
def verifyNoTag [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (tok : Token B T)
    (r : Request B) (ds : List (Discharge B T)) : Except CapError Unit :=
  andThen (require (!tok.discharge) .denied) (checkPrimary S tok r ds)

/-- The discharge check without the parent binding: authentic and first-party clean. -/
def dischargeCheckUnbound [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (r : Request B)
    (d : Discharge B T) : Except CapError Unit :=
  andThen (authenticate S d.rootKey d.token)
    (checkToken { d.token with discharge := false } r none deny)

/-- `verify` accepting discharges that are not bound to the presenting token. -/
def verifyUnbound [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B) (tok : Token B T)
    (r : Request B) (ds : List (Discharge B T)) : Except CapError Unit :=
  andThen (require (!tok.discharge) .denied)
    (andThen (authenticate S key tok) (checkPrimaryWith (dischargeCheckUnbound S r) tok r ds))

structure DemoTag where
  key : Nat
  discharge : Bool
  identifier : Nat
  audience : Nat
  trail : List (Caveat Nat)
  deriving DecidableEq

def demoSuite : MacSuite Nat DemoTag where
  root k f i a := ⟨k, f, i, a, []⟩
  chain t c := { t with trail := t.trail ++ [c] }
  bind t := 1000 + 7 * t.identifier + t.trail.length

def demoRequest : Request Nat := ⟨2, 3, 1#64, 5#128, 10#64⟩

def demoDeployment : Deployment Nat := ⟨1, 4, 2, fun _ => 6⟩

/-- Issued under key 1 for identifier 4 and audience 2, restricted to resource 3. -/
def demoScoped : Token Nat DemoTag :=
  ⟨false, 4, 2, [.resource 3], ⟨1, false, 4, 2, [.resource 3]⟩⟩

def demoParent : Token Nat DemoTag :=
  ⟨false, 4, 2, [.resource 3, .thirdParty 5], ⟨1, false, 4, 2, [.resource 3, .thirdParty 5]⟩⟩

def demoUnbound : Token Nat DemoTag := issueDischarge demoSuite 6 5 2

def demoBound : Token Nat DemoTag :=
  ⟨true, 5, 2, [.bindToParent 1030], ⟨6, true, 5, 2, [.bindToParent 1030]⟩⟩

/-- `demoScoped` with an expiry the demonstration request has passed. -/
def demoExpired : Token Nat DemoTag :=
  ⟨false, 4, 2, [.resource 3, .expiresAt 5#64],
    ⟨1, false, 4, 2, [.resource 3, .expiresAt 5#64]⟩⟩

/-- `demoExpired` with the expiry removed from the caveat list and the tag kept. -/
def demoStripped : Token Nat DemoTag :=
  ⟨false, 4, 2, [.resource 3], ⟨1, false, 4, 2, [.resource 3, .expiresAt 5#64]⟩⟩

theorem demo_attenuate_thirdParty :
    attenuate demoSuite demoScoped (.thirdParty 5) = .ok demoParent := by rfl

theorem demo_attenuate_expiry :
    attenuate demoSuite demoScoped (.expiresAt 5#64) = .ok demoExpired := by rfl

theorem demo_bind : bindDischarge demoSuite demoParent demoUnbound = .ok demoBound := by rfl

theorem demo_scoped_genuine : Genuine demoSuite demoDeployment demoScoped :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem demo_parent_accepted :
    verify demoSuite 1 demoParent demoRequest [⟨demoBound, 6⟩] = .ok () := by decide

theorem demo_parent_authorized :
    Authorized demoSuite demoParent demoDeployment demoRequest :=
  ⟨[⟨demoBound, 6⟩], fun d hd => by rw [List.mem_singleton.mp hd]; rfl, by decide⟩

theorem demo_scoped_authorized :
    Authorized demoSuite demoScoped demoDeployment demoRequest :=
  ⟨[], fun d hd => (nomatch hd), by decide⟩

/-- Narrowing can be strict: the expiry removes the demonstration request. -/
theorem demo_expired_not_authorized :
    ¬ Authorized demoSuite demoExpired demoDeployment demoRequest := by
  intro h
  rcases authorized_caveat h (.expiresAt 5#64) (by decide) with hh | hh
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)

theorem demo_stripped_rejected :
    verify demoSuite 1 demoStripped demoRequest [] = .error .invalidTag := by decide

theorem demo_stripped_accepted_without_tag_check :
    verifyNoTag demoSuite demoStripped demoRequest [] = .ok () := by decide

theorem demo_unbound_rejected :
    verify demoSuite 1 demoParent demoRequest [⟨demoUnbound, 6⟩] = .error .unboundDischarge := by
  decide

theorem demo_unbound_accepted_without_binding_check :
    verifyUnbound demoSuite 1 demoParent demoRequest [⟨demoUnbound, 6⟩] = .ok () := by decide

/-- Another token of the same session with the same third-party caveat. -/
def demoSibling : Token Nat DemoTag :=
  ⟨false, 4, 2, [.thirdParty 5], ⟨1, false, 4, 2, [.thirdParty 5]⟩⟩

/-- The bound discharge of `demoParent` does not serve `demoSibling`: its commitment is to
another tag. -/
theorem demo_transplant_rejected :
    verify demoSuite 1 demoSibling demoRequest [⟨demoBound, 6⟩] = .error .denied := by decide

theorem demo_parent_has_thirdParty : Caveat.thirdParty 5 ∈ demoParent.caveats := by decide

def demoRootTag : DemoTag := ⟨1, false, 4, 2, []⟩

def demoExpiredCaveats : List (Caveat Nat) := [.resource 3, .expiresAt 5#64]

def demoScopedCaveats : List (Caveat Nat) := [.resource 3]

theorem demo_edit_not_prefix : ¬ demoExpiredCaveats <+: demoScopedCaveats := by
  intro h
  have hl := h.length_le
  exact absurd hl (by decide)

theorem demo_chain_expired :
    chainFrom demoSuite demoRootTag demoExpiredCaveats = demoExpired.tag := by rfl

theorem demo_chain_scoped :
    chainFrom demoSuite demoRootTag demoScopedCaveats = demoScoped.tag := by rfl

#verify_constructive authorized_of_caveat_subset attenuation_narrows attenuation_firstParty_exact
  attenuation_narrows_or_chain_collision edit_yields_cascade_forgery
  edited_chain_is_cascade_forgery accepted_non_attenuation_is_token_forgery
  accepted_edit_yields_cascade_forgery truncation_exposes_link_key
  last_caveat_swap_is_one_step_forgery accepted_discharge_bound unbound_discharge_rejected
  discharge_not_transplantable transplant_gives_equal_tags_or_bind_collision
  bindDischarge_factors_through_binding checkPrimary_factors_through_binding
  raw_tag_binding_exposes_bearer

end Qsag.MacaroonAttenuation
