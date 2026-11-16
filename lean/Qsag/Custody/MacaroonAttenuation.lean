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
