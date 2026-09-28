import X509.Der
import X509.Prim
import X509.Rsa

/-!
# Certificates (RFC 5280 §4)

    Certificate  ::=  SEQUENCE  { tbsCertificate, signatureAlgorithm, signatureValue BIT STRING }

`decodeCert` reads the DER tree into the fields the rest of the project uses. It is strict where RFC 5280
and DER are strict: version 3 or an omitted version (v1), a serial of at most 20 bytes, the inner
and outer signature algorithms byte-identical, extensions only in v3, no extension twice, no critical
extension it does not understand, and DER's rule that a default value (a `critical` flag of FALSE, a `cA`
of FALSE) is left out rather than written.

The bytes a signature covers are the exact bytes of `tbsCertificate` as they appear in the input
(`tbs_slice`), which is what makes checking a signature over `c.tbs` mean something.
-/

namespace X509

/-- An object identifier, kept as its DER contents. The decoder checks each one with `oidOk`, and a
well-formed OID has one encoding, so equal OIDs have equal bytes. -/
abbrev Oid := List Nat

namespace Oid
def rsaEncryption : Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]
def sha256WithRSA : Oid := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b]
def basicConstraints : Oid := [0x55, 0x1d, 0x13]
def keyUsage : Oid := [0x55, 0x1d, 0x0f]
def subjectAltName : Oid := [0x55, 0x1d, 0x11]
def extKeyUsage : Oid := [0x55, 0x1d, 0x25]
def serverAuth : Oid := [0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01]
def anyExtendedKeyUsage : Oid := [0x55, 0x1d, 0x25, 0x00]
def commonName : Oid := [0x55, 0x04, 0x03]
def organization : Oid := [0x55, 0x04, 0x0a]
def country : Oid := [0x55, 0x04, 0x06]
end Oid

/-- The DER contents of an OBJECT IDENTIFIER, well formed: base-128 groups, each ending in a byte below
`0x80`, none starting with the padding byte `0x80`. Such an OID has exactly one encoding, which is why
comparing OIDs by their bytes is sound. -/
def oidOk (o : List Nat) : Bool :=
  o != [] && o.all (· < 256) && go true o
where
  go (start : Bool) : List Nat → Bool
    | [] => start
    | b :: bs => if start && b == 0x80 then false else go (b < 128) bs

/-- One attribute of a name: its type, the string type it was written in, and the string's bytes. -/
abbrev Attr := Oid × Nat × List Nat

/-- A distinguished name: a sequence of relative names, each a set of attributes. -/
abbrev Name := List (List Attr)

/-- The ASN.1 string types a name may use. -/
def stringTag (t : Nat) : Bool :=
  t == 0x0C || t == 0x13 || t == 0x16 || t == 0x14 || t == 0x1E || t == 0x1C

def decodeAttr : Node → Option Attr
  | .cons 0x30 [.prim 0x06 oid, .prim t v] => if stringTag t && oidOk oid then some (oid, t, v) else none
  | _ => none

def decodeRdn : Node → Option (List Attr)
  | .cons 0x31 (a :: as) => (a :: as).mapM decodeAttr
  | _ => none

def decodeName : Node → Option Name
  | .cons 0x30 rdns => rdns.mapM decodeRdn
  | _ => none

inductive PublicKey where
  | rsa (key : Rsa.Key)
  | other (alg : Oid)
  deriving Repr, DecidableEq

/-- SubjectPublicKeyInfo. An RSA key is itself DER inside the BIT STRING: `SEQUENCE { n, e }`. -/
def decodeKey : Node → Option PublicKey
  | .cons 0x30 [.cons 0x30 (.prim 0x06 alg :: params), .prim 0x03 (0 :: keyBytes)] =>
    if !oidOk alg then none
    else if alg = Oid.rsaEncryption then
      match params, parse keyBytes with
      | [.prim 0x05 []], some (.cons 0x30 [.prim 0x02 n, .prim 0x02 e]) =>
        match decodeUInt n, decodeUInt e with
        | some n, some e => some (.rsa ⟨n, e⟩)
        | _, _ => none
      | _, _ => none
    else some (.other alg)
  | _ => none

structure Ext where
  oid : Oid
  critical : Bool
  value : List Nat
  deriving Repr, DecidableEq

/-- An extension. `critical` is written only when TRUE: DER leaves out a value equal to its default. -/
def decodeExt : Node → Option Ext
  | .cons 0x30 [.prim 0x06 oid, .prim 0x04 v] => if oidOk oid then some ⟨oid, false, v⟩ else none
  | .cons 0x30 [.prim 0x06 oid, .prim 0x01 [0xFF], .prim 0x04 v] =>
    if oidOk oid then some ⟨oid, true, v⟩ else none
  | _ => none

/-- basicConstraints: `(cA, pathLenConstraint)`. A path length without `cA` means nothing and is refused. -/
def decodeBasic (v : List Nat) : Option (Bool × Option Nat) :=
  match parse v with
  | some (.cons 0x30 []) => some (false, none)
  | some (.cons 0x30 [.prim 0x01 [0xFF]]) => some (true, none)
  | some (.cons 0x30 [.prim 0x01 [0xFF], .prim 0x02 p]) => (decodeUInt p).map fun p => (true, some p)
  | _ => none

/-- keyUsage: the bytes of the bit string after its unused-bits count. -/
def decodeKeyUsage (v : List Nat) : Option (List Nat) :=
  match parse v with
  | some (.prim 0x03 (u :: bits)) => if u < 8 ∧ bits ≠ [] then some bits else none
  | _ => none

/-- subjectAltName: the dNSName entries (`[2] IA5String`). Other kinds of name are kept out of it. -/
def decodeSan (v : List Nat) : Option (List (List Nat)) :=
  match parse v with
  | some (.cons 0x30 (n :: ns)) =>
    some ((n :: ns).filterMap fun
      | .prim 0x82 d => some d
      | _ => none)
  | _ => none

/-- extKeyUsage: the list of purposes. -/
def decodeEku (v : List Nat) : Option (List Oid) :=
  match parse v with
  | some (.cons 0x30 (n :: ns)) =>
    (n :: ns).mapM fun
      | .prim 0x06 o => if oidOk o then some o else none
      | _ => none
  | _ => none

/-- DER contents of an INTEGER of either sign: not empty, bytes, and no redundant leading `0x00` or
`0xFF`. -/
def minimalInt : List Nat → Bool
  | [] => false
  | [b] => b < 256
  | b :: c :: rest => (b :: c :: rest).all (· < 256) && !(b == 0 && c < 128) && !(b == 255 && 128 ≤ c)

/-- No value twice. -/
def distinct {α} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- The extensions this project reads. Any other extension marked critical makes the certificate unusable
(RFC 5280 §4.2). -/
def understood (o : Oid) : Bool :=
  o == Oid.basicConstraints || o == Oid.keyUsage || o == Oid.subjectAltName || o == Oid.extKeyUsage

structure Cert where
  /-- The exact DER bytes of `tbsCertificate`: what the signature covers. -/
  tbs : List Nat
  /-- 0 for v1, 2 for v3. -/
  version : Nat
  /-- The serial number's DER contents. RFC 5280 wants it positive, but trust stores still carry roots
  with serial 0 or a negative serial, and §4.1.2.2 asks clients to handle them, so any minimal
  two's-complement integer of at most 20 bytes is accepted. -/
  serial : List Nat
  /-- The DER of the signature algorithm, inner and outer being byte-identical. -/
  sigAlg : List Nat
  issuer : Name
  notBefore : Nat
  notAfter : Nat
  subject : Name
  key : PublicKey
  exts : List Ext
  isCA : Bool
  pathLen : Option Nat
  keyUsage : Option (List Nat)
  eku : Option (List Oid)
  dnsNames : List (List Nat)
  /-- The signature as a number, and how many bytes it was written in. -/
  signature : Nat
  sigBytes : Nat
  deriving Repr

/-- Looks up an extension's value and reads it with `f`: absent is `some none`, unreadable is `none`. -/
def extField {α} (exts : List Ext) (oid : Oid) (f : List Nat → Option α) : Option (Option α) :=
  match exts.find? (·.oid == oid) with
  | none => some none
  | some e => (f e.value).map some

def decodeValidity : Node → Option (Nat × Nat)
  | .cons 0x30 [.prim t₁ c₁, .prim t₂ c₂] =>
    match decodeTime t₁ c₁, decodeTime t₂ c₂ with
    | some a, some b => some (a, b)
    | _, _ => none
  | _ => none

/-- Everything after the version: the fields common to v1 and v3. -/
def decodeTbsBody (tbs : Node) (version : Nat) (serial sigAlg issuer validity subject spki : Node)
    (extNodes : List Node) : Option (Cert × Node) := do
  let .prim 0x02 sn := serial | none
  if sn.length > 20 || !minimalInt sn then none
  let iss ← decodeName issuer
  let (nb, na) ← decodeValidity validity
  let sub ← decodeName subject
  let key ← decodeKey spki
  let exts ← extNodes.mapM decodeExt
  if !distinct (exts.map (·.oid)) then none
  if exts.any (fun e => e.critical && !understood e.oid) then none
  let bc ← extField exts Oid.basicConstraints decodeBasic
  let ku ← extField exts Oid.keyUsage decodeKeyUsage
  let san ← extField exts Oid.subjectAltName decodeSan
  let eku ← extField exts Oid.extKeyUsage decodeEku
  let (ca, pl) := bc.getD (false, none)
  some ({ tbs := [], version, serial := sn, sigAlg := encode sigAlg, issuer := iss,
          notBefore := nb, notAfter := na, subject := sub, key, exts, isCA := ca, pathLen := pl,
          keyUsage := ku, eku, dnsNames := san.getD [], signature := 0, sigBytes := 0 }, sigAlg)

def decodeTbs (tbs : Node) : Option (Cert × Node) :=
  match tbs with
  | .cons 0x30 [.cons 0xA0 [.prim 0x02 [2]], serial, alg, iss, val, sub, spki,
      .cons 0xA3 [.cons 0x30 (e :: es)]] =>
    decodeTbsBody tbs 2 serial alg iss val sub spki (e :: es)
  | .cons 0x30 [.cons 0xA0 [.prim 0x02 [2]], serial, alg, iss, val, sub, spki] =>
    decodeTbsBody tbs 2 serial alg iss val sub spki []
  | .cons 0x30 [serial, alg, iss, val, sub, spki] =>
    decodeTbsBody tbs 0 serial alg iss val sub spki []
  | _ => none

/-- Reads a certificate from its DER bytes. -/
def decodeCert (bs : List Nat) : Option Cert :=
  match parse bs with
  | some (.cons 0x30 [tbs, alg, .prim 0x03 (0 :: sig)]) =>
    match decodeTbs tbs with
    | some (c, innerAlg) =>
      if encode innerAlg = encode alg then
        some { c with tbs := encode tbs, signature := ofBE sig, sigBytes := sig.length }
      else none
    | none => none
  | _ => none

/-! ## What a decoded certificate guarantees -/

/-- The bytes a signature is checked over are a slice of the input, byte for byte: the certificate cannot
present one `tbsCertificate` and have another one checked. -/
theorem tbs_slice {bs : List Nat} {c : Cert} (h : decodeCert bs = some c) :
    ∃ pre suf, bs = pre ++ c.tbs ++ suf := by
  unfold decodeCert at h
  split at h
  · rename_i tbs alg sig hp
    split at h
    · rename_i c' innerAlg hd
      split at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨0x30 :: encodeLen (encodeSeq [tbs, alg, .prim 0x03 (0 :: sig)]).length,
          encode alg ++ encode (.prim 0x03 (0 :: sig)), ?_⟩
        rw [encode_parse hp]
        simp [encode, encodeSeq]
      · simp at h
    · simp at h
  · simp at h

end X509
