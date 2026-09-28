import X509
import Lean.Data.Json

/-!
`x509`: the same code the proofs are about, compiled, for the differential tests in `test/`.

    x509 show FILE.der ...                 one JSON line per certificate, or {"file":…,"reject":…}
    x509 validate HOST NOW ANCHOR.der CHAIN.der ...
                                           prints true or false
-/

open X509 Lean

def readDer (path : String) : IO (List Nat) := do
  let bs ← IO.FS.readBinFile path
  pure (bs.toList.map (·.toNat))

def str (bs : List Nat) : String := String.ofList (bs.map Char.ofNat)

def hex (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  if s.length % 2 == 1 then "0" ++ s else s

def nameJson (n : X509.Name) : Json :=
  Json.arr (n.flatten.map fun (oid, _, v) => Json.arr #[toJson oid, toJson (str v)]).toArray

def certJson (file : String) (c : Cert) : Json :=
  let key := match c.key with
    | .rsa k => Json.mkObj [("rsaBits", toJson (Nat.log2 k.n + 1)), ("e", toJson k.e)]
    | .other alg => Json.mkObj [("alg", toJson alg)]
  let selfSigned := match c.key with
    | .rsa k => toJson (c.issuer == c.subject && signedBy k c)
    | .other _ => Json.null
  Json.mkObj [("file", toJson file), ("version", toJson c.version), ("serial", toJson (String.join (c.serial.map hex))),
    ("notBefore", toJson c.notBefore), ("notAfter", toJson c.notAfter),
    ("subject", nameJson c.subject), ("issuer", nameJson c.issuer), ("isCA", toJson c.isCA),
    ("pathLen", toJson c.pathLen), ("dns", toJson (c.dnsNames.map str)), ("key", key),
    ("extensions", toJson c.exts.length), ("selfSignatureVerifies", selfSigned)]

def reason (bs : List Nat) : String :=
  match parse bs with
  | none => "not DER"
  | some _ => "not a certificate this reader accepts"

def main (args : List String) : IO UInt32 := do
  match args with
  | "show" :: files =>
    for f in files do
      let bs ← readDer f
      match decodeCert bs with
      | some c => IO.println (certJson f c).compress
      | none => IO.println (Json.mkObj [("file", toJson f), ("reject", toJson (reason bs))]).compress
    pure 0
  | "validate" :: host :: now :: anchor :: chain =>
    let a ← readDer anchor
    let cs ← chain.mapM readDer
    let anchors := ((decodeCert a).bind Anchor.ofCert).toList
    let ok := match cs.mapM decodeCert with
      | some certs => validate anchors now.toNat! (Sha256.ascii host) certs
      | none => false
    IO.println ok
    pure 0
  | _ =>
    IO.eprintln "usage: x509 show FILE.der ... | x509 validate HOST NOW ANCHOR.der CHAIN.der ..."
    pure 2
