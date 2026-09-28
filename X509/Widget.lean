import X509.Real
import Lean.Widget.UserWidget
import Lean.Widget.Commands

/-!
# The widget

Everything the widget shows is computed here, by Lean, from the definitions the theorems are about: the DER
trees `parse` returns, the fields `decodeCert` reads, and each check `validate` makes. The one exception is
the tamper sweep, which runs the compiled `x509 sweep` over all 1,000-odd one-byte changes of the leaf
(too many to evaluate in the editor) and is read from `docs/sweep.json`.

Open this file in Lean Studio (or VS Code), put the cursor on the `#widget` line at the end, and look at
the Infoview.
-/

namespace X509.Widget

open Lean

deriving instance Inhabited for Rsa.Key, PublicKey, Cert

mutual
/-- A DER node for the widget: tag, header length, content length, children. -/
def nodeJson : Node → Json
  | .prim t c => Json.mkObj [("t", toJson t), ("h", toJson (1 + (encodeLen c.length).length)), ("n", toJson c.length)]
  | .cons t cs =>
    let n := (encodeSeq cs).length
    Json.mkObj [("t", toJson t), ("h", toJson (1 + (encodeLen n).length)), ("n", toJson n),
      ("c", Json.arr (nodesJson cs).toArray)]
def nodesJson : List Node → List Json
  | [] => []
  | x :: xs => nodeJson x :: nodesJson xs
end

def str (bs : List Nat) : String := String.ofList (bs.map Char.ofNat)

def hexByte (b : Nat) : String :=
  let d := fun (n : Nat) => "0123456789abcdef".toList.getD n '0'
  String.ofList [d (b / 16), d (b % 16)]

def cn (n : X509.Name) : String :=
  match n.flatten.find? (fun (o, _, _) => o == Oid.commonName) with
  | some (_, _, v) => str v
  | none => "?"

def bits (k : PublicKey) : Nat :=
  match k with
  | .rsa k => Nat.log2 k.n + 1
  | .other _ => 0

def certJson (der : List Nat) (c : Cert) : Json :=
  Json.mkObj [("cn", toJson (cn c.subject)), ("issuerCn", toJson (cn c.issuer)), ("bits", toJson (bits c.key)),
    ("notBefore", toJson c.notBefore), ("notAfter", toJson c.notAfter), ("isCA", toJson c.isCA),
    ("pathLen", toJson c.pathLen), ("dns", toJson (c.dnsNames.map str)),
    ("der", toJson (String.join (der.map hexByte))),
    ("tree", match parse der with | some t => nodeJson t | none => Json.null)]

/-- The checks of one link, parent issuing child. `anchor` links report only what RFC 5280 asks of a trust
anchor: its name and its key. -/
def linkJson (parent child : Cert) (anchor : Bool) : Json :=
  let sig := match parent.key with
    | .rsa k => signedBy k child
    | .other _ => false
  Json.mkObj [("names", toJson (child.issuer == parent.subject)),
    ("ca", if anchor then Json.null else toJson parent.isCA),
    ("ku", if anchor then Json.null else toJson (kuAllows parent 5)),
    ("sig", toJson sig), ("bits", toJson (bits parent.key))]

def theorems : List (String × String) := [
  ("der_unique", "Two byte strings that parse to the same DER tree are the same bytes."),
  ("parse_encode", "The parser reads back every well-formed tree the encoder writes."),
  ("encodeUInt_decodeUInt", "An INTEGER has one encoding: no redundant leading zero, never negative."),
  ("verify_iff", "RSA accepts exactly when sᵉ mod n is the one correctly padded block."),
  ("tbs_slice", "The signed bytes are a slice of the input, byte for byte."),
  ("validate_iff", "The checker returns true exactly when the chain meets the specification Valid."),
  ("issuers_are_CAs", "In a valid chain every certificate after the leaf is a CA."),
  ("signatures_verify", "Each certificate is signed by the next one's key over its own tbs bytes."),
  ("path_length", "A CA with pathLen p has at most p intermediates below it."),
  ("wildcard_one_label", "A wildcard stands for exactly one non-empty label with no dot."),
  ("names_no_nul", "A matched host has no NUL byte in it."),
  ("star_dot_com", "The pattern *.com names no host at all."),
  ("keithadler_github_io", "This chain is valid for keithadler.github.io today, checked by the kernel."),
  ("not_two_labels_deep", "…and not for x.keithadler.github.io."),
  ("expires", "…and not after 2026-10-31 23:38:01 UTC.")]

/-- The tamper sweep from the compiled tool (`x509 sweep`); see the module comment. -/
def sweep : Json :=
  match Json.parse (include_str ".." / "docs" / "sweep.json") with
  | .ok j => j
  | .error _ => Json.arr #[]

def widgetProps : Json := Id.run do
  let ders := [Data.leaf, Data.yr1, Data.rootYR, Data.isrgX1]
  let some certs := ders.mapM decodeCert | return Json.null
  let host := Real.host "keithadler.github.io"
  let leaf := certs.headD default
  let matched := (leaf.dnsNames.find? (Host.nameMatches · host)).map str
  let links := (List.range 3).map fun i =>
    linkJson (certs.getD (i + 1) default) (certs.getD i default) (i == 2)
  return Json.mkObj [
    ("host", toJson "keithadler.github.io"), ("now", toJson Real.now),
    ("valid", toJson (Real.chain.map (validate Real.anchors Real.now host) == some true)),
    ("matched", toJson matched),
    ("certs", Json.arr ((ders.zip certs).map fun (d, c) => certJson d c).toArray),
    ("links", Json.arr links.toArray),
    ("sweep", sweep),
    ("theorems", Json.arr (theorems.map fun (a, b) => Json.arr #[toJson a, toJson b]).toArray)]

@[widget_module]
def X509Widget : Widget.Module where
  javascript := include_str ".." / "widget" / "X509.js"

end X509.Widget

open X509.Widget in
#widget X509Widget with widgetProps
