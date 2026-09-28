// Apple Security framework (Safari, URLSession, all of macOS and iOS): SecTrust with the SSL policy,
// the corpus anchor as the only anchor, network fetching off, at the corpus time.
import Foundation
import Security

let dir = URL(fileURLWithPath: CommandLine.arguments[1])
let manifest = try! JSONSerialization.jsonObject(with: Data(contentsOf: dir.appendingPathComponent("manifest.json"))) as! [String: Any]
let now = Date(timeIntervalSince1970: TimeInterval(manifest["now"] as! Int))

func cert(_ name: String) -> SecCertificate? {
    guard let data = try? Data(contentsOf: dir.appendingPathComponent(name)) else { return nil }
    return SecCertificateCreateWithData(nil, data as CFData)
}

func emit(_ id: String, _ ok: Bool, _ err: String?) {
    var o: [String: Any] = ["id": id, "ok": ok]
    if let err { o["err"] = err }
    let j = try! JSONSerialization.data(withJSONObject: o, options: [.sortedKeys])
    print(String(data: j, encoding: .utf8)!)
}

for c in manifest["cases"] as! [[String: Any]] {
    let id = c["id"] as! String
    guard let leaf = cert(c["leaf"] as! String) else { emit(id, false, "SecCertificateCreateWithData refused the leaf"); continue }
    var chain = [leaf]
    var parsed = true
    for n in c["chain"] as! [String] {
        if let x = cert(n) { chain.append(x) } else { parsed = false }
    }
    guard parsed, let anchor = cert(c["anchor"] as! String) else { emit(id, false, "refused an intermediate or the anchor"); continue }
    var trust: SecTrust?
    let policy = SecPolicyCreateSSL(true, c["host"] as! CFString)
    guard SecTrustCreateWithCertificates(chain as CFArray, policy, &trust) == errSecSuccess, let trust else {
        emit(id, false, "SecTrustCreateWithCertificates failed"); continue
    }
    SecTrustSetAnchorCertificates(trust, [anchor] as CFArray)
    SecTrustSetAnchorCertificatesOnly(trust, true)
    SecTrustSetNetworkFetchAllowed(trust, false)
    SecTrustSetVerifyDate(trust, now as CFDate)
    var error: CFError?
    let ok = SecTrustEvaluateWithError(trust, &error)
    emit(id, ok, ok ? nil : (error.map { CFErrorCopyDescription($0) as String } ?? "rejected"))
}
